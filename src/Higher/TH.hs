{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- TODO: Remove
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Higher.TH
  ( higher
  , higherWith
  , Options (..)
  , defaultOptions
  )
where

import Barbies.Constraints (Dict (..))
import Control.Exception (Exception, throwIO)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Functor ((<&>))
import Data.Functor.Barbie
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.List (foldl')
import Data.Set (Set)
import Data.Traversable (for)
import Higher.Class (Higher (..))
import Language.Haskell.TH hiding (Strict, bang)
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Datatype.TyVarBndr (TyVarBndrVis)

import qualified Data.Set as Set

data Error = Error String
  deriving stock (Show)
  deriving anyclass (Exception)

data Options = Options
  { typeConstructorNameModifier :: String -> String
    -- ^ How the higher-kinded variant's type constructor should be named.
  , typeParameterName :: String
    -- ^ What the higher-kinded variant's type parameter should be named.
  , dataConstructorNameModifier :: String -> String
    -- ^ How the higher-kinded variant's data constructors should be named.
  , fieldNameModifier :: String -> String
    -- ^ How the higher-kinded variant's fields should be named.
  }

defaultOptions :: Options
defaultOptions =
  Options
    { typeConstructorNameModifier = (<> "B")
    , typeParameterName = "f"
    , dataConstructorNameModifier = (<> "B")
    , fieldNameModifier = (<> "B")
    }

higher :: Name -> Q [Dec]
higher = higherWith defaultOptions

higherWith :: Options -> Name -> Q [Dec]
higherWith options loTypeName = do
  loDatatypeInfo :: DatatypeInfo <- reifyDatatype loTypeName

  sequence
    [ hiTypeD options loDatatypeInfo
    , higherInstanceD options loDatatypeInfo
    , functorBInstanceD options loDatatypeInfo
    , traversableBInstanceD options loDatatypeInfo
    -- , distributiveBInstanceD options loDatatypeInfo
    -- , applicativeBInstanceD options loDatatypeInfo
    , constraintsBInstanceD options loDatatypeInfo
    ]

hiTypeD :: Options -> DatatypeInfo -> Q Dec
hiTypeD options loDatatypeInfo = do
  let loDatatypeVariant :: DatatypeVariant
      loDatatypeVariant = datatypeVariant loDatatypeInfo

  when (loDatatypeVariant `notElem` [Datatype, Newtype]) do
    let datatypeVariantString :: String
        datatypeVariantString =
          case loDatatypeVariant of
            Datatype -> "data"
            Newtype -> "newtype"
            DataInstance -> "data instance"
            NewtypeInstance -> "newtype instance"
            TypeData -> "type data"

    let message :: String
        message = unwords
          [ "Unsupported data type: `" <> datatypeVariantString <> "`."
          , "Currently only types declared with `data` or `newtype` are"
          , "supported."
          ]
    liftIO $ throwIO $ Error message

  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  hiTypeParameterName :: Name <- newName (typeParameterName options)

  let hiTypeParameters :: [TyVarBndrVis]
      hiTypeParameters =
        datatypeVars loDatatypeInfo <> [PlainTV hiTypeParameterName ()]

  let hiDataConstructors :: [Q Con]
      hiDataConstructors =
        datatypeCons loDatatypeInfo <&> \loConstructorInfo -> do
          let loConstructorName :: Name
              loConstructorName = constructorName loConstructorInfo

          let hiConstructorName :: Name
              hiConstructorName =
                mkNameWith
                  (dataConstructorNameModifier options)
                  loConstructorName

          let bangTypes :: [(Bang, Type)]
              bangTypes = do
                (loFieldType, strictness) :: (Type, FieldStrictness) <-
                  zip
                    (constructorFields loConstructorInfo)
                    (constructorStrictness loConstructorInfo)

                let bang :: Bang
                    bang =
                      Bang
                        case fieldUnpackedness strictness of
                          UnspecifiedUnpackedness -> NoSourceUnpackedness
                          NoUnpack -> SourceNoUnpack
                          Unpack -> SourceUnpack
                        case fieldStrictness strictness of
                          UnspecifiedStrictness -> NoSourceStrictness
                          Lazy -> SourceLazy
                          Strict -> SourceStrict

                let hiFieldType :: Type
                    hiFieldType = AppT (VarT hiTypeParameterName) loFieldType

                pure (bang, hiFieldType)

          let hiConstructor =
                case constructorVariant loConstructorInfo of
                  NormalConstructor ->
                    NormalC hiConstructorName bangTypes

                  InfixConstructor -> do
                    let left :: (Bang, Type)
                        left = bangTypes !! 0

                    let right :: (Bang, Type)
                        right = bangTypes !! 1

                    InfixC left hiConstructorName right

                  RecordConstructor loFieldNames -> do
                    let hiFieldNames :: [Name]
                        hiFieldNames =
                            fmap
                              (mkName . fieldNameModifier options . nameBase)
                              loFieldNames

                    let fieldBangTypes :: [(Name, Bang, Type)]
                        fieldBangTypes = do
                          (hiFieldName, (bang, hiFieldType)) <-
                            zip hiFieldNames bangTypes
                          pure (hiFieldName, bang, hiFieldType)

                    RecC hiConstructorName fieldBangTypes

          let vars :: [TyVarBndr Specificity]
              vars = fmap (SpecifiedSpec <$) (constructorVars loConstructorInfo)

          let context :: Cxt
              context = constructorContext loConstructorInfo

          if not (null vars) || not (null context)
            then pure $ ForallC vars context hiConstructor
            else pure hiConstructor

  let hiDerivedClasses :: [Name]
      hiDerivedClasses = []

  dataDCompat
    context
    hiTypeName
    hiTypeParameters
    hiDataConstructors
    hiDerivedClasses

higherInstanceD :: Options -> DatatypeInfo -> Q Dec
higherInstanceD options loDatatypeInfo = do
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  let loType :: Type
      loType = applyTypeParameters loDatatypeInfo (ConT loTypeName)

  let hiType :: Type
      hiType = applyTypeParameters loDatatypeInfo (ConT hiTypeName)

  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  let higherInstanceType :: Q Type
      higherInstanceType = pure $ ConT ''Higher `AppT` loType `AppT` hiType

  let higherMethod :: HigherMethod -> Q Dec
      higherMethod method = do
        let name :: Name
            name =
              case method of
                ToHKD -> 'toHKD
                FromHKD -> 'fromHKD

        clauses :: [Clause] <-
          for (datatypeCons loDatatypeInfo) \loConstructorInfo -> do
            let loConstructorName :: Name
                loConstructorName = constructorName loConstructorInfo

            let hiConstructorName :: Name
                hiConstructorName =
                  mkNameWith
                    (dataConstructorNameModifier options)
                    loConstructorName

            let leftConstructorName, rightConstructorName :: Name
                (leftConstructorName, rightConstructorName) =
                  case method of
                    ToHKD -> (loConstructorName, hiConstructorName)
                    FromHKD -> (hiConstructorName, loConstructorName)

            fieldNames :: [Name] <-
              for (zip [0 ..] (constructorFields loConstructorInfo)) \(i, _) ->
                newName ("x" <> show @Int i)

            let patterns :: [Pat]
                patterns = [ConP leftConstructorName [] (fmap VarP fieldNames)]

            let body :: Body
                body = NormalB (foldl' cons nil fieldNames)
                  where
                  nil :: Exp
                  nil = ConE rightConstructorName

                  cons :: Exp -> Name -> Exp
                  cons e n = AppE e (ParensE (AppE f (VarE n)))

                  f :: Exp
                  f =
                    case method of
                      ToHKD -> ConE 'Identity
                      FromHKD -> VarE 'runIdentity

            let declarations :: [Dec]
                declarations = []

            pure $ Clause patterns body declarations

        pure $ FunD name clauses

  instanceD
    context
    higherInstanceType
    [ higherMethod ToHKD
    , higherMethod FromHKD
    ]

data HigherMethod
  = ToHKD
  | FromHKD

functorBInstanceD :: Options -> DatatypeInfo -> Q Dec
functorBInstanceD options loDatatypeInfo = do
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  let hiType :: Type
      hiType = applyTypeParameters loDatatypeInfo (ConT hiTypeName)

  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  let functorBInstanceType :: Q Type
      functorBInstanceType = pure $ AppT (ConT ''FunctorB) hiType

  let bmapMethod :: Q Dec
      bmapMethod = do
        clauses :: [Clause] <-
          for (datatypeCons loDatatypeInfo) \loConstructorInfo -> do
            let loConstructorName :: Name
                loConstructorName = constructorName loConstructorInfo

            let hiConstructorName :: Name
                hiConstructorName =
                  mkNameWith
                    (dataConstructorNameModifier options)
                    loConstructorName

            fName :: Name <- newName "f"

            fieldNames :: [Name] <-
              for (zip [0 ..] (constructorFields loConstructorInfo)) \(i, _) ->
                newName ("x" <> show @Int i)

            let patterns :: [Pat]
                patterns =
                  [ VarP fName
                  , ConP hiConstructorName [] (fmap VarP fieldNames)
                  ]

            let body :: Body
                body = NormalB (foldl' cons nil fieldNames)
                  where
                  nil :: Exp
                  nil = ConE hiConstructorName

                  cons :: Exp -> Name -> Exp
                  cons e n =
                    AppE e (ParensE (AppE (VarE fName) (VarE n)))

            let declarations :: [Dec]
                declarations = []

            pure $ Clause patterns body declarations

        pure $ FunD 'bmap clauses

  instanceD
    context
    functorBInstanceType
    [bmapMethod]

traversableBInstanceD :: Options -> DatatypeInfo -> Q Dec
traversableBInstanceD options loDatatypeInfo = do
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  let hiType :: Type
      hiType = applyTypeParameters loDatatypeInfo (ConT hiTypeName)

  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  let traversableBInstanceType :: Q Type
      traversableBInstanceType = pure $ AppT (ConT ''TraversableB) hiType

  let btraverseMethod :: Q Dec
      btraverseMethod = do
        clauses :: [Clause] <-
          for (datatypeCons loDatatypeInfo) \loConstructorInfo -> do
            let loConstructorName :: Name
                loConstructorName = constructorName loConstructorInfo

            let hiConstructorName :: Name
                hiConstructorName =
                  mkNameWith
                    (dataConstructorNameModifier options)
                    loConstructorName

            fName :: Name <- newName "f"

            fieldNames :: [Name] <-
              for (zip [0 ..] (constructorFields loConstructorInfo)) \(i, _) ->
                newName ("x" <> show @Int i)

            let patterns :: [Pat]
                patterns =
                  [ VarP fName
                  , ConP hiConstructorName [] (fmap VarP fieldNames)
                  ]

            let body :: Body
                body = NormalB (foldl' cons nil fieldNames)
                  where
                  nil :: Exp
                  nil = AppE (VarE 'pure) (ConE hiConstructorName)

                  cons :: Exp -> Name -> Exp
                  cons e n =
                    UInfixE
                      e
                      (VarE '(<*>))
                      (ParensE (AppE (VarE fName) (VarE n)))

            let declarations :: [Dec]
                declarations = []

            pure $ Clause patterns body declarations

        pure $ FunD 'btraverse clauses

  instanceD
    context
    traversableBInstanceType
    [btraverseMethod]

distributiveBInstanceD :: Options -> DatatypeInfo -> Q Dec
distributiveBInstanceD options loDatatypeInfo = do
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  let hiType :: Type
      hiType = applyTypeParameters loDatatypeInfo (ConT hiTypeName)

  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  let distributiveBInstanceType :: Q Type
      distributiveBInstanceType = pure $ AppT (ConT ''DistributiveB) hiType

  let bdistributeMethod :: Q Dec
      bdistributeMethod = do
        undefined

  instanceD
    context
    distributiveBInstanceType
    [bdistributeMethod]

applicativeBInstanceD :: Options -> DatatypeInfo -> Q Dec
applicativeBInstanceD options loDatatypeInfo = do
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  let hiType :: Type
      hiType = applyTypeParameters loDatatypeInfo (ConT hiTypeName)

  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  let applicativeBInstanceType :: Q Type
      applicativeBInstanceType = pure $ AppT (ConT ''ApplicativeB) hiType

  let bpureMethod :: Q Dec
      bpureMethod = do
        undefined

  let bprodMethod :: Q Dec
      bprodMethod = do
        undefined

  instanceD
    context
    applicativeBInstanceType
    [ bpureMethod
    , bprodMethod
    ]

constraintsBInstanceD :: Options -> DatatypeInfo -> Q Dec
constraintsBInstanceD options loDatatypeInfo = do
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  let hiType :: Type
      hiType = applyTypeParameters loDatatypeInfo (ConT hiTypeName)

  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  let constraintsBInstanceType :: Q Type
      constraintsBInstanceType = pure $ AppT (ConT ''ConstraintsB) hiType

  let allBTypeFamilyInstance :: Q Dec
      allBTypeFamilyInstance = do
        cType :: Type <- VarT <$> newName "c"

        let params :: Maybe [TyVarBndrUnit]
            params = Nothing

        let left :: Type
            left = ConT ''AllB `AppT` cType `AppT` hiType

        -- TODO: Either support existentials, or degrade gracefully when they
        -- appear (e.g. don't generate a ``ConstraintsB` instance).
        let fieldTypes :: Set Type
            fieldTypes =
              Set.fromList $
                foldMap constructorFields (datatypeCons loDatatypeInfo)

        let right :: Type
            right = foldl' cons nil fieldTypes
              where
              nil :: Type
              nil = TupleT (Set.size fieldTypes)

              cons :: Type -> Type -> Type
              cons f x = AppT f (AppT cType x)

        pure $ TySynInstD (TySynEqn params left right)

  let baddDictsMethod :: Q Dec
      baddDictsMethod = do
        clauses :: [Clause] <- do
          for (datatypeCons loDatatypeInfo) \loConstructorInfo -> do
            let loConstructorName :: Name
                loConstructorName = constructorName loConstructorInfo

            let hiConstructorName :: Name
                hiConstructorName =
                  mkNameWith
                    (dataConstructorNameModifier options)
                    loConstructorName

            fieldNames :: [Name] <-
              for (zip [0 ..] (constructorFields loConstructorInfo)) \(i, _) ->
                newName ("x" <> show @Int i)

            let patterns :: [Pat]
                patterns = [ConP hiConstructorName [] (fmap VarP fieldNames)]

            let body :: Body
                body = NormalB (foldl' cons nil fieldNames)
                  where
                  nil :: Exp
                  nil = ConE hiConstructorName

                  cons :: Exp -> Name -> Exp
                  cons e n =
                    AppE e
                      (ParensE (ConE 'Pair `AppE` ConE 'Dict `AppE` VarE n))

            let declarations :: [Dec]
                declarations = []

            pure $ Clause patterns body declarations

        pure $ FunD 'baddDicts clauses

  instanceD
    context
    constraintsBInstanceType
    [ allBTypeFamilyInstance
    , baddDictsMethod
    ]

applyTypeParameters :: DatatypeInfo -> Type -> Type
applyTypeParameters loDatatypeInfo nil =
  foldl' cons nil (datatypeVars loDatatypeInfo)
  where
  cons :: Type -> TyVarBndrUnit -> Type
  cons type_ = \case
    PlainTV name () -> AppT type_ (VarT name)
    KindedTV name () kind -> AppT type_ (SigT (VarT name) kind)

mkNameWith :: (String -> String) -> Name -> Name
mkNameWith modify name = mkName (modify (nameBase name))
