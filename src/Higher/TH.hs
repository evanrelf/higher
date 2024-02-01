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

import Control.Exception (Exception, throwIO)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Functor ((<&>))
import Data.List (foldl')
import Data.Traversable (for)
import Higher.Class (Higher (..))
import Language.Haskell.TH hiding (Strict, bang)
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Datatype.TyVarBndr (TyVarBndrVis)

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
    -- , functorBInstanceD options loDatatypeInfo
    -- , traversableBInstanceD options loDatatypeInfo
    -- , distributiveBInstanceD options loDatatypeInfo
    -- , applicativeBInstanceD options loDatatypeInfo
    -- , constraintsBInstanceD options loDatatypeInfo
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

  -- `(Eq a, Ord a)`
  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  -- "Foo"
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  -- "FooB"
  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  hiTypeParameterName :: Name <- newName (typeParameterName options)

  -- `a`, `b`, f`
  let hiTypeParameters :: [TyVarBndrVis]
      hiTypeParameters =
        datatypeVars loDatatypeInfo <> [PlainTV hiTypeParameterName ()]

  let hiDataConstructors :: [Q Con]
      hiDataConstructors =
        datatypeCons loDatatypeInfo <&> \loConstructorInfo -> do
          -- "Foo"
          let loConstructorName :: Name
              loConstructorName = constructorName loConstructorInfo

          -- "FooB"
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

          let vars = fmap (SpecifiedSpec <$) (constructorVars loConstructorInfo)

          let context = constructorContext loConstructorInfo

          if not (null vars) || not (null context)
            then pure $ ForallC vars context hiConstructor
            else pure hiConstructor

  -- `deriving (...)`
  let hiDerivedClasses :: [Name]
      hiDerivedClasses = []

  -- `data FooB a b f = FooB (f a) (f b)`
  dataDCompat
    context
    hiTypeName
    hiTypeParameters
    hiDataConstructors
    hiDerivedClasses

higherInstanceD :: Options -> DatatypeInfo -> Q Dec
higherInstanceD options loDatatypeInfo = do
  -- `Foo` -> `Foo a b`
  let applyTypeParameters :: Type -> Type
      applyTypeParameters nil = foldl' cons nil (datatypeVars loDatatypeInfo)
        where
        cons :: Type -> TyVarBndrUnit -> Type
        cons type_ = \case
          -- `a`
          PlainTV name () -> AppT type_ (VarT name)
          -- `a :: k`
          KindedTV name () kind -> AppT type_ (SigT (VarT name) kind)

  -- "Foo"
  let loTypeName :: Name
      loTypeName = datatypeName loDatatypeInfo

  -- "FooB"
  let hiTypeName :: Name
      hiTypeName = mkNameWith (typeConstructorNameModifier options) loTypeName

  -- `Foo a b`
  let loType :: Type
      loType = applyTypeParameters (ConT loTypeName)

  -- `FooB a b f`
  let hiType :: Type
      hiType = applyTypeParameters (ConT hiTypeName)

  -- `(Eq a, Ord a)`
  let context :: Q Cxt
      context = pure (datatypeContext loDatatypeInfo)

  -- `Higher Foo`
  let higherInstanceType :: Q Type
      higherInstanceType = pure $ AppT (ConT ''Higher) loType

  -- `type HKD (Foo a b) = FooB a b`
  let hkdInstance :: Q Dec
      hkdInstance = do
        let params = Nothing
        -- `HKD (Foo a b)`
        let left = AppT (ConT ''HKD) loType
        -- `FooB a b`
        let right = hiType
        pure $ TySynInstD (TySynEqn params left right)

  let higherMethod :: HigherMethod -> Q Dec
      higherMethod method = do
        -- "toHKD"
        let name =
              case method of
                ToHKD -> mkName "toHKD"
                FromHKD -> mkName "fromHKD"

        clauses <-
          for (datatypeCons loDatatypeInfo) \loConstructorInfo -> do
            -- "Foo"
            let loConstructorName :: Name
                loConstructorName = constructorName loConstructorInfo

            -- "FooB"
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

            fieldNames <-
              for (zip [0 ..] (constructorFields loConstructorInfo)) \(i, _) ->
                newName ("x" <> show @Int i)

            -- `toHKD (Foo x0 x1) = FooB (Identity x0) (Identity x1)`
            --        ^^^^^^^^^^^
            let patterns = [ConP leftConstructorName [] (fmap VarP fieldNames)]

            -- `toHKD (Foo x0 x1) = FooB (Identity x0) (Identity x1)`
            --                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            let body = NormalB (foldl' cons nil fieldNames)
                  where
                  nil :: Exp
                  nil = ConE rightConstructorName

                  cons :: Exp -> Name -> Exp
                  cons e n = AppE e (ParensE (AppE f (VarE n)))

                  f :: Exp
                  f =
                    case method of
                      ToHKD -> ConE (mkName "Identity")
                      FromHKD -> VarE (mkName "runIdentity")

            -- `toHKD (Foo x0 x1) = FooB (Identity x0) (Identity x1) where ...`
            --                                                       ^^^^^^^^^
            let declarations = []

            pure $ Clause patterns body declarations

        pure $ FunD name clauses

  -- ```
  -- instance Higher (Foo a b) where
  --   type HKD (Foo a b) = FooB a b
  --   toHKD (Foo x0 x1) = FooB (Identity x0) (Identity x1)
  --   fromHKD (FooB x0 x1) = Foo (runIdentity x0) (runIdentity x1)
  -- ```
  instanceD
    context
    higherInstanceType
    [ hkdInstance
    , higherMethod ToHKD
    , higherMethod FromHKD
    ]

data HigherMethod
  = ToHKD
  | FromHKD

functorBInstanceD :: Options -> DatatypeInfo -> Q Dec
functorBInstanceD options loDatatypeInfo = do
  undefined

traversableBInstanceD :: Options -> DatatypeInfo -> Q Dec
traversableBInstanceD options loDatatypeInfo = do
  undefined

distributiveBInstanceD :: Options -> DatatypeInfo -> Q Dec
distributiveBInstanceD options loDatatypeInfo = do
  undefined

applicativeBInstanceD :: Options -> DatatypeInfo -> Q Dec
applicativeBInstanceD options loDatatypeInfo = do
  undefined

constraintsBInstanceD :: Options -> DatatypeInfo -> Q Dec
constraintsBInstanceD options loDatatypeInfo = do
  undefined

mkNameWith :: (String -> String) -> Name -> Name
mkNameWith modify name = mkName (modify (nameBase name))
