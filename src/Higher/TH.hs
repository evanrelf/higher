{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

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
higherWith options lowerTypeName = do
  lowerDatatypeInfo :: DatatypeInfo <- reifyDatatype lowerTypeName

  let lowerDatatypeVariant :: DatatypeVariant
      lowerDatatypeVariant = datatypeVariant lowerDatatypeInfo

  when (lowerDatatypeVariant `notElem` [Datatype, Newtype]) do
    let message :: String
        message = unwords
          [ "Unsupported datatype variant: " <> show lowerDatatypeVariant <> "."
          , "Currently only types declared with `data` or `newtype` are"
          , "supported."
          ]
    liftIO $ throwIO $ Error message

  let context :: Q Cxt
      context = pure (datatypeContext lowerDatatypeInfo)

  higherTypeName :: Name <- do
    let original :: String
        original = nameBase lowerTypeName
    newName ((typeConstructorNameModifier options) original)

  higherTypeParameterName :: Name <- newName (typeParameterName options)

  let higherTypeParameters :: [TyVarBndrVis]
      higherTypeParameters =
        datatypeVars lowerDatatypeInfo <> [PlainTV higherTypeParameterName ()]

  let higherDataConstructors :: [Q Con]
      higherDataConstructors =
        datatypeCons lowerDatatypeInfo <&> \lowerConstructorInfo -> do
          name :: Name <- do
            let original :: String
                original = nameBase (constructorName lowerConstructorInfo)
            newName ((dataConstructorNameModifier options) original)
          let bangTypes :: [(Bang, Type)]
              bangTypes = do
                (lowerType, strictness) :: (Type, FieldStrictness) <-
                  zip
                    (constructorFields lowerConstructorInfo)
                    (constructorStrictness lowerConstructorInfo)
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
                let type_ :: Type
                    type_ = AppT (VarT higherTypeParameterName) lowerType
                pure (bang, type_)
          case constructorVariant lowerConstructorInfo of
            NormalConstructor ->
              pure $ NormalC name bangTypes
            InfixConstructor -> do
              let left :: (Bang, Type)
                  left = bangTypes !! 0
              let right :: (Bang, Type)
                  right = bangTypes !! 1
              pure $ InfixC left name right
            RecordConstructor originalFieldNames -> do
              fieldNames <-
                for originalFieldNames \originalFieldName -> do
                  let original :: String
                      original = nameBase originalFieldName
                  newName ((fieldNameModifier options) original)
              let varBangTypes :: [(Name, Bang, Type)]
                  varBangTypes = do
                    (fieldName, (bang, type_)) <- zip fieldNames bangTypes
                    pure (fieldName, bang, type_)
              pure $ RecC name varBangTypes

  higherDataType :: Dec <-
    dataDCompat
      context
      higherTypeName
      higherTypeParameters
      higherDataConstructors
      []

  let classType :: Type
      classType = ConT ''Higher

  let familyType :: Type
      familyType = ConT ''HKD

  let applyTypeParameters :: Type -> Type
      applyTypeParameters nil = foldl' cons nil (datatypeVars lowerDatatypeInfo)
        where
        cons :: Type -> TyVarBndrUnit -> Type
        cons type_ = \case
          PlainTV param _flag -> AppT type_ (VarT param)
          KindedTV param _flag kind -> AppT type_ (SigT (VarT param) kind)

  let lowerType :: Type
      lowerType = applyTypeParameters (ConT lowerTypeName)

  let higherType :: Type
      higherType = applyTypeParameters (ConT higherTypeName)

  let higherInstanceType :: Q Type
      higherInstanceType = pure $ AppT classType lowerType

  let higherInstanceDeclarations :: [Q Dec]
      higherInstanceDeclarations = do
        let typeFamilyInstance :: Q Dec
            typeFamilyInstance =
              pure $ TySynInstD (TySynEqn Nothing (AppT familyType lowerType) higherType)
        let toHKDFunction :: Q Dec
            toHKDFunction = do
              FunD (mkName "toHKD") <$> do
                for (datatypeCons lowerDatatypeInfo) \lowerConstructorInfo -> do
                  let original :: String
                      original = nameBase (constructorName lowerConstructorInfo)
                  let fName = mkName ((dataConstructorNameModifier options) original)
                  xNames <-
                    for (zip [0 ..] (constructorFields lowerConstructorInfo)) \(i, _) ->
                      newName ("x" <> show @Int i)
                  let body = foldl' cons nil xNames
                        where
                        nil = ConE fName
                        cons e n = AppE e (ParensE (AppE (ConE (mkName "Identity")) (VarE n)))
                  pure $ Clause [ConP (constructorName lowerConstructorInfo) [] (VarP <$> xNames)] (NormalB body) []
        let fromHKDFunction :: Q Dec
            fromHKDFunction = do
              FunD (mkName "fromHKD") <$> do
                for (datatypeCons lowerDatatypeInfo) \lowerConstructorInfo -> do
                  let original :: String
                      original = nameBase (constructorName lowerConstructorInfo)
                  let fName = mkName ((dataConstructorNameModifier options) original)
                  xNames <-
                    for (zip [0 ..] (constructorFields lowerConstructorInfo)) \(i, _) ->
                      newName ("x" <> show @Int i)
                  let body = foldl' cons nil xNames
                        where
                        nil = ConE (constructorName lowerConstructorInfo)
                        cons e n = AppE e (ParensE (AppE (VarE (mkName "runIdentity")) (VarE n)))
                  pure $ Clause [ConP fName [] (VarP <$> xNames)] (NormalB body) []
        [typeFamilyInstance, toHKDFunction, fromHKDFunction]

  higherInstance :: Dec <-
    instanceD
      context
      higherInstanceType
      higherInstanceDeclarations

  pure [higherDataType, higherInstance]
