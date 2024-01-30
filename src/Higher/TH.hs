{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Higher.TH
  ( makeHKD
  , makeHKDWith
  , Options (..)
  , defaultOptions
  )
where

import Control.Exception (Exception, throwIO)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Functor ((<&>))
import Data.Traversable (for)
import Language.Haskell.TH hiding (Strict, bang)
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Datatype.TyVarBndr (TyVarBndrVis)

data Error = Error String
  deriving stock (Show)
  deriving anyclass (Exception)

data Options = Options
  { typeConstructorNameModifier :: String -> String
    -- ^ How the higher-kinded variant's type constructor should be named.
  , dataConstructorNameModifier :: String -> String
    -- ^ How the higher-kinded variant's data constructors should be named.
  , fieldNameModifier :: String -> String
    -- ^ How the higher-kinded variant's fields should be named.
  , typeParameterName :: String
    -- ^ What the higher-kinded variant's type parameter should be named.
  }

defaultOptions :: Options
defaultOptions =
  Options
    { typeConstructorNameModifier = (<> "B")
    , dataConstructorNameModifier = (<> "B")
    , fieldNameModifier = (<> "B")
    , typeParameterName = "f"
    }

makeHKD :: Name -> Q [Dec]
makeHKD = makeHKDWith defaultOptions

makeHKDWith :: Options -> Name -> Q [Dec]
makeHKDWith options lowerTypeName = do
  lowerDatatypeInfo :: DatatypeInfo <- reifyDatatype lowerTypeName

  let lowerDatatypeVariant :: DatatypeVariant
      lowerDatatypeVariant = datatypeVariant lowerDatatypeInfo

  when (lowerDatatypeVariant /= Datatype) do
    let message :: String
        message = unwords
          [ "Unsupported datatype variant: " <> show lowerDatatypeVariant <> "."
          , "Currently only types declared with `data` are supported."
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
        PlainTV higherTypeParameterName () : datatypeVars lowerDatatypeInfo

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

  pure [higherDataType]
