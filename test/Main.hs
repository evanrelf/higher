{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import GHC.TypeLits (KnownSymbol)
import Higher

data Person = Person
  { name :: String
  , age :: Int
  }

do
  let personOptions :: Options
      personOptions =
        Options
          { typeConstructorNameModifier = ("Cool" <>)
          , typeParameterName = "m"
          , dataConstructorNameModifier = ("Cool" <>)
          , fieldNameModifier = id
          }
  higherWith personOptions ''Person

person :: Person
person = Person{ name = "John", age = 42 }

type Named :: Type -> Type
data Named a where
  Named :: KnownSymbol s => Named a

personP :: CoolPerson Named
personP = CoolPerson{ name = Named @"name", age = Named @"age" }

data Point a = Point a a

higher ''Point

point :: Point Int
point = Point 0 0

pointB :: PointB (Either String) Int
pointB = PointB (Left "x") (Right 0)

data Result e a
  = Err e
  | Ok a

higher ''Result

err :: Result String a
err = Err "uh oh"

ok :: Result e [a]
ok = Ok []

errB :: ResultB Identity String a
errB = ErrB (Identity "uh oh")

okB :: ResultB [] e a
okB = OkB []

newtype Newtype1 = Newtype1 String

$(higher ''Newtype1)

newtype Newtype2 a = Newtype2 a

$(higher ''Newtype2)

newtype Newtype3 a b c d e = Newtype3 c

$(higher ''Newtype3)

main :: IO ()
main = pure ()
