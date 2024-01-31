{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import GHC.TypeLits (KnownSymbol, Symbol)
import Higher

data Person = Person
  { name :: String
  , age :: Int
  }

do
  let personOptions :: Options
      personOptions =
        defaultOptions
          { typeConstructorNameModifier = ("Cool" <>)
          , dataConstructorNameModifier = ("Cool" <>)
          , fieldNameModifier = id
          }
  higherWith personOptions ''Person

person1 :: Person
person1 = Person{ name = "John", age = 42 }

type Named :: Type -> Type
data Named a where
  Named :: KnownSymbol s => Named a

personP1 :: CoolPerson Named
personP1 = CoolPerson{ name = Named @"name", age = Named @"age" }

personP2 :: HKD Person Identity
personP2 = CoolPerson{ name = Identity "John", age = Identity 42 }

personP3 :: HKD Person Identity
personP3 = toHKD person1

person2 :: Person
person2 = fromHKD personP3

data Point a = Point a a

higher ''Point

point1 :: Point Int
point1 = Point 0 0

pointB1 :: PointB Int (Either String)
pointB1 = PointB (Left "x") (Right 0)

pointB2 :: HKD (Point Int) (Either String)
pointB2 = PointB (Left "x") (Right 0)

pointB3 :: PointB Int Identity
pointB3 = toHKD point1

point2 :: Point Int
point2 = fromHKD pointB3

data Result e a
  = Err e
  | Ok a

higher ''Result

err :: Result String a
err = Err "uh oh"

ok :: Result e [a]
ok = Ok []

errB :: ResultB String a Identity
errB = ErrB (Identity "uh oh")

okB :: ResultB e a []
okB = OkB []

newtype Newtype1 = Newtype1 String

$(higher ''Newtype1)

newtype Newtype2 a = Newtype2 a

$(higher ''Newtype2)

newtype Newtype3 (a :: Symbol) (b :: Type -> Type) = Newtype3 Int

$(higher ''Newtype3)

newtype3B :: HKD (Newtype3 "foo" Maybe) Identity
newtype3B = Newtype3B 42

data TypePhantom a (b :: Type) = TypePhantom a

higher ''TypePhantom

-- TOOD: Fix `k` getting included in type parameters for `Higher` instance

-- data PolyKindedPhantom a b = PolyKindedPhantom a

-- higher ''PolyKindedPhantom

main :: IO ()
main = pure ()
