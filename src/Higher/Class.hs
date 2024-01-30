{-# LANGUAGE TypeFamilies #-}

module Higher.Class
  ( Higher (..)
  )
where

import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)

class Higher a where
  type HKD a :: (Type -> Type) -> Type
  toHKD :: a -> HKD a Identity
  fromHKD :: HKD a Identity -> a
