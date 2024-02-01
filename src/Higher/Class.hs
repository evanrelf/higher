{-# LANGUAGE FunctionalDependencies #-}

module Higher.Class
  ( Higher (..)
  )
where

import Data.Functor.Identity (Identity (..))

class Higher lo hi | lo -> hi, hi -> lo where
  toHKD :: lo -> hi Identity
  fromHKD :: hi Identity -> lo
