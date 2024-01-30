# higher

Generate [higher-kinded data] (HKD) types from regular data types with Template
Haskell.

[higher-kinded data]: https://reasonablypolymorphic.com/blog/higher-kinded-data/

Turns this:

```haskell
import Higher

data Person = Person
  { name :: Text
  , age :: Word8
  }

$(higher ''Person)
```

Into this:

```haskell
import Higher

data Person = Person
  { name :: Text
  , age :: Word8
  }

data PersonB f = PersonB
  { nameB :: f Text
  , ageB :: f Word8
  }

instance Higher Person where
  type HKD Person = PersonB

  toHKD :: Person -> HKD Person Identity
  toHKD (Person x0 x1) = PersonB (Identity x0) (Identity x1)

  fromHKD :: HKD Person Identity -> Person
  fromHKD (PersonB x0 x1) = Person (runIdentity x0) (runIdentity x1)
```

You can customize how the type constructor, data constructors, and fields are
named with `higherWith`.

Take a look at the test suite for examples.
