# higher

Generate [higher-kinded data] (HKD) types from regular data types with Template
Haskell.

[higher-kinded data]: https://reasonablypolymorphic.com/blog/higher-kinded-data/

Turns this:

```haskell
import Higher

data Person = Person
  { name :: Text
  , age :: Word
  }

$(makeHKD ''Person)
```

Into this:

```haskell
import Higher

data Person = Person
  { name :: Text
  , age :: Word
  }

data PersonB f = PersonB
  { nameB :: f Text
  , ageB :: f Word
  }
```

You can customize how the type constructor, data constructors, and fields are
named with `makeHKDWith`.

Take a look at the test suite for examples.
