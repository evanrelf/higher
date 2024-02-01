# higher

[Higher-kinded data][hkd] (HKD) types with less pain.

[hkd]: https://reasonablypolymorphic.com/blog/higher-kinded-data/

This library takes your regular Haskell data types and produces additional
higher-kinded versions, along with term- and type-level conversion functions.

I wanted to leverage the power of higher-kinded data as an internal
implementation detail of my code, without burdening others with the extra type
parameter, `Identity` wrapping (or poor type inference from the type family
unwrapping `Identity`), and overall increase in complexity.

With this library, I can work with my data in a higher-kinded fashion
temporarily, and then convert back to regular Haskell data types when I'm done.

In other words, this:

```haskell
import Higher

data Person = Person
  { name :: Text
  , age :: Word8
  }

$(higher ''Person)
```

...turns into this:

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

instance Higher Person PersonB where
  toHKD :: Person -> PersonB Identity
  toHKD (Person x0 x1) = PersonB (Identity x0) (Identity x1)

  fromHKD :: PersonB Identity -> Person
  fromHKD (PersonB x0 x1) = Person (runIdentity x0) (runIdentity x1)

instance FunctorB PersonB where
  bmap :: (forall a. f a -> g a) -> PersonB f -> PersonB g
  bmap f (PersonB x0 x1) = PersonB (f x0) (f x1)

instance TraversableB PersonB where
  btraverse :: Applicative e => (forall a. f a -> e (g a)) -> PersonB f -> e (PersonB g)
  btraverse f (PersonB x0 x1) = pure PersonB <*> f x0 <*> f x1

instance ConstraintsB PersonB where
  type AllB c PersonB = (c Text, c Word8)

  baddDicts :: AllB c PersonB => PersonB f -> PersonB (Product (Dict c) f)
  baddDicts (PersonB x0 x1) = PersonB (Pair Dict x0) (Pair Dict x1)

-- Other `barbies` type class instances coming soon
```

You can customize how the type constructor, data constructors, and fields are
named with `higherWith`.

Take a look at the test suite for examples.

Check out [higgledy](https://github.com/i-am-tom/higgledy) if you prefer using
`Generic` over Template Haskell.
