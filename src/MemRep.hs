{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module MemRep where

import Generics.SOP (All, All2, Code, Generic)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Finite.Internal (Finite)
import Data.Type.Equality

import Fcf

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types
data Vector xs where
  Nil :: Vector '[]
  Cons :: x -> Vector ys -> Vector (x ': ys)

instance (All Show xs) =>  Show (Vector xs) where
  show Nil = "[]"
  show (Cons a as) = show a ++ " : " ++ show as

-- concat for Vectors
-- could (should) be a Semigroup instance (<>)
rvconcat :: Vector x -> Vector y -> Vector (Eval (x ++ y))
rvconcat Nil         ys = ys
rvconcat (Cons x xs) ys = Cons x (rvconcat xs ys)

-----------------------------------------------------------------------
-- Typelevel sums with a empty value
data RNS :: [*] -> * where
  RZ :: x -> RNS (x ': xs)
  RS :: RNS xs -> RNS (x ': xs)
  Empty :: RNS xs

instance (All Show x) => Show (RNS x) where
  show (RZ x) = show x
  show (RS x) = show x
  show Empty = "Ø"

-- stolen from https://hackage.haskell.org/package/first-class-families-0.8.0.1
-- and adapted to keep the length of the longest list
--
-- | Combine elements of two lists pairwise.
--
-- === __Example__
--
-- >>> :kind! Eval (ZipWith' (+) '[1,2,3] '[1,1])
-- Eval (ZipWith' (+) '[1,2,3] '[1,1]) :: [Nat]
-- = '[2, 3, 3]
data ZipWith' :: (a -> b -> Exp c) -> [a] -> [b] -> Exp [c]
type instance Eval (ZipWith' _f '[] _bs) = _bs
type instance Eval (ZipWith' _f _as '[]) = _as
type instance Eval (ZipWith' f (a ': as) (b ': bs)) =
  Eval (f a b) ': Eval (ZipWith' f as bs)


data (<>) :: * -> * -> Exp *

type instance Eval ((<>) x y) = x </> y

-- Type level append of RNS's
-- We might want to use the correct operator here, but for now this works well enough
type family (a :: *) </> (b :: *) :: * where
  RNS a </> RNS b = RNS (Eval (a ++ b))

-- Value level implementation of ZipWith' (<>)
rnsConcat :: (All IsRNS l, All IsRNS r, All IsRNS (Eval (ZipWith' (<>) l r))) => Vector l -> Vector r -> Vector (Eval (ZipWith' (<>) l r))
rnsConcat (Cons (x :: a) xs) (Cons (y :: b) ys)
  | Proof (Refl :: a :~: RNS a') <- proof @ a
  , Proof (Refl :: b :~: RNS b') <- proof @ b
  , Proof Refl <- proofRNSConcat @ a' @ b' = Cons Empty (rnsConcat xs ys)
rnsConcat Nil ys = ys
rnsConcat xs Nil = xs

-- Proofs to convice the compiler that ChoiceTypes and FieldTypes contain RNS's
class IsRNS x where
  proof :: RNSProof x

data RNSProof x where
  Proof :: x :~: RNS y -> RNSProof x

instance IsRNS (RNS x) where
  proof = Proof Refl

proofRNSConcat :: RNSProof (RNS a </> RNS b)
proofRNSConcat = Proof Refl

-- takeLeft and takeRight version of rnsConcat
-- We should probably merge them in a polymorphic thing (or even drop rnsConcat,
-- since it is functionaly equivalent to applying zipLeft (or zipRight) on 2 empty values)
zipLeft :: (All IsRNS l, All IsRNS r, All IsRNS (Eval (ZipWith' (<>) l r))) => Vector l -> Vector r -> Vector (Eval (ZipWith' (<>) l r))
zipLeft (Cons (x :: a) xs) (Cons (y :: b) ys)
  | Proof (Refl :: a :~: RNS a') <- proof @ a
  , Proof (Refl :: b :~: RNS b') <- proof @ b
  , Proof Refl <- proofRNSConcat @ a' @ b' = Cons (takeLeft x y) (rnsConcat xs ys)
zipLeft Nil ys = ys
zipLeft xs Nil = xs

takeLeft :: RNS l -> RNS r -> RNS (Eval (l ++ r))
takeLeft Empty  _ = Empty
takeLeft (RZ x) _ = RZ x
takeLeft (RS x) ys = RS (takeLeft x ys)

zipRight :: (All IsRNS l, All IsRNS r, All IsRNS (Eval (ZipWith' (<>) l r))) => Vector l -> Vector r -> Vector (Eval (ZipWith' (<>) l r))
zipRight (Cons (x :: a) xs) (Cons (y :: b) ys)
  | Proof (Refl :: a :~: RNS a') <- proof @ a
  , Proof (Refl :: b :~: RNS b') <- proof @ b
  , Proof Refl <- proofRNSConcat @ a' @ b' = Cons (takeRight x y) (rnsConcat xs ys)
zipRight Nil ys = ys
zipRight xs Nil = xs

-- It has proven to be quite hard to write a working instance for takeRight
-- This is due to Empty in left, which makes it hard to know how many RS's have to be applied
-- We might need to do some typeOf trickery:
-- https://hackage.haskell.org/package/base-4.15.0.0/docs/Data-Typeable.html#v:typeOf
-- But that requires runtime evaluation of types, which is not ideal
-- Another idea might be to split RNS '[] and RNS (x':xs) into seperate instances
-- of some class (probably IsRNS, since we already pass this constraint to zipRight)
-- Anyhow, this is going to take a bit more work then zipLeft
takeRight :: RNS l -> RNS r -> RNS (Eval (l ++ r))
takeRight = undefined

-----------------------------------------------------------------------
-- MemRep, the king of this file
class (All IsRNS (ChoiceTypes x), All IsRNS (FieldTypes x)) => MemRep x where
  type ChoiceTypes x :: [*]
  choices :: x -> Vector (ChoiceTypes x)

  type FieldTypes x :: [*]
  fields :: x -> Vector (FieldTypes x)

  widths :: [Int]

  emptyChoices :: Vector (ChoiceTypes x)
  emptyFields :: Vector (FieldTypes x)

-----------------------------------------------------------------------
-- Instances of MemRep for machine types

-- Sadly, this definition does not work but gives the following error:
-- 'Conflicting family instance declarations'
-- as soon as any other instance of ChoiceTypes or FieldTypes is declared
-- This is related to this GHC issue: https://gitlab.haskell.org/ghc/ghc/-/issues/4259
-- and won't be fixed very soon probably

-- instance Base x => MemRep x where
--   type ChoiceTypes x = '[]
--   choices x = Nil

--   type FieldTypes x = '[RNS '[x]]
--   mtfields x = Cons (RZ x) Nil

-- Instead, we have to do with a seperate definition per base type, which leads
-- to a horrible amount of boilerplate.
-- This is fixable with some Template Haskell, but let's not go there now.
instance MemRep Int where
  type ChoiceTypes Int = '[]
  choices _ = Nil

  type FieldTypes Int = '[RNS '[Int]]
  fields x = Cons (RZ x) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

instance MemRep Float where
  type ChoiceTypes Float = '[]
  choices _ = Nil

  type FieldTypes Float = '[RNS '[Float]]
  fields x = Cons (RZ x) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

instance MemRep Int8 where
  type ChoiceTypes Int8 = '[]
  choices _ = Nil

  type FieldTypes Int8 = '[RNS '[Int8]]
  fields x = Cons (RZ x) Nil

  widths = [8]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

instance MemRep Int16 where
  type ChoiceTypes Int16 = '[]
  choices _ = Nil

  type FieldTypes Int16 = '[RNS '[Int16]]
  fields x = Cons (RZ x) Nil

  widths = [16]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

-----------------------------------------------------------------------
-- Instances of MemRep that should be generically derived in the future
-- This needs a typelevel ZipWith (++), which we might be able to reuse from Fcf
-- https://hackage.haskell.org/package/first-class-families-0.8.0.1

-- This thing won't typecheck
-- The problem lies in the fact that we have to conjure up something that typechecks with the type of
-- Left while we are in the Right branch, and vice versa

instance (All IsRNS (ChoiceTypes (Either l r)), All IsRNS (FieldTypes (Either l r)), MemRep l, MemRep r) => MemRep (Either l r) where
  type ChoiceTypes (Either l r) = Eval ('[RNS '[Finite 2]] ++ Eval (ZipWith' (<>) (ChoiceTypes l) (ChoiceTypes r)))
  choices (Left lv)  = Cons (RZ 0) (zipLeft (choices lv) (emptyChoices @ r))
  choices (Right rv) = Cons (RZ 1) (zipRight (emptyChoices @ l) (choices rv))

  type FieldTypes (Either l r) = Eval (ZipWith' (<>) (FieldTypes l) (FieldTypes r))
  fields (Left lv)  = zipLeft (fields lv) (emptyFields @ r)
  fields (Right rv) = zipRight (emptyFields @ l) (fields rv)

  widths = zipWith max (widths @ l) (widths @ r)

  -- This might help significantly in the definition of fields
  -- and we might want to have something comparable for choices
  -- To this point I have not been able to come up with a definition of <>
  -- that typechecks however.
  -- It should not be too difficult however, it's just a Vector with the right amount of Empty's of the right type
  emptyChoices = Cons Empty (rnsConcat (emptyChoices @ l) (emptyChoices @ r))
  emptyFields = rnsConcat (emptyFields @ l) (emptyFields @ r)

-- Instance for product types (tuples)
-- Recursively defined, because concatenation is a whole lot easier then zipWith (++)
instance (All IsRNS (ChoiceTypes (x,y)), All IsRNS (FieldTypes (x,y)), MemRep x, MemRep y) => MemRep (x, y) where
  type ChoiceTypes (x,y) = Eval (ChoiceTypes x ++ ChoiceTypes y)
  choices (x,y) = rvconcat (choices x) (choices y)

  type FieldTypes (x, y) = Eval (FieldTypes x ++ FieldTypes y)
  fields (x,y) = rvconcat (fields x) (fields y)

  widths = widths @ x ++ widths @ y

  emptyChoices = rvconcat (emptyChoices @ x) (emptyChoices @ y)
  emptyFields = rvconcat (emptyFields @ x) (emptyFields @ y)
