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

module MemRep where

import Generics.SOP (All, All2, Code, Generic)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Finite.Internal (Finite)

import Fcf

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types
data Vector xs where
  Nil :: Vector '[]
  Cons :: x -> Vector ys -> Vector (x ': ys)

instance (All Show xs) =>  Show (Vector xs) where
  show Nil = "[]"
  show (Cons a as) = show a ++ ":" ++ show as

-- concat for Vectors
-- could (should) be a Semigroup instance (<>)
rvconcat :: Vector x -> Vector y -> Vector (Eval (x ++ y))
rvconcat Nil         ys = ys
rvconcat (Cons x xs) ys = Cons x (rvconcat xs ys)

-----------------------------------------------------------------------
-- Typelevel sums with a bottom value
data RNS :: [*] -> * where
  RZ :: x -> RNS (x ': xs)
  RS :: RNS xs -> RNS (x ': xs)
  Bottom :: RNS xs

instance (All Show x) => Show (RNS x) where
  show (RZ x) = show x
  show (RS x) = show x
  show Bottom = "_|_"

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

-----------------------------------------------------------------------
-- MemRep, the king of this file
class MemRep x where
  type ChoiceTypes x :: [*]
  choices :: x -> Vector (ChoiceTypes x)

  type FieldTypes x :: [*]
  fields :: x -> Vector (FieldTypes x)

  widths :: [Int]

  choicesBottom :: Vector (ChoiceTypes x)
  fieldsBottom :: Vector (FieldTypes x)

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

  choicesBottom = Nil
  fieldsBottom = Cons Bottom Nil

instance MemRep Float where
  type ChoiceTypes Float = '[]
  choices _ = Nil

  type FieldTypes Float = '[RNS '[Float]]
  fields x = Cons (RZ x) Nil

  widths = [32]

  choicesBottom = Nil
  fieldsBottom = Cons Bottom Nil

instance MemRep Int8 where
  type ChoiceTypes Int8 = '[]
  choices _ = Nil

  type FieldTypes Int8 = '[RNS '[Int8]]
  fields x = Cons (RZ x) Nil

  widths = [8]

  choicesBottom = Nil
  fieldsBottom = Cons Bottom Nil

instance MemRep Int16 where
  type ChoiceTypes Int16 = '[]
  choices _ = Nil

  type FieldTypes Int16 = '[RNS '[Int16]]
  fields x = Cons (RZ x) Nil

  widths = [16]

  choicesBottom = Nil
  fieldsBottom = Cons Bottom Nil

-----------------------------------------------------------------------
-- Instances of MemRep that should be generically derived in the future
-- This needs a typelevel ZipWith (++), which we might be able to reuse from Fcf
-- https://hackage.haskell.org/package/first-class-families-0.8.0.1

-- This thing won't typecheck
-- The problem lies in the fact that we have to conjure up something that typechecks with the type of
-- Left while we are in the Right branch, and vice versa

-- instance (MemRep l, MemRep r) => MemRep (Either l r) where
--   type ChoiceTypes (Either l r) = Eval ('[RNS '[Finite 2]] ++ Eval (ZipWith' (<>) (ChoiceTypes l) (ChoiceTypes r)))
--   choices (Left x)  = case choices x of
--     Cons x' Nil -> Cons (RZ 0) _
--   choices (Right x) = case choices x of
--     Cons x' xs -> Cons (RZ 1) _

--   type FieldTypes (Either l r) = Eval (ZipWith' (<>) (FieldTypes l) (FieldTypes r))
--   fields (Left x)  = case fields x of
--     Nil         -> _
--     Cons x' Nil -> _
--   fields (Right x) = case fields x of
--     Cons x' Nil -> _

--   -- This might help significantly in the definition of fields
--   -- and we might want to have something comparable for choices
--   -- To this point I have not been able to come up with a definition of <>
--   -- that typechecks however.
--   -- It should not be too difficult however, it's just a Vector with the right amount of Bottoms of the right type
--   choicesBottom = Cons Bottom (choicesBottom @ r <> choicesBottom @ l)
--   fieldsBottom = fieldsBottom @ r <> fieldsBottom @ l


instance (MemRep x) => MemRep (Maybe x) where
  type ChoiceTypes (Maybe x) = Eval ('[RNS '[Finite 2]] ++ ChoiceTypes x)
  choices Nothing  = Cons (RZ 0) (choicesBottom @ x)
  choices (Just x) = Cons (RZ 1) (choices x)

  type FieldTypes (Maybe x) = FieldTypes x
  fields Nothing  = fieldsBottom @ x
  fields (Just x) = fields x

  widths = zipWith max (widths @ Float) (widths @ Int)

  fieldsBottom = fieldsBottom @ x
  choicesBottom = Cons Bottom (choicesBottom @ x)

instance MemRep (Either Float Int) where
  type ChoiceTypes (Either Float Int) = '[RNS '[Finite 2]]
  choices (Left x)  = Cons (RZ 0) Nil
  choices (Right x) = Cons (RZ 1) Nil

  type FieldTypes (Either Float Int) = '[RNS '[Float, Int]]
  fields (Left x)  = Cons (RZ x) Nil
  fields (Right x) = Cons (RS $ RZ x) Nil

  widths = zipWith max (widths @ Float) (widths @ Int)

  choicesBottom = Cons Bottom Nil
  fieldsBottom = Cons Bottom Nil

instance MemRep (Either Int8 Int16) where
  type ChoiceTypes (Either Int8 Int16) = '[RNS '[Finite 2]]
  choices (Left x)  = Cons (RZ 0) Nil
  choices (Right x) = Cons (RZ 1) Nil

  type FieldTypes (Either Int8 Int16) = '[RNS '[Int8, Int16]]
  fields (Left x)  = Cons (RZ x) Nil
  fields (Right x) = Cons (RS $ RZ x) Nil

  widths = zipWith max (widths @ Int8) (widths @ Int16)

  fieldsBottom = Cons Bottom Nil
  choicesBottom = Cons Bottom Nil


instance MemRep (Either (Either Float Int) (Either Int8 Int16)) where
  type ChoiceTypes (Either (Either Float Int) (Either Int8 Int16)) = '[RNS '[Finite 2], RNS '[Finite 2, Finite 2]]
  choices (Left x)  = case choices x of
    Cons (RZ x') Nil -> Cons (RZ 0) (Cons (RZ x') Nil)
  choices (Right x) = case choices x of
    Cons x' Nil -> Cons (RZ 1) (Cons (RS x') Nil)

  type FieldTypes (Either (Either Float Int) (Either Int8 Int16)) = '[RNS [Float, Int, Int8, Int16]]
  fields (Left x)  = case fields x of
    Cons (RZ x') Nil      -> Cons (RZ x') Nil
    Cons (RS (RZ x')) Nil -> Cons (RS $ RZ x') Nil
  fields (Right x) = case fields x of
    Cons x' Nil      -> Cons (RS $ RS x') Nil

  widths = zipWith max (widths @ (Either Float Int)) (widths @ (Either Int8 Int16))

  fieldsBottom = Cons Bottom Nil
  choicesBottom = Cons Bottom (Cons Bottom Nil)

-- Instance for product types (tuples)
-- Recursively defined, because concatenation is a whole lot easier then zipWith (++)
instance (MemRep x, MemRep y) => MemRep (x, y) where
  type ChoiceTypes (x,y) = Eval (ChoiceTypes x ++ ChoiceTypes y)
  choices (x,y) = rvconcat (choices x) (choices y)

  type FieldTypes (x, y) = Eval (FieldTypes x ++ FieldTypes y)
  fields (x,y) = rvconcat (fields x) (fields y)

  widths = widths @ x ++ widths @ y

  choicesBottom = rvconcat (choicesBottom @ x) (choicesBottom @ y)
  fieldsBottom = rvconcat (fieldsBottom @ x) (fieldsBottom @ y)
