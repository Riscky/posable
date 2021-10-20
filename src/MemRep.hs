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
-- could (should) be an applicative
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

-----------------------------------------------------------------------
-- Machine types with their staticly known width
class Base x where
  width :: Int

instance Base Int8 where
  width = 8

instance Base Int16 where
  width = 16

instance Base Int32 where
  width = 32

instance Base Int64 where
  width = 64

instance Base Int where
  width = 32

instance Base Float where
  width = 32

-----------------------------------------------------------------------
-- MemRep, the king of this file
class MemRep x where
  type ChoiceTypes x :: [*]
  choices :: x -> Vector (ChoiceTypes x)

  type FieldTypes x :: [*]
  fields :: x -> Vector (FieldTypes x)

-----------------------------------------------------------------------
-- Instances of MemRep for machine types

-- Sadly, this definition does not work but gives the following error:
-- 'Conflicting family instance declarations'
-- as soons as any other instance of ChoiceTypes or FieldTypes is declared
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

instance MemRep Float where
  type ChoiceTypes Float = '[]
  choices _ = Nil

  type FieldTypes Float = '[RNS '[Float]]
  fields x = Cons (RZ x) Nil

instance MemRep Int8 where
  type ChoiceTypes Int8 = '[]
  choices _ = Nil

  type FieldTypes Int8 = '[RNS '[Int8]]
  fields x = Cons (RZ x) Nil

instance MemRep Int16 where
  type ChoiceTypes Int16 = '[]
  choices _ = Nil

  type FieldTypes Int16 = '[RNS '[Int16]]
  fields x = Cons (RZ x) Nil

-----------------------------------------------------------------------
-- Instances of MemRep that should be generically derived in the future
-- This needs a typelevel ZipWith (++), which we might be able to reuse from Fcf
-- https://hackage.haskell.org/package/first-class-families-0.8.0.1

instance MemRep (Either Int Int) where
  type ChoiceTypes (Either Int Int) = '[RNS '[Finite 2]]
  choices (Left x)  = Cons (RZ 0) Nil
  choices (Right x) = Cons (RZ 1) Nil

  type FieldTypes (Either Int Int) = '[RNS '[Int, Int]]
  fields (Left x)  = Cons (RZ x) Nil
  fields (Right x) = Cons (RS $ RZ x) Nil


instance MemRep (Either Float Int) where
  type ChoiceTypes (Either Float Int) = '[RNS '[Finite 2]]
  choices (Left x)  = Cons (RZ 0) Nil
  choices (Right x) = Cons (RZ 1) Nil

  type FieldTypes (Either Float Int) = '[RNS '[Float, Int]]
  fields (Left x)  = Cons (RZ x) Nil
  fields (Right x) = Cons (RS $ RZ x) Nil


instance MemRep (Either Int8 Int16) where
  type ChoiceTypes (Either Int8 Int16) = '[RNS '[Finite 2]]
  choices (Left x)  = Cons (RZ 0) Nil
  choices (Right x) = Cons (RZ 1) Nil

  type FieldTypes (Either Int8 Int16) = '[RNS '[Int8, Int16]]
  fields (Left x)  = Cons (RZ x) Nil
  fields (Right x) = Cons (RS $ RZ x) Nil


instance MemRep (Either (Either Float Int) (Either Int8 Int16)) where
  type ChoiceTypes (Either (Either Float Int) (Either Int8 Int16)) = '[RNS '[Finite 2], RNS '[Finite 2, Finite 2]]
  choices (Left x)  = case choices x of
    Cons (RZ x') Nil -> Cons (RZ 0) (Cons (RZ x') Nil)
  choices (Right x) = case choices x of
    Cons (RZ x') Nil -> Cons (RZ 1) (Cons (RS $ RZ x') Nil)

  type FieldTypes (Either (Either Float Int) (Either Int8 Int16)) = '[RNS [Float, Int, Int8, Int16]]
  fields (Left x)  = case fields x of
    Cons (RZ x') Nil      -> Cons (RZ x') Nil
    Cons (RS (RZ x')) Nil -> Cons (RS $ RZ x') Nil
  fields (Right x) = case fields x of
    Cons (RZ x') Nil      -> Cons (RS $ RS $ RZ x') Nil
    Cons (RS (RZ x')) Nil -> Cons (RS $ RS $ RS $ RZ x') Nil


-- Instance for product types (tuples)
-- Recursively defined, because concatenation is a whole lot easier then zipWith (++)
instance (MemRep x, MemRep y) => MemRep (x, y) where
  type ChoiceTypes (x,y) = Eval (ChoiceTypes x ++ ChoiceTypes y)
  choices (x,y) = rvconcat (choices x) (choices y)

  type FieldTypes (x, y) = Eval (FieldTypes x ++ FieldTypes y)
  fields (x,y) = rvconcat (fields x) (fields y)
