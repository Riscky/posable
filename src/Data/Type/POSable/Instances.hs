{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- This is needed to derive POSable for tuples of size more then 4
{-# OPTIONS_GHC -fconstraint-solver-iterations=8 #-}

-- | This module contains instances of POSable for all Haskell prelude data types
--   as well as fixed size integers from Data.Int (Int8, Int16, Int32 and Int64)
module Data.Type.POSable.Instances (POSable) where

import           Data.Int                        (Int16, Int8, Int32, Int64)
import           Data.Type.POSable.POSable
import           Data.Type.POSable.Representation

-----------------------------------------------------------------------
-- Instances for common nonrecursive Haskell datatypes
deriving instance POSable Bool
deriving instance POSable x => POSable (Maybe x)
deriving instance (POSable l, POSable r) => POSable (Either l r)
deriving instance POSable Ordering

deriving instance POSable ()
deriving instance (POSable a, POSable b) => POSable (a,b)
deriving instance (POSable a, POSable b, POSable c) => POSable (a,b,c)
deriving instance (POSable a, POSable b, POSable c, POSable d) => POSable (a,b,c,d)
deriving instance (POSable a, POSable b, POSable c, POSable d, POSable e) => POSable (a,b,c,d,e)
deriving instance (POSable a, POSable b, POSable c, POSable d, POSable e, POSable f) => POSable (a,b,c,d,e,f)
deriving instance (POSable a, POSable b, POSable c, POSable d, POSable e, POSable f, POSable g) => POSable (a,b,c,d,e,f,g)
deriving instance (POSable a, POSable b, POSable c, POSable d, POSable e, POSable f, POSable g, POSable h) => POSable (a,b,c,d,e,f,g,h)

-----------------------------------------------------------------------
-- Instances of POSable for machine types

instance POSable Int where
  type Choices Int = 1
  choices _ = 0

  type Fields Int = '[ '[Int]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Float where
  type Choices Float = 1
  choices _ = 0

  type Fields Float = '[ '[Float]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Int8 where
  type Choices Int8 = 1
  choices _ = 0

  type Fields Int8 = '[ '[Int8]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Int16 where
  type Choices Int16 = 1
  choices _ = 0

  type Fields Int16 = '[ '[Int16]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Int32 where
  type Choices Int32 = 1
  choices _ = 0

  type Fields Int32 = '[ '[Int32]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Int64 where
  type Choices Int64 = 1
  choices _ = 0

  type Fields Int64 = '[ '[Int64]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Char where
    type Choices Char = 1
    choices _ = 0

    type Fields Char = '[ '[Char]]
    fields x = Cons (Pick x) Nil

    fromPOSable 0 (Cons (Pick x) Nil) = x
    fromPOSable _ _                   = error "index out of range"

    emptyFields = PTCons (STSucc '_' STZero) PTNil

instance POSable Word where
  type Choices Word = 1
  choices _ = 0

  type Fields Word = '[ '[Word]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Double where
  type Choices Double = 1
  choices _ = 0

  type Fields Double = '[ '[Double]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil
