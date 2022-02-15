{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- This is needed to derive MemRep for tuples of size more then 4
{-# OPTIONS_GHC -fconstraint-solver-iterations=8 #-}

module Data.Type.MemRep.Instances (MemRep) where

import           Data.Int                        (Int16, Int8)
import           Data.Type.MemRep.Generic        ()
import           Data.Type.MemRep.MemRep
import           Data.Type.MemRep.Representation

-----------------------------------------------------------------------
-- Instances for common nonrecursive Haskell datatypes
deriving instance MemRep Bool
deriving instance MemRep x => MemRep (Maybe x)
deriving instance (MemRep l, MemRep r) => MemRep (Either l r)
deriving instance MemRep Ordering

deriving instance MemRep ()
deriving instance (MemRep a, MemRep b) => MemRep (a,b)
deriving instance (MemRep a, MemRep b, MemRep c) => MemRep (a,b,c)
deriving instance (MemRep a, MemRep b, MemRep c, MemRep d) => MemRep (a,b,c,d)
deriving instance (MemRep a, MemRep b, MemRep c, MemRep d, MemRep e) => MemRep (a,b,c,d,e)
deriving instance (MemRep a, MemRep b, MemRep c, MemRep d, MemRep e, MemRep f) => MemRep (a,b,c,d,e,f)
deriving instance (MemRep a, MemRep b, MemRep c, MemRep d, MemRep e, MemRep f, MemRep g) => MemRep (a,b,c,d,e,f,g)
deriving instance (MemRep a, MemRep b, MemRep c, MemRep d, MemRep e, MemRep f, MemRep g, MemRep h) => MemRep (a,b,c,d,e,f,g,h)

-----------------------------------------------------------------------
-- Instances of MemRep for machine types

instance MemRep Int where
  type Choices Int = 1
  choices _ = 0

  type Fields Int = '[ '[Int]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Float where
  type Choices Float = 1
  choices _ = 0

  type Fields Float = '[ '[Float]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int8 where
  type Choices Int8 = 1
  choices _ = 0

  type Fields Int8 = '[ '[Int8]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int16 where
  type Choices Int16 = 1
  choices _ = 0

  type Fields Int16 = '[ '[Int16]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Char where
    type Choices Char = 1
    choices _ = 0

    type Fields Char = '[ '[Char]]
    fields x = Cons (Pick x) Nil

    fromMemRep 0 (Cons (Pick x) Nil) = x
    fromMemRep _ _                   = error "index out of range"

    emptyFields = PTCons (STSucc '_' STZero) PTNil

instance MemRep Word where
  type Choices Word = 1
  choices _ = 0

  type Fields Word = '[ '[Word]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Double where
  type Choices Double = 1
  choices _ = 0

  type Fields Double = '[ '[Double]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil
