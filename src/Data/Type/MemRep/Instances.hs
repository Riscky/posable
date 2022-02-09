{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- This is needed to derive MemRep for tuples of size more then 4
{-# OPTIONS_GHC -fconstraint-solver-iterations=6 #-}

module Data.Type.MemRep.Instances (MemRep) where

import qualified GHC.Generics as GHC
import Data.Int (Int8, Int16)
import qualified Generics.SOP as SOP
import Data.Type.MemRep.MemRep
import Data.Type.MemRep.Generic ()
import Data.Type.MemRep.Representation

-----------------------------------------------------------------------
-- Instances for common Haskell datatypes
deriving instance MemRep Bool
deriving instance MemRep x => MemRep (Maybe x)
deriving instance (MemRep l, MemRep r) => MemRep (Either l r)
deriving instance MemRep ()
deriving instance (MemRep a, MemRep b) => MemRep (a,b)


-----------------------------------------------------------------------
-- Instances for some made up datatypes
data Try a b = Som a | Oth b
             deriving (GHC.Generic, SOP.Generic, MemRep, Show)

data Tuple1 a = T1 a
              deriving (GHC.Generic, SOP.Generic, MemRep)

data Tuple a b = T a b
               deriving (GHC.Generic, SOP.Generic, MemRep)

data Tuple3 a b c = T3 a b c
                  deriving (GHC.Generic, SOP.Generic, MemRep, Show)

data Tuple5 a b c d e = T5 a b c d e
                      deriving (GHC.Generic, SOP.Generic, MemRep)

data Unit = Unit
          deriving (GHC.Generic, SOP.Generic, MemRep)

data MultiSum x y = First x y
                  | Second y x
                  deriving (GHC.Generic, SOP.Generic, MemRep, Show)

data Direction n e s = North n
                     | East e
                     | South s
                     deriving (Show)

-----------------------------------------------------------------------
-- Instances of MemRep for machine types

-- Sadly, this definition due to overlapping instances:

-- instance Base x => MemRep x where
--   type Choices x = '[]
--   choices x = Nil

--   type Fields x = '[Sum '[x]]
--   mtfields x = Cons (Pick x) Nil

-- Instead, we have to do with a seperate definition per base type, which leads
-- to a horrible amount of boilerplate.
-- This is fixable with some Template Haskell, but let's not go there now.
instance MemRep Int where
  type Choices Int = 1
  choices _ = 0

  type Fields Int = '[ '[Int]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [32]

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Float where
  type Choices Float = 1
  choices _ = 0

  type Fields Float = '[ '[Float]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [32]

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int8 where
  type Choices Int8 = 1
  choices _ = 0

  type Fields Int8 = '[ '[Int8]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [8]

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int16 where
  type Choices Int16 = 1
  choices _ = 0

  type Fields Int16 = '[ '[Int16]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [16]

  emptyFields = PTCons (STSucc 0 STZero) PTNil
