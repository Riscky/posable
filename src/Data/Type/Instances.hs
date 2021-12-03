{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.Type.Instances (Bool, Maybe, Either) where

import Data.Type.MemRep
    ( Elt(..), Remainder(Zero), Sum(..), Product(Nil, Cons) )
import qualified GHC.Generics as GHC
import Data.Int (Int8, Int16)
import qualified Generics.SOP as SOP

-----------------------------------------------------------------------
-- Instances for common Haskell datatypes
deriving instance Elt Bool
deriving instance Elt x => Elt (Maybe x)
-- deriving instance (Elt l, Elt r) => Elt (Either l r)
deriving instance Elt ()
-- deriving instance (Elt a, Elt b) => Elt (a,b)


-----------------------------------------------------------------------
-- Instances for some made up datatypes
data Try a b = Som a | Oth b
             deriving (GHC.Generic, SOP.Generic, Elt)

data Tuple a b = T a b
               deriving (GHC.Generic, SOP.Generic, Elt)

data Tuple5 a b c d e = T5 a b c d e
                      deriving (GHC.Generic, SOP.Generic, Elt)

data Unit = Unit
          deriving (GHC.Generic, SOP.Generic, Elt)

data MultiSum x y = First x y
                  | Second y x
                  deriving (GHC.Generic, SOP.Generic, Elt)

data Direction n e s = North n
                     | East e
                     | South s
                     deriving (GHC.Generic, SOP.Generic, Elt)


-----------------------------------------------------------------------
-- Instances of Elt for machine types

-- Sadly, this definition due to overlapping instances:

-- instance Base x => Elt x where
--   type Choices x = '[]
--   choices x = Nil

--   type Fields x = '[Sum '[x]]
--   mtfields x = Cons (Pick x) Nil

-- Instead, we have to do with a seperate definition per base type, which leads
-- to a horrible amount of boilerplate.
-- This is fixable with some Template Haskell, but let's not go there now.
instance Elt Int where
  type Choices Int = '[]
  choices _ = Nil

  type Fields Int = '[Sum '[Int]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance Elt Float where
  type Choices Float = '[]
  choices _ = Nil

  type Fields Float = '[Sum '[Float]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance Elt Int8 where
  type Choices Int8 = '[]
  choices _ = Nil

  type Fields Int8 = '[Sum '[Int8]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [8]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance Elt Int16 where
  type Choices Int16 = '[]
  choices _ = Nil

  type Fields Int16 = '[Sum '[Int16]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [16]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil
