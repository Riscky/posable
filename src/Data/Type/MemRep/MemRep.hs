{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module Data.Type.MemRep.MemRep where

import Generics.SOP hiding (Nil)
import Data.Finite (Finite)

import qualified Generics.SOP as SOP

import Data.Kind (Type)

import GHC.Base (Nat)
import GHC.TypeLits (KnownNat, natVal)


import Data.Type.MemRep.Representation

-----------------------------------------------------------------------
-- MemRep, the king of this file
class (KnownNat (Choices x)) => MemRep x where
  type Choices x :: Nat
  type Choices x = GChoices (SOP I (Code x))

  choices :: x -> Finite (Choices x)
  default choices ::
    ( Generic x
    , (GMemRep (SOP I (Code x)))
    , GChoices (SOP I (Code x)) ~ Choices x
    ) => x -> Finite (Choices x)
  choices x = gchoices $ from x

  emptyChoices :: Finite (Choices x)
  emptyChoices = 0

  fromMemRep :: Finite (Choices x) -> Product (Fields x) -> x

  default fromMemRep ::
    ( Generic x
    , (GMemRep (SOP I (Code x)))
    , Fields x ~ GFields (SOP I (Code x))
    , Choices x ~ GChoices (SOP I (Code x))
    ) => Finite (Choices x) -> Product (Fields x) -> x
  fromMemRep cs fs = to $ gfromMemRep cs fs

  type Fields x :: [[Type]]
  type Fields x = GFields (SOP I (Code x))

  fields :: x -> Product (Fields x)

  default fields ::
    ( Generic x
    , Fields x ~ GFields (SOP I (Code x))
    , GMemRep (SOP I (Code x))
    ) => x -> Product (Fields x)
  fields x = gfields $ from x

  widths :: [Int]

  emptyFields :: ProductType (Fields x)

  default emptyFields ::
    ( GMemRep (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => ProductType (Fields x)
  emptyFields  = gemptyFields @(SOP I (Code x))

--------------------------------------------------------------
-- Generics

-----------------------------------------------------------------------
-- GMemRep, the serf of this file
class (KnownNat (GChoices x)) => GMemRep x where
  type GChoices x :: Nat
  gchoices :: x -> Finite (GChoices x)

  type GFields x :: [[Type]]
  gfields :: x -> Product (GFields x)

  gfromMemRep :: Finite (GChoices x) -> Product (GFields x) -> x

  gemptyFields :: ProductType (GFields x)
