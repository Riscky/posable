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

module Generics where

import Generics.SOP (All, All2, Code, Generic, I(I), SOP(SOP), NS(Z,S), NP((:*), Nil))
import qualified Generics.SOP as SOP
import Data.Finite.Internal (Finite)
import Data.Type.Equality

import Fcf

import MemRep
import qualified MemRep as MR



-----------------------------------------------------------------------
-- GMemRep, the serf of this file
class (All IsRNS (GChoiceTypes x), All IsRNS (GFieldTypes x)) => GMemRep x where
  type GChoiceTypes x :: [*]
  gchoices :: x -> Vector (GChoiceTypes x)

  type GFieldTypes x :: [*]
  gfields :: x -> Vector (GFieldTypes x)

  gemptyChoices :: Vector (GChoiceTypes x)
  gemptyFields :: Vector (GFieldTypes x)

-- Instance for Either-like types
instance (All IsRNS (GChoiceTypes (SOP I '[ '[l], '[r]])), All IsRNS (GFieldTypes (SOP I '[ '[l], '[r]])), MemRep l, MemRep r) => GMemRep (SOP I '[ '[l], '[r]]) where
  type GChoiceTypes (SOP I '[ '[l], '[r]]) =  Eval ('[RNS '[Finite 2]] ++ Eval (ZipWith' (<>) (ChoiceTypes l) (ChoiceTypes r)))
  gchoices (SOP (Z (I lv :* SOP.Nil)))      = Cons (RZ 0) (zipLeft (choices lv) (emptyChoices @ r))
  gchoices (SOP (S (Z (I rv :* SOP.Nil)))) = Cons (RZ 1) (zipRight (emptyChoices @ l) (choices rv))

  type GFieldTypes (SOP I '[ '[l], '[r]]) = Eval (ZipWith' (<>) (FieldTypes l) (FieldTypes r))
  gfields (SOP (Z (I lv :* SOP.Nil)))     = zipLeft  (fields lv)       (emptyFields @ r)
  gfields (SOP (S (Z (I rv :* SOP.Nil)))) = zipRight (emptyFields @ l) (fields rv)

  gemptyChoices = Cons Empty (rnsConcat (emptyChoices @ l) (emptyChoices @ r))
  gemptyFields = rnsConcat (emptyFields @ l) (emptyFields @ r)

-- Instance for Tuple-like types
instance (All IsRNS (GChoiceTypes (SOP I '[ '[a, b]])), All IsRNS (GFieldTypes (SOP I '[ '[a, b]])), MemRep a, MemRep b) => GMemRep (SOP I '[ '[a, b]]) where
  type GChoiceTypes (SOP I '[ '[a, b]]) = Eval (ChoiceTypes a ++ ChoiceTypes b)
  gchoices (SOP (Z (I av :* I bv :* SOP.Nil))) = rvconcat (choices av) (choices bv)

  type GFieldTypes (SOP I '[ '[a, b]]) = Eval (FieldTypes a ++ FieldTypes b)
  gfields (SOP (Z (I av :* I bv :* SOP.Nil))) = rvconcat (fields av) (fields bv)

  gemptyChoices = rvconcat (emptyChoices @ a) (emptyChoices @ b)
  gemptyFields = rvconcat (emptyFields @ a) (emptyFields @ b)
