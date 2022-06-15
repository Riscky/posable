{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- This is needed to derive POSable for tuples of size more then 4
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}

-- | This module contains instances of `POSable` for all non-recursive prelude
--   data types, like tuples, `Either` and `Maybe`
module Generics.POSable.Instances (POSable) where

import           Generics.POSable.POSable
import           Generics.POSable.Representation
import           Language.Haskell.TH

-----------------------------------------------------------------------
-- Instances for non-recursive prelude data types
deriving instance POSable Bool
deriving instance POSable x => POSable (Maybe x)
deriving instance (POSable l, POSable r) => POSable (Either l r)
deriving instance POSable Ordering

deriving instance POSable ()

deriving instance POSable Undef

-- Instances for tuples of length 2 - 16
runQ $ do
  let
    mkTuple :: Int -> Q Dec
    mkTuple n =
      let
          xs  = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
          ts  = map varT xs
          res = foldl (\ts' t -> [t| $ts' $t |]) (tupleT (length ts)) ts
          ctx = mapM (appT [t| POSable |]) ts
      in
      instanceD ctx [t| POSable $res |] []
  mapM mkTuple [2..16]

