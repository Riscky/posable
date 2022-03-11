{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- This is needed to derive POSable for tuples of size more then 4
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}

-- | This module contains instances of `POSable` for all Haskell prelude data types
--   as well as fixed size integers from Data.Int (`Int8`, `Int16`, `Int32` and `Int64`)
module Data.Type.POSable.Instances (POSable) where

import           Data.Int                         (Int16, Int32, Int64, Int8)
import           Data.Type.POSable.POSable
import           Data.Type.POSable.Representation
import Language.Haskell.TH

-----------------------------------------------------------------------
-- Instances for common nonrecursive Haskell datatypes
deriving instance POSable Bool
deriving instance POSable x => POSable (Maybe x)
deriving instance (POSable l, POSable r) => POSable (Either l r)
deriving instance POSable Ordering

deriving instance POSable ()

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

