{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- This is needed to derive POSable for tuples of size more then 4
{-# OPTIONS_GHC -fconstraint-solver-iterations=8 #-}

-- | This module contains instances of `POSable` for all Haskell prelude data types
--   as well as fixed size integers from Data.Int (`Int8`, `Int16`, `Int32` and `Int64`)
module Data.Type.POSable.Instances (POSable) where

import           Data.Int                         (Int16, Int32, Int64, Int8)
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
