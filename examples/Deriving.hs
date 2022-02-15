-- Needed to derive MemRep
{-# LANGUAGE DeriveAnyClass #-}
-- Needed to derive GHC.Generic
{-# LANGUAGE DeriveGeneric  #-}
-- Needed to determine the tag size at compile time
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- Larger types need more iterations
{-# OPTIONS_GHC -fconstraint-solver-iterations=11 #-}

module Deriving where

-- MemRep re-exports SOP.Generic
import           Data.Type.MemRep.MemRep as MemRep
import           GHC.Generics            as GHC

data Test a b c = C1 a
                | C2 b
                | C3 c
                | C4 a a a a a a a
                | C5 a b c
    deriving (GHC.Generic, MemRep.Generic, MemRep)
