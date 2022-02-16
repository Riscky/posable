-- Needed to derive POSable
{-# LANGUAGE DeriveAnyClass #-}
-- Needed to derive GHC.Generic
{-# LANGUAGE DeriveGeneric  #-}
-- Needed to determine the tag size at compile time
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- Larger types need more iterations
{-# OPTIONS_GHC -fconstraint-solver-iterations=11 #-}

-- | Contains an example for deriving POSable for some datatype
module Examples () where

-- POSable re-exports SOP.Generic
import           Data.Type.POSable.POSable as POSable
import           GHC.Generics            as GHC

data Test a b c = C1 a
                | C2 b
                | C3 c
                | C4 a a a a a a a
                | C5 a b c
    deriving (GHC.Generic, POSable.Generic, POSable)

