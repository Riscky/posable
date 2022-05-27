-- Needed to derive POSable
{-# LANGUAGE DeriveAnyClass  #-}
-- Needed to derive GHC.Generic
{-# LANGUAGE DeriveGeneric   #-}
-- To generate instances for ground types
{-# LANGUAGE TemplateHaskell #-}
-- Needed to determine the tag size at compile time
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- Larger types need more iterations
{-# OPTIONS_GHC -fconstraint-solver-iterations=11 #-}
{-# OPTIONS_GHC -ddump-splices #-}

-- | Contains an example for deriving POSable for some datatype
module Examples () where

-- POSable re-exports SOP.Generic
import           GHC.Generics                    as GHC
import           Generics.POSable.POSable        as POSable
import           Generics.POSable.Representation
import           Generics.POSable.TH

data Test a b c = C1 a
                | C2 b
                | C3 c
                | C4 a a a a a a a
                | C5 a b c
    deriving (GHC.Generic, POSable.Generic, POSable)

-- Define a set of types that can be the ground types of the POSable
-- representation. Only types in this set can occur in Fields.
instance Ground Float where
  mkGround = 0.0

instance Ground Double where
  mkGround = 0


-- Define a POSable instance for these ground types
mkPOSableGround ''Float

mkPOSableGround ''Double
