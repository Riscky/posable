-- Needed to derive POSable
{-# LANGUAGE DeriveAnyClass #-}
-- Needed to derive GHC.Generic
{-# LANGUAGE DeriveGeneric  #-}
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
import           Data.Type.POSable.POSable as POSable
import           Data.Type.POSable.Representation
import           Data.Type.POSable.TH
import           GHC.Generics              as GHC

data Test a b c = C1 a
                | C2 b
                | C3 c
                | C4 a a a a a a a
                | C5 a b c
    deriving (GHC.Generic, POSable.Generic, POSable)

-- Define a set of types that can be the ground types of the POSable
-- representation. Only types in this set can occur in Fields.
instance GroundType Float where
  type TypeRep Float = Float

  mkTypeRep = 0

instance GroundType Double where
  type TypeRep Double = Double

  mkTypeRep = 0


-- Define a POSable instance for these ground types
mkPOSableGroundType ''Float

mkPOSableGroundType ''Double
