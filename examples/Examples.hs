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
import           Data.Type.POSable.Representation
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

instance GroundType Double where
  type TypeRep Double = Double

-- Define a POSable instance for these ground types
instance POSable Float where
  type Choices Float = 1
  choices _ = 0

  type Fields Float = '[ '[Float]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance POSable Double where
  type Choices Double = 1
  choices _ = 0

  type Fields Double = '[ '[Double]]
  fields x = Cons (Pick x) Nil

  fromPOSable 0 (Cons (Pick x) Nil) = x
  fromPOSable _ _                   = error "index out of range"

  emptyFields = PTCons (STSucc 0 STZero) PTNil
