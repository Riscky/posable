{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- This is needed to derive MemRep for tuples of size more then 4
{-# OPTIONS_GHC -fconstraint-solver-iterations=6 #-}

module Data.Type.MemRep.Instances where

import qualified GHC.Generics as GHC
import Data.Int (Int8, Int16)
import Generics.SOP hiding (Nil)
import qualified Generics.SOP as SOP
import Data.Type.MemRep.MemRep
import Data.Finite
  ( combineSum
  , separateSum
  , Finite
  )
import GHC.TypeNats (type (+))
import Data.Type.MemRep.Generic
import Data.Type.MemRep.Representation

-----------------------------------------------------------------------
-- Instances for common Haskell datatypes
-- deriving instance MemRep Bool
-- deriving instance MemRep x => MemRep (Maybe x)
-- -- deriving instance (MemRep l, MemRep r) => MemRep (Either l r)
deriving instance MemRep ()
-- deriving instance (MemRep a, MemRep b) => MemRep (a,b)


-----------------------------------------------------------------------
-- Instances for some made up datatypes
-- data Try a b = Som a | Oth b
--              deriving (GHC.Generic, SOP.Generic, MemRep, Show)

data Tuple1 a = T1 a
              deriving (GHC.Generic, SOP.Generic, MemRep)

data Tuple a b = T a b
               deriving (GHC.Generic, SOP.Generic, MemRep)

data Tuple3 a b c = T3 a b c
                  deriving (GHC.Generic, SOP.Generic, MemRep, Show)

data Tuple5 a b c d e = T5 a b c d e
                      deriving (GHC.Generic, SOP.Generic, MemRep)

data Unit = Unit
          deriving (GHC.Generic, SOP.Generic, MemRep)

-- data MultiSum x y = First x y
--                   | Second y x
--                   deriving (GHC.Generic, SOP.Generic, MemRep)

data Direction n e s = North n
                     | East e
                     | South s
                     deriving (Show)
                    --  deriving (GHC.Generic, SOP.Generic, MemRep)


-----------------------------------------------------------------------
-- Instances of MemRep for machine types

-- Sadly, this definition due to overlapping instances:

-- instance Base x => MemRep x where
--   type Choices x = '[]
--   choices x = Nil

--   type Fields x = '[Sum '[x]]
--   mtfields x = Cons (Pick x) Nil

-- Instead, we have to do with a seperate definition per base type, which leads
-- to a horrible amount of boilerplate.
-- This is fixable with some Template Haskell, but let's not go there now.
instance MemRep Int where
  type Choices Int = 1
  choices _ = 0

  type Fields Int = '[ '[Int]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [32]

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Float where
  type Choices Float = 1
  choices _ = 0

  type Fields Float = '[ '[Float]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [32]

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int8 where
  type Choices Int8 = 1
  choices _ = 0

  type Fields Int8 = '[ '[Int8]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [8]

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int16 where
  type Choices Int16 = 1
  choices _ = 0

  type Fields Int16 = '[ '[Int16]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [16]

  emptyFields = PTCons (STSucc 0 STZero) PTNil


-- Instance for Either, recursively defined
instance (MemRep l, MemRep r) => MemRep (Either l r) where
  type Choices (Either l r) = Sums (MapProducts (Map2Choices '[ '[l], '[r]]))
  choices (Left lv)  = combineSum (Left (choices lv))
  choices (Right rv) = combineSum (Right (choices rv))

  type Fields (Either l r) = Merge (Fields l) (Fields r)
  fields (Left lv)  = zipSumLeft (fields lv) (emptyFields @r)
  fields (Right rv) = zipSumRight (emptyFields @l) (fields rv)

  widths = zipWith max (widths @l) (widths @r)

  fromMemRep cs fs = case cs' of
      Left lcs -> Left (fromMemRep lcs lfs)
      Right rcs -> Right (fromMemRep rcs rfs)
    where
      cs' :: Either (Finite (Choices l)) (Finite (Choices r))
      cs' = separateSum cs
      (lfs,rfs) = splitHorizontal fs (emptyFields @l) (emptyFields @r)

  emptyFields = zipSumT (emptyFields @l) (emptyFields @r)


-- Instance for Direction, recursively defined
instance (MemRep n, MemRep e, MemRep s) => MemRep (Direction n e s) where
  type Choices (Direction n e s) = Sums '[Choices n, Choices e, Choices s]
  choices (North nv) = sums ((Z (choices nv)) :: NS Finite '[Choices n, Choices e, Choices s])
  choices (East  ev) = sums ((S (Z (choices ev))) :: NS Finite '[Choices n, Choices e, Choices s])
  choices (South sv) = sums ((S (S (Z (choices sv)))) :: NS Finite '[Choices n, Choices e, Choices s])

  type Fields (Direction n e s) = FoldMerge '[Fields n, Fields e, Fields s]
  fields (North nv) = zipSumLeft  (fields nv)      (zipSumT     (emptyFields @e) (emptyFields @s))
  fields (East  ev) = zipSumRight (emptyFields @n) (zipSumLeft  (fields ev)      (emptyFields @s))
  fields (South sv) = zipSumRight (emptyFields @n) (zipSumRight (emptyFields @e) (fields sv))

  fromMemRep cs fs = case (cs', fs') of
    (Z nc, Z nf) -> North (fromMemRep nc nf)
    (S (Z ec), S (Z ef)) -> East (fromMemRep ec ef)
    (S (S (Z sc)), S (S (Z sf))) -> South (fromMemRep sc sf)
    (_,_) -> error "Choices do not match Fields"
    where
      cs' = unSums @'[Choices n, Choices e, Choices s] cs
      fs' = unMerge fs (emptyFields @n :* emptyFields @e :* emptyFields @s :* SOP.Nil)
  
  emptyFields = foldMergeT (emptyFields @n :* emptyFields @e :* emptyFields @s :* SOP.Nil)

-- Instance for product types (tuples)
instance (MemRep x, MemRep y) => MemRep (x, y) where
  type Choices (x,y) = Products '[Choices x, Choices y]
  choices (x,y) = combineProducts (choices x :* choices y :* SOP.Nil)

  type Fields (x, y) = Appends [Fields x, Fields y]
  fields (x,y) = appends (fields x :* fields y :* SOP.Nil)

  widths = widths @x ++ widths @y

  emptyFields = appendsT (emptyFields @x :* emptyFields @y :* SOP.Nil)

  fromMemRep cs fs = (fromMemRep xcs xfs, fromMemRep ycs yfs)
                   where
                     (xcs :* ycs :* SOP.Nil) = separateProducts cs (emptyChoices @x :* emptyChoices @y :* SOP.Nil)
                     (xfs :* yfs :* SOP.Nil) = unAppends fs (emptyFields @x :* emptyFields @y :* SOP.Nil)

-- Instance for 3-tuples
instance (MemRep x, MemRep y, MemRep z) => MemRep (x, y, z) where
  type Choices (x, y, z) = Products '[Choices x, Choices y, Choices z]
  choices (x, y, z) = combineProducts (choices x :* choices y :* choices z :* SOP.Nil)

  type Fields (x, y, z) = Appends '[Fields x, Fields y, Fields z]
  fields (x, y, z) = concatP (fields x) (concatP (fields y) (concatP (fields z) Nil))

  widths = widths @x ++ widths @y ++ widths @z

  emptyFields = concatPT (emptyFields @x) (concatPT (emptyFields @y) (concatPT (emptyFields @z) (PTNil)))

  fromMemRep cs fs = (fromMemRep xcs xfs, fromMemRep ycs yfs, fromMemRep zcs zfs)
                   where
                    (xcs :* ycs :* zcs :* SOP.Nil) = separateProducts cs (emptyChoices @x :* emptyChoices @y :* emptyChoices @z :* SOP.Nil)
                    (xfs :* yfs :* zfs :* SOP.Nil) = unAppends fs (emptyFields @x :* emptyFields @y :* emptyFields @z :* SOP.Nil)
