{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.Type.Instances where
import qualified GHC.Generics as GHC
import Data.Int (Int8, Int16)
import qualified Generics.SOP as SOP
import Fcf (Eval, type (++))
import Data.Type.MemRep
import Data.Finite (
  finite,
  add,
  multiply,
  combineProduct,
  combineSum,
  separateProduct
  , separateSum
  )
import GHC.TypeNats (type (+), type (*))
import Unsafe.Coerce (unsafeCoerce)


-----------------------------------------------------------------------
-- Instances for common Haskell datatypes
deriving instance MemRep Bool
deriving instance MemRep x => MemRep (Maybe x)
-- deriving instance (MemRep l, MemRep r) => MemRep (Either l r)
deriving instance MemRep ()
-- deriving instance (MemRep a, MemRep b) => MemRep (a,b)


-----------------------------------------------------------------------
-- Instances for some made up datatypes
data Try a b = Som a | Oth b
             deriving (GHC.Generic, SOP.Generic, MemRep, Show)

data Tuple a b = T a b
               deriving (GHC.Generic, SOP.Generic, MemRep)

data Tuple5 a b c d e = T5 a b c d e
                      deriving (GHC.Generic, SOP.Generic, MemRep)

data Unit = Unit
          deriving (GHC.Generic, SOP.Generic, MemRep)

data MultiSum x y = First x y
                  | Second y x
                  deriving (GHC.Generic, SOP.Generic, MemRep)

data Direction n e s = North n
                     | East e
                     | South s
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

  emptyChoices = 1 -- note that this should be equal to Choices Int, but on the value level
  -- we might want to enforce this somehow (TODO)

  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Float where
  type Choices Float = 1
  choices _ = 0

  type Fields Float = '[ '[Float]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [32]

  emptyChoices = 1
  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int8 where
  type Choices Int8 = 1
  choices _ = 0

  type Fields Int8 = '[ '[Int8]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [8]

  emptyChoices = 1
  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int16 where
  type Choices Int16 = 1
  choices _ = 0

  type Fields Int16 = '[ '[Int16]]
  fields x = Cons (Pick x) Nil

  fromMemRep 0 (Cons (Pick x) Nil) = x
  fromMemRep _ _ = error "index out of range"

  widths = [16]

  emptyChoices = 1
  emptyFields = PTCons (STSucc 0 STZero) PTNil


-- Instance for Either, recursively defined
instance (MemRep l, MemRep r) => MemRep (Either l r) where
  type Choices (Either l r) = Choices l + Choices r
  choices (Left lv)  = combineSum (Left (choices lv))
  choices (Right rv) = combineSum (Right (choices rv))

  emptyChoices = emptyChoices @l + emptyChoices @r

  type Fields (Either l r) = Eval (ZipWith' (++) (Fields l) (Fields r))
  fields (Left lv)  = zipSumLeft (fields lv) (emptyFields @r)
  fields (Right rv) = zipSumRight (emptyFields @l) (fields rv)

  widths = zipWith max (widths @l) (widths @r)

  fromMemRep cs fs = case cs' of
      Left lcs -> Left (fromMemRep lcs lfs)
      Right rcs -> Right (fromMemRep rcs rfs)
    where
      cs' = separateSum (unsafeCoerce cs) -- Not sure if safe
      (lfs,rfs) = splitHorizontal fs (emptyFields @l)  (emptyFields @r)

  emptyFields = zipSumT (emptyFields @l) (emptyFields @r)


-- Instance for Direction, recursively defined
instance (MemRep n, MemRep e, MemRep s) => MemRep (Direction n e s) where
  type Choices (Direction n e s) = Choices n + Choices e + Choices s
  choices (North _) = 0
  choices (East  _) = finite (emptyChoices @n)
  choices (South _) = finite (emptyChoices @n + emptyChoices @e)

  type Fields (Direction n e s) =  Eval (Foldl (ZipWith' (++)) '[] '[ Fields n, Fields e, Fields s])
  fields (North nv) = zipSumLeft  (zipSumLeft  (fields nv) (emptyFields @e)) (emptyFields @s)
  fields (East  ev) = zipSumLeft  (zipSumRight (emptyFields @n) (fields ev)) (emptyFields @s)
  fields (South sv) = zipSumRight (zipSumT     (emptyFields @n) (emptyFields @e)) (fields sv)

  fromMemRep = undefined
  --   where
  --     (ncs, _, _) = splitHorizontal3 cs (emptyChoices @n) (emptyChoices @e) (emptyChoices @s)
  --     (nfs, _, _) = splitHorizontal3 fs (emptyFields @n) (emptyFields @e) (emptyFields @s)
  -- fromMemRep (Cons (Pick 1) cs) fs = East (fromMemRep ecs efs)
  --   where
  --     (_, ecs, _) = splitHorizontal3 cs (emptyChoices @n) (emptyChoices @e) (emptyChoices @s)
  --     (_, efs, _) = splitHorizontal3 fs (emptyFields @n) (emptyFields @e) (emptyFields @s)
  -- fromMemRep (Cons (Pick 3) cs) fs = South (fromMemRep scs sfs)
  --   where
  --     (_, _, scs) = splitHorizontal3 cs (emptyChoices @n) (emptyChoices @e) (emptyChoices @s)
  --     (_, _, sfs) = splitHorizontal3 fs (emptyFields @n) (emptyFields @e) (emptyFields @s)
  -- fromMemRep _                  _  = error "constructor index out of bounds"
  
  emptyChoices = 3 -- should be equal to Choices x
  emptyFields = zipSumT (zipSumT (emptyFields @n) (emptyFields @e)) (emptyFields @s)

-- Instance for product types (tuples)
instance (MemRep x, MemRep y) => MemRep (x, y) where
  type Choices (x,y) = Choices x * Choices y
  choices (x,y) = combineProduct (choices x, choices y)

  type Fields (x, y) = Eval (Fields x ++ Fields y)
  fields (x,y) = rvconcat (fields x) (fields y)

  widths = widths @x ++ widths @y

  emptyFields = rvconcatT (emptyFields @x) (emptyFields @y)

  fromMemRep cs fs = (fromMemRep xcs xfs, fromMemRep ycs yfs)
                   where
                     (xcs, ycs) = separateProduct cs
                     (xfs, yfs) = split fs (emptyFields @x) (emptyFields @y)

-- Instance for 3-tuples
instance (MemRep x, MemRep y, MemRep z) => MemRep (x, y, z) where
  type Choices (x, y, z) = Choices x * Choices y * Choices z
  choices (x, y, z) = combineProduct (combineProduct (choices x, choices y),choices z)

  type Fields (x, y, z) = Eval (Eval (Fields x ++ Fields y) ++ Fields z)
  fields (x, y, z) = rvconcat (rvconcat (fields x) (fields y)) (fields z)

  widths = widths @x ++ widths @y ++ widths @z

  emptyFields = rvconcatT (rvconcatT (emptyFields @x) (emptyFields @y)) (emptyFields @z)

  fromMemRep cs fs = (fromMemRep xcs xfs, fromMemRep ycs yfs, fromMemRep zcs zfs)
                   where
                    (xcs, ycs)  = separateProduct xycs
                    (xycs, zcs) = separateProduct cs
                    (PSCons xfs (PSCons yfs (PSCons zfs PSNil))) = splits fs $ PSTCons (emptyFields @x)  $ PSTCons (emptyFields @y)  $ PSTCons (emptyFields @z)  PSTNil

