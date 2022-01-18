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

module Data.Type.Instances where
import qualified GHC.Generics as GHC
import Data.Int (Int8, Int16)
import qualified Generics.SOP as SOP
import Data.Finite (Finite)
import Fcf (Eval, type (++))
import Data.Type.MemRep
    ( MemRep(..),
      ZipWith',
      Sum(..),
      Product(Nil, Cons),
      SumType(..),
      ProductType(..),
      rvconcat,
      rvconcatT
    , zipSumT
    , zipSumRight
    , zipSumLeft
    , split
    )

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
             deriving (GHC.Generic, SOP.Generic, MemRep)

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
                     deriving (GHC.Generic, SOP.Generic, MemRep)


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
  type Choices Int = '[]
  choices _ = Nil

  type Fields Int = '[ '[Int]]
  fields x = Cons (Pick x) Nil

  fromMemRep Nil (Cons (Pick x) Nil) = x

  widths = [32]

  emptyChoices = PTNil
  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Float where
  type Choices Float = '[]
  choices _ = Nil

  type Fields Float = '[ '[Float]]
  fields x = Cons (Pick x) Nil

  fromMemRep Nil (Cons (Pick x) Nil) = x

  widths = [32]

  emptyChoices = PTNil
  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int8 where
  type Choices Int8 = '[]
  choices _ = Nil

  type Fields Int8 = '[ '[Int8]]
  fields x = Cons (Pick x) Nil

  fromMemRep Nil (Cons (Pick x) Nil) = x

  widths = [8]

  emptyChoices = PTNil
  emptyFields = PTCons (STSucc 0 STZero) PTNil

instance MemRep Int16 where
  type Choices Int16 = '[]
  choices _ = Nil

  type Fields Int16 = '[ '[Int16]]
  fields x = Cons (Pick x) Nil

  fromMemRep Nil (Cons (Pick x) Nil) = x

  widths = [16]

  emptyChoices = PTNil
  emptyFields = PTCons (STSucc 0 STZero) PTNil



-- Instance for Either, recursively defined
instance (MemRep l, MemRep r) => MemRep (Either l r) where
  type Choices (Either l r) = '[Finite 2] ': Eval (ZipWith' (++) (Choices l) (Choices r))
  choices (Left lv)  = Cons (Pick 0) (zipSumLeft (choices lv) (emptyChoices @r))
  choices (Right rv) = Cons (Pick 1) (zipSumRight (emptyChoices @l) (choices rv))

  type Fields (Either l r) = Eval (ZipWith' (++) (Fields l) (Fields r))
  fields (Left lv)  = zipSumLeft (fields lv) (emptyFields @r)
  fields (Right rv) = zipSumRight (emptyFields @l) (fields rv)

  widths = zipWith max (widths @l) (widths @r)

  fromMemRep (Cons (Pick 0) cs) fs = undefined --  Left (fromMemRep lcs lfs)
                                        -- where
                                        --   lcs = splitLeftWith cs (emptyChoices @l) (emptyChoices @r)
                                        --   lfs = splitLeftWith fs (emptyFields @l)  (emptyFields @r)
  fromMemRep (Cons (Pick 1) cs) fs = undefined -- Right (fromMemRep rcs rfs)
                                        -- where
                                        --   rcs = splitRightWith cs (emptyChoices @l) (emptyChoices @r)
                                        --   rfs = splitRightWith fs (emptyFields @l) (emptyFields @r)
  fromMemRep (Cons _             _)  _  = error "constructor index out of bounds"

  emptyChoices = PTCons (STSucc 0 STZero) (zipSumT (emptyChoices @l) (emptyChoices @r))
  emptyFields = zipSumT (emptyFields @l) (emptyFields @r)


-- instance (MemRep a, MemRep b) => MemRep (Either (a, b) (b, a)) where
--   type Choices (Either (a, b) (b, a)) = Sum '[Finite 2] ': Eval (ZipWith' (<>) (Choices (a, b)) (Choices (b, a)))
--   choices (Left x)  = Cons (Pick 0 Zero) (zipSum (choices x) (emptyChoices @ (b, a)))
--   choices (Right x) = Cons (Pick 1 Zero) (zipSum (emptyChoices @ (a,b)) (choices x))

--   type Fields (Either (a, b) (b, a)) = Fields (a, b)
--   fields (Left  (a,b)) = fields (a,b)
--   fields (Right (b,a)) = fields (a,b)

--   fromMemRep (Cons (Pick 0 Zero) cs) fs = Left (fromMemRep cs fs)
--   fromMemRep (Cons (Pick 1 Zero) cs) fs | (a,b) <- fromMemRep cs fs = Right (b,a)

  -- widths = [16]

  -- emptyChoices = Nil
  -- emptyFields = Cons (Pick 0 Zero) Nil

-- Instance for product types (tuples)
instance (MemRep x, MemRep y) => MemRep (x, y) where
  type Choices (x,y) = Eval (Choices x ++ Choices y)
  choices (x,y) = rvconcat (choices x) (choices y)

  type Fields (x, y) = Eval (Fields x ++ Fields y)
  fields (x,y) = rvconcat (fields x) (fields y)

  widths = widths @x ++ widths @y

  emptyChoices = rvconcatT (emptyChoices @x) (emptyChoices @y)
  emptyFields = rvconcatT (emptyFields @x) (emptyFields @y)

  fromMemRep cs fs = (fromMemRep xcs xfs, fromMemRep ycs yfs)
                   where
                     (xcs, ycs) = split cs (emptyChoices @x) (emptyChoices @y)
                     (xfs, yfs) = split fs (emptyFields @x) (emptyFields @y)

-- Instance for 3-tuples
instance (MemRep x, MemRep y, MemRep z) => MemRep (x, y, z) where
  type Choices (x, y, z) = Eval (Eval (Choices x ++ Choices y) ++ Choices z)
  choices (x, y, z) = rvconcat (rvconcat (choices x) (choices y)) (choices z)

  type Fields (x, y, z) = Eval (Eval (Fields x ++ Fields y) ++ Fields z)
  fields (x, y, z) = rvconcat (rvconcat (fields x) (fields y)) (fields z)

  widths = widths @x ++ widths @y ++ widths @z

  emptyChoices = rvconcatT (rvconcatT (emptyChoices @x) (emptyChoices @y)) (emptyChoices @z)
  emptyFields = rvconcatT (rvconcatT (emptyFields @x) (emptyFields @y)) (emptyFields @z)

  fromMemRep cs fs = (fromMemRep xcs xfs, fromMemRep ycs yfs, fromMemRep zcs zfs)
                   where
                    (xycs, zcs) = split cs (rvconcatT (emptyChoices @x) (emptyChoices @y)) (emptyChoices @z)
                    (xyfs, zfs) = split fs (rvconcatT (emptyFields @x) (emptyFields @y)) (emptyFields @z)
                    (xcs, ycs) = split xycs (emptyChoices @x) (emptyChoices @y)
                    (xfs, yfs) = split xyfs (emptyFields @x) (emptyFields @y)

