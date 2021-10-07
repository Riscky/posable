{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Main where

import Generics.SOP
import Generics.SOP.NP
import Data.Int
import qualified GHC.Generics as G
import Data.Kind
import Data.Array.Accelerate.Representation.Tag
import GHC.Float

-- class SizeOf a where
--   sizeof :: a -> DataShape

main :: IO ()
main = print "hello world"

-- gsizeof :: (Generic a, Code a ~(xs : xss), All SizeOf xs) => Proxy a -> DataShape
-- gsizeof p = PofP $ collapse_POP $ cpure p (I sizeof)

-- pureEllende :: POP f xss
-- pureEllende = hcpure p (I sizeof)
--             where
--               p = Proxy :: Proxy SizeOf

-- gdef :: (Generic a, All2 SizeOf (Code a)) => Proxy a -> DataShape
-- gdef p = (cpure @POP p (I sizeof)) injections


-- outershapeNP :: (f ~ K a, SizeOf a, All2 SizeOf xss) => NP (NP f) xss -> DataShape
-- outershapeNP Nil         = PofP []
-- outershapeNP (xs :* xss) = case outershapeNP xss of
--                             PofP yss -> PofP (shapeNP xs : yss)

-- shapeNP :: (f ~ K a, SizeOf a, All SizeOf xs) => NP f xs -> [DataShape]
-- shapeNP Nil       = []
-- shapeNP (x :* xs) = sizeof (unK x) : shapeNP xs


-- p :: Proxy SizeOf
-- p = Proxy

-- instance SizeOf Int8 where
--   sizeof _ = Singleton 8

-- instance SizeOf Int32 where
--   sizeof _ = Singleton 32

-- instance SizeOf Int64 where
--   sizeof _ = Singleton 64

-- data Test = A Int8 Int32
--           | B Int8
--           deriving G.Generic

-- instance Generic Test

-- instance SizeOf Test where
--   sizeof = gsizeof

-- instance SizeOf Bool where
--   sizeof = gsizeof

newtype EitherTree = EitherTree (Either (Either (Either Int Int) (Either Int Int)) (Either (Either Int Int) (Either Int Int)))
                  deriving (G.Generic, Show)

instance Generic EitherTree

exampleTree = Left (Right (Left 1))

fromSOP :: Generic a => a -> NS (NP I) (Code a)
fromSOP x = (\(SOP xs) -> xs) (from x)

-- fromNS :: NS a b -> p
-- fromNS (Z x) = x
-- fromNS (S x) = x

class Elt a where
  type EltR a :: Type
  fromElt :: a -> EltR a
  defaultElt :: a -> EltR a
  -- toElt   :: EltR a -> a

instance Elt Int where
  type EltR Int = Int
  fromElt a = a
  defaultElt _ = 0
  -- toElt a = a

instance Elt a => Elt (Maybe a) where
  type EltR (Maybe a) = (TAG, ((), EltR a))
  fromElt Nothing  = (0, ((), defaultElt (undefined :: a)))
  fromElt (Just x) = (1, ((), fromElt x))
  defaultElt _ = (0, ((), defaultElt (undefined :: a)))

instance (Elt l, Elt r) => Elt (Either l r) where
  type EltR (Either l r) = (TAG, (((), EltR l), EltR r))
  fromElt (Left x)  = (0, (((), fromElt x), defaultElt (undefined :: r)))
  fromElt (Right x) = (1, (((), defaultElt (undefined :: l)), fromElt x ))
  defaultElt _ = (0, (((), defaultElt (undefined :: l)), defaultElt (undefined ::r)))


-- class MemRep a where
--   memRep :: MRep

-- instance MemRep Int where
--   memRep = 32

-- instance MemRep a => MemRep (Maybe a) where
--   memRep = FieldSet [TagSet ]

data A a b = A a a a
           | B b b

type Thing = A (Either Int16 Int8) (Maybe Int32)

newtype Single = Hoi Thing

---------

data InnerRep = Tagged [[InnerRep]] -- outerlist contains sum, inner list contains field
              | Base Int -- width in integers
              deriving (Show)

memWidthI :: InnerRep -> Int
memWidthI a = case a of
                Tagged xxs -> let amountOfConstructors = length xxs
                                  maximumInnerWidth    = maximum $ map (sum . map memWidthI) xxs
                              in  maximumInnerWidth + log2 amountOfConstructors
                Base x    -> x

class MemRep a where
  memRep :: InnerRep
  memWidth :: Int
  memWidth = memWidthI (memRep @ a)

-- binary log with rounding upwards
-- this works up to at least 256 :)
log2 :: Int -> Int
log2 x = let fl = int2Float x
             log10 = log fl
             log2 = log 2.0
         in ceiling $ log10 / log2

instance MemRep Int8 where
  memRep = Base 8

instance MemRep Int16 where
  memRep = Base 16

instance MemRep Int32 where
  memRep = Base 32

instance MemRep Int64 where
  memRep = Base 64

instance MemRep a => MemRep (Maybe a) where
  memRep = Tagged [[],[memRep @ a]]

instance (MemRep l, MemRep r) => MemRep (Either l r) where
  memRep = Tagged [[memRep @ l], [memRep @ r]]

instance (MemRep a, MemRep b) => MemRep (A a b) where
  memRep = Tagged [[memRep @ a, memRep @ a, memRep @ a],[memRep @ b, memRep @ b]]
