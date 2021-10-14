{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}


module Main where

import Generics.SOP
import Generics.SOP.NP
import Data.Int
import qualified GHC.Generics as G
import Data.Kind
import Data.Array.Accelerate.Representation.Tag
import GHC.Float
import Data.Maybe
import Data.Universe.Helpers (cartesianProduct)
import Data.List (sortBy, transpose, nub)
import Generics.SOP.NS

import GHC.TypeLits
-- import GHC.TypeLits.Compare
-- import Data.Type.Equality
-- import Data.Proxy
-- import Control.Applicative
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

data InnerRep = Tagged [IProduct] -- outerlist contains sum, inner list contains fields
              | Base Int -- width in integers
              deriving (Show)

newtype IProduct = IProduct [InnerRep]
                 deriving (Show)

unIP :: IProduct -> [InnerRep]
unIP (IProduct x) = x

memWidthI :: InnerRep -> Int
memWidthI a = case a of
                Tagged xxs -> let amountOfConstructors = length xxs
                                  maximumInnerWidth    = maximum $ map (sum . (\(IProduct xs) -> map memWidthI xs)) xxs
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

instance (MemRep a, MemRep b) => MemRep (a,b) where
  memRep = Tagged [IProduct [memRep @ a, memRep @ b]]

instance (MemRep a, MemRep b, MemRep c) => MemRep (a,b, c) where
  memRep = Tagged [IProduct [memRep @ a, memRep @ b, memRep @ c]]

instance MemRep a => MemRep (Maybe a) where
  memRep = Tagged [IProduct [], IProduct [memRep @ a]]

instance (MemRep l, MemRep r) => MemRep (Either l r) where
  memRep = Tagged [IProduct [memRep @ l], IProduct [memRep @ r]]

instance MemRep Bool where
  memRep = Tagged [IProduct [], IProduct []]

instance (MemRep a, MemRep b) => MemRep (A a b) where
  memRep = Tagged [IProduct [memRep @ a, memRep @ a, memRep @ a], IProduct [memRep @ b, memRep @ b]]

type Tag = Int

data OuterRep = OuterRep [[Tag]] Sum
              deriving (Show)

newtype Sum = Sum [Product]
            deriving (Show)

data Product = Product [Sum]
             | Singleton Int
             deriving (Show)

-- in2out :: InnerRep -> OuterRep
-- in2out (Base x)     = OuterRep [[1]] (Sum [Singleton x])
-- in2out x@(Tagged xxs) = OuterRep (tags x) undefined

-- tags :: InnerRep -> [[Tag]]
-- tags (Base x)     = [[1]]
-- tags (Tagged xss) = [[length xss], tagsr1 xss] ++ tagsrx xss

-- tagsR :: InnerRep -> [[Tag]]
-- tagsR x = case step $ tagsFix x of
--             (t, ts, irs) -> [[t],ts] ++ concatMap tagsR irs

-- stepR :: InnerRep -> [[Tag]]
-- stepR ir = [[fst $ tagsFix ir]] ++ map (concat . stepR) (snd $ tagsFix ir)

tags :: InnerRep -> [[Tag]]
tags = runStepR . prepareStepR

runStepR :: ([[Tag]], [InnerRep]) -> [[Tag]]
runStepR (ts, []) = ts
runStepR x        = runStepR $ stepR x

stepR :: ([[Tag]], [InnerRep]) -> ([[Tag]], [InnerRep])
stepR (ts, irs) = (ts ++ [map (fst . tagsFix) irs], concatMap (snd . tagsFix) irs)

prepareStepR :: InnerRep -> ([[Tag]], [InnerRep])
prepareStepR x = case tagsFix x of (t, irs) -> ([[t]], irs)

step2 :: (Tag, [Tag], [InnerRep]) -> (Tag, [Tag], [Tag], [InnerRep])
step2 (t, ts, irs) = (t, ts, map (fst . tagsFix) irs, concatMap (snd . tagsFix) irs)

step :: (Tag, [InnerRep]) -> (Tag, [Tag], [InnerRep])
step (t, rs) = (t, map (fst . tagsFix) rs, concatMap (snd . tagsFix) rs)

tagsFix :: InnerRep -> (Tag, [InnerRep])
tagsFix (Base x)               = (0, [])
tagsFix (Tagged xss)           = (length xss, concatMap unIP xss)

data Store = Value Int
           | Tag Int
           deriving (Show, Eq)

flatten :: InnerRep -> [[Store]]
flatten (Base x)     = [[Value x]]
flatten (Tagged xss) = map (\xs -> getTag xss : xs) $ concatMap flatten' xss

flatten' :: IProduct -> [[Store]]
flatten' (IProduct [])     = [[]]
flatten' (IProduct (x:xs)) = cartesianProduct (++) (flatten x) (flatten' (IProduct xs))

getTag :: [IProduct] -> Store
getTag = Tag . length

sortTags :: [[Store]] -> [[Store]]
sortTags = map $ sortBy tagOrdering

tagOrdering :: Store -> Store -> Ordering
tagOrdering (Tag _) (Value _) = LT
tagOrdering (Value _) (Tag _) = GT
tagOrdering _         _       = EQ

splitTags :: [[Store]] -> [([Store], [Store])]
splitTags = map splitTags'

splitTags' :: [Store] -> ([Store], [Store])
splitTags' []           = ([],[])
splitTags' (Tag x : xs) = case splitTags' xs of
                           (ys, zs) -> (Tag x:ys, zs)
splitTags' xs           = ([], xs)

allign :: [([Store], [Store])] -> ([[Store]],[[Store]])
allign xs = (allign' fst xs, allign' snd xs)
          where
            allign' f = map nub . transpose . map f

data Opts = Fst
          | Snd
          | Trd

instance MemRep Opts where
  memRep = Tagged [IProduct [], IProduct [], IProduct []]

instance MemRep Float where
  memRep = Base 32

allignment :: InnerRep -> ([[Store]],[[Store]])
allignment = allign . splitTags . sortTags . flatten

sizeOf :: ([[Store]], [[Store]]) -> Int
sizeOf (ts, ds) = sizeOf' (\(Tag x) -> log2 x) ts + sizeOf' (\(Value x) -> x) ds

sizeOf' :: (Store -> Int) -> [[Store]] -> Int
sizeOf' f xs = sum (map (maximum . map f) xs)

---

somethingSOP :: SOP I '[ '[Bool], '[Int]] -- kind [[*]]
somethingSOP = SOP (S (Z (I 3 :* Nil)))

somethingSOP2 :: SOP I '[ '[Bool], '[Int]]
somethingSOP2 = SOP (Z (I True :* Nil))

somethingPOP :: POP I '[ '[Bool], '[Int]]
somethingPOP = POP ((I True :* Nil) :* (I 1 :* Nil) :* Nil)

fromE :: NS (NP I) '[ '[Either Int Int], '[Either Int Int]]
fromE = unSOP $ from (Right (Left 1))

nogiets :: SOP (NS (NP I)) (x : '[ '[Integer] : xs1] : xs2)
nogiets = SOP (S (Z (Z (I 1 :* Nil) :* Nil)))

-- TODO: map from (Right (Left 1)) to nogiets

mapping :: SOP I '[ '[Either Int Int], '[Either Int Int]] -> a
mapping x = undefined $ unSOP x

-- useful crap: index_NS: get the index of the constructor

class MemVal a where
  choices :: a -> [Int]

instance MemVal Int16 where
  choices = const []


instance MemVal Int where
  choices = const []

instance (MemVal l, MemVal r) => MemVal (Either l r) where
  choices = gchoices

-- This definition could be better:
-- - Define singleton sums with an empty list
-- - Define a default for base types (`[]`)
-- - Types should restrict list length and tag indices
gchoices :: (Generic a, All2 MemVal (Code a)) => a -> [Int]
gchoices x = index_NS (unSOP $ from x) : gchoices' x

gchoices' :: (Generic a, All2 MemVal (Code a)) => a -> [Int]
gchoices' x = concat $ hcollapse $ hcliftA pMemVal (K . choices . unI) $ from x

pMemVal :: Proxy MemVal
pMemVal = Proxy

class NFData a where
  rnf :: a -> [Int]

instance NFData [[Int]] where
  rnf = map sum

grnf :: (Generic a, All2 NFData (Code a)) => a -> [Int]
grnf = rnf . hcollapse . hcliftA p (K . rnf . unI) . from

p :: Proxy NFData
p = Proxy

-- data Nat = Zero
--          | Succ Nat

-- data Max m where
--   Max :: forall n m . (KnownNat n, n < m)

-- ttwo :: Succ (Succ Zero)
-- ttwo = Succ (Succ Zero)

-- type level list of naturals:
-- ('Succ 'Zero) ': ('Succ ('Succ 'Zero)) ': '[] :: [Nat]

-- difference :: forall n m. (KnownNat n,KnownNat m,n <= m)
--            => Proxy n
--            -> Proxy m
--            -> Integer
-- difference pn pm = natVal pm - natVal pn

data Vector n a where
  VNil :: Vector 0 a
  VCons :: a -> Vector n a -> Vector (1 + n) a

instance Show a => Show (Vector n a) where
  show VNil = "[]"
  show (VCons x xs) = show x ++ " : " ++ show xs

class TypedMemVal x where
  type Length x :: Nat
  -- Int should be a restricted type Max that restricts the tag choice
  -- to the corresponding constructors
  -- This type should also have a Bottom value to represent nonchoice
  typedChoices :: x -> Vector (Length x) Int

instance TypedMemVal Int where
  type Length Int = 0
  typedChoices _ = VNil

instance TypedMemVal (Either Int Int) where
  type Length (Either Int Int) = 1
  typedChoices (Right r) = VCons 0 (typedChoices r)
  typedChoices (Left l)  = VCons 1 (typedChoices l)

instance TypedMemVal (Either (Either Int Int) (Either Int Int)) where
  -- should be something like 1 + max (l r)
  -- but that might not be a lot of fun on the type level
  type Length (Either (Either Int Int) (Either Int Int)) = 2
  typedChoices (Right r) = VCons 0 (typedChoices r)
  typedChoices (Left l)  = VCons 1 (typedChoices l)

instance TypedMemVal (Maybe Int) where
  type Length (Maybe Int) = 1
  typedChoices Nothing  = VCons 0 VNil
  typedChoices (Just x) = VCons 1 VNil

instance TypedMemVal (Maybe (Maybe Int)) where
  type Length (Maybe (Maybe Int)) = 2
  typedChoices Nothing  = VCons 0 (VCons 0 VNil)
  typedChoices (Just x) = VCons 1 (typedChoices x)
