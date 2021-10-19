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
{-# LANGUAGE UndecidableInstances #-}


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
import GHC.TypeLits.Extra

import Data.Finite.Internal
-- import Fcf.Core (Eval)
-- import Fcf.Data.List (ZipWith)
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

-- Length-indexed homegeneous lists
data Array n a where
  ANil :: Array 0 a
  ACons :: a -> Array n a -> Array (1 + n) a

-- Length-indexed heterogeneous lists
data Vector n where
  VNil :: Vector 0
  VCons :: a -> Vector n -> Vector (1 + n)

instance Show a => Show (Array n a) where
  show ANil = "[]"
  show (ACons x xs) = show x ++ " : " ++ show xs

instance Show (Vector n) where
  show VNil = "[]"
  show (VCons x xs) = "somevalue" ++ " : " ++ show xs

class TypedMemVal x where
  type Length x :: Nat
  -- Int should be a restricted type Max that restricts the tag choice
  -- to the corresponding constructors
  -- This type should also have a Bottom value to represent nonchoice
  typedChoices :: x -> Array (Length x) Int

  type FieldLength x :: Nat
  -- This is even more beautiful: every value in the Array
  -- should have a seperate type that denotes the possible values,
  -- including bottom (if that is possible for the field)
  -- Values can have different bitlenghts too, so its gonna
  -- take some deep magic to perform this act
  fields :: x -> Vector (FieldLength x)

instance TypedMemVal Int where
  type Length Int = 0
  typedChoices _ = ANil
  type FieldLength Int = 1
  fields x = VCons x VNil

instance TypedMemVal (Either Int Int) where
  type Length (Either Int Int) = 1
  typedChoices (Right r) = ACons 0 (typedChoices r)
  typedChoices (Left l)  = ACons 1 (typedChoices l)
  type FieldLength (Either Int Int) = 1
  fields (Right x) = VCons x VNil
  fields (Left x)  = VCons x VNil

instance TypedMemVal (Either (Either Int Int) (Either Int Int)) where
  -- should be something like 1 + max (typedChoices l) (typedChoices r)
  -- but that might not be a lot of fun on the type level
  -- see: https://hackage.haskell.org/package/ghc-typelits-extra for a max type
  -- This package also has a ceil+log operation that might be the typelevel equivalent to our log2 function
  -- See https://hackage.haskell.org/package/first-class-families-0.8.0.1/docs/Fcf.html
  -- for the needed typelevel operations to actually create such a list of type-dependend length.
  type Length (Either (Either Int Int) (Either Int Int)) = 2
  typedChoices (Right r) = ACons 0 (typedChoices r)
  typedChoices (Left l)  = ACons 1 (typedChoices l)
  type FieldLength (Either (Either Int Int) (Either Int Int)) = 1
  fields (Right x) = fields x
  fields (Left x)  = fields x

instance TypedMemVal (Maybe Int) where
  type Length (Maybe Int) = 1
  typedChoices Nothing  = ACons 0 ANil
  typedChoices (Just x) = ACons 1 ANil
  type FieldLength (Maybe Int) = 1
  fields (Just x) = VCons x VNil
  fields Nothing  = VCons 0 VNil -- should be bottom value

instance TypedMemVal (Maybe (Maybe Int)) where
  type Length (Maybe (Maybe Int)) = 2
  typedChoices Nothing  = ACons 0 (ACons 0 ANil)
  typedChoices (Just x) = ACons 1 (typedChoices x)
  type FieldLength (Maybe (Maybe Int)) = 1
  fields (Just x) = fields x
  fields Nothing  = VCons 0 VNil -- should be bottom value

-- we might need something like https://hackage.haskell.org/package/finite-typelits-0.1.4.2/docs/Data-Finite-Internal.html
-- to do finite values

-- data Tagged where
--   Bottom :: Nat -> Tagged
--   Choice :: (n ~ Nat, m ~ Nat, n <= m) => n -> m -> Tagged

-- data family Tagged :: Nat -> Type

-- data instance (Tagged 0) where
--   Bottom :: Tagged 0
--   Choice :: (KnownNat n, n <= m) => n -> Tagged 0

instance TypedMemVal (Int, Int) where
  type Length (Int, Int) = 0
  -- Should be:
  -- type Length (a, b) = Length a + Length b
  -- Need to write a ++ instance for Array to get this to work
  -- I haven't found an implementation for this on Hackage (yet)
  -- typedChoices (a, b) = typedChoices a ++ typedChoices b
  typedChoices _ = ANil
  type FieldLength (Int, Int) = 2
  fields (x,y) = VCons x (VCons y VNil)

-- finite integers be like:
x :: Finite 5
x = 4

-- Length-indexed heterogeneous lists with explicit types
data RVector xs where
  RVNil :: RVector '[]
  RVCons :: x -> RVector xs -> RVector (x ': xs)

instance (All Show xs) =>  Show (RVector xs) where
  show RVNil = "[]"
  show (RVCons a as) = show a ++ ":" ++ show as

-- Length-indexed heterogeneous lists with explicit types, constrained to `Finite`s
-- Has no inhabitants because `Finite :: Nat -> *` instead of `Nat -> Finite Nat`
data FVector n xs where
  FVNil :: FVector 0 '[]
  FVCons :: Finite a -> FVector n xs -> FVector (1 + n) (Finite a ': xs)

class MoreTypedMemVal x where
  type MTFieldTypes x :: [*]
  -- RVector should capture the actual types of the fields
  -- This is severely complicated by the fact that in a sum
  -- each branch can have different types of fields
  -- We need a typelevel sum to express this (probably)
  mtfields :: x -> RVector (MTFieldTypes x)

instance MoreTypedMemVal Int where
  type MTFieldTypes Int = '[Int]
  mtfields x = RVCons x RVNil

instance MoreTypedMemVal (Either Int Int) where
  type MTFieldTypes (Either Int Int) = '[Int]
  mtfields (Right x) = RVCons x RVNil
  mtfields (Left x)  = RVCons x RVNil

instance MoreTypedMemVal Float where
  type MTFieldTypes Float = '[Float]
  mtfields x = RVCons x RVNil

instance MoreTypedMemVal (Either Float Int) where
  type MTFieldTypes (Either Float Int) = '[RNS (Float : Int : '[])]
  mtfields (Left x)  = RVCons (RZ x) RVNil
  mtfields (Right x) = RVCons (RS $ RZ x) RVNil

instance MoreTypedMemVal (Either Int Float) where
  type MTFieldTypes (Either Int Float) = '[RNS (Int : Float : '[])]
  mtfields (Left x)  = RVCons (RZ x) RVNil
  mtfields (Right x) = RVCons (RS $ RZ x) RVNil

instance MoreTypedMemVal (Either (Either Float Int) (Either Float Int)) where
  type MTFieldTypes (Either (Either Float Int) (Either Float Int)) = '[RNS (Float : Int : '[])]
  mtfields (Right x) = mtfields x
  mtfields (Left x)  = mtfields x

instance MoreTypedMemVal (Either (Either Float Int) (Either Int Int)) where
  type MTFieldTypes (Either (Either Float Int) (Either Int Int)) = '[RNS (Float : Int : '[])]
  mtfields (Left x)  = mtfields x
  mtfields (Right x) = case mtfields x of
                        RVCons x' rv -> RVCons (RS $ RZ x') rv

-- instance (MoreTypedMemVal l, MoreTypedMemVal r) => MoreTypedMemVal (Either l r) where
  -- The dream: generically, recursively calculating fieldtypes
  -- The problem: I'm unsure what the type here should be (but we have examples) and
  -- we don't have the operators yet to construct the type.
  -- We probably have to make a set of such operators, but lets first find out what we
  -- need exactly
  -- type MTFieldTypes (Either l r) = MTFieldTypes l ++ MTFieldTypes r
  -- mtfields (Right x) = mtfields x
  -- mtfields (Left x)  = mtfields x

instance MoreTypedMemVal (Either (Either Float Int) (Either Int Float)) where
  type MTFieldTypes (Either (Either Float Int) (Either Int Float)) = '[RNS (Float : Int : Int : Float : '[])]
  mtfields (Left x)  = case mtfields x of
                        -- patterns are actually complete
                        -- types are not strong enough here to discover
                        -- mtfields x is actually of the correct type
                        RVCons x' rv -> case x' of
                          RZ x'' -> RVCons (RZ x'') rv
                          RS (RZ x'') -> RVCons (RS $ RZ x'') rv
  mtfields (Right x) = case mtfields x of
                        -- type system doesn't understand that
                        -- RVCons x' rv -> RVCons (RS $ RS $ x') rv
                        -- would be enough
                        RVCons x' rv -> case x' of
                          RZ x'' -> RVCons (RS $ RS $ RZ x'') rv
                          RS (RZ x'') -> RVCons (RS $ RS $ RS $ RZ x'') rv

instance MoreTypedMemVal (Int, Float) where
  type MTFieldTypes (Int, Float) = '[Int, Float]
  mtfields (x,y) = RVCons x (RVCons y RVNil)

instance MoreTypedMemVal (Either Int Float, Float) where
  type MTFieldTypes (Either Int Float, Float) = '[RNS '[Int, Float], Float]
  mtfields (x,y) = case mtfields x of
    RVCons x' rv -> RVCons x' (RVCons y RVNil)

instance MoreTypedMemVal (Either (Int, Float) Float) where
  type MTFieldTypes (Either (Int, Float) Float) = '[RNS '[Int, Float], RNS '[Float]]
  mtfields (Left x) = case mtfields x of
    RVCons x' (RVCons y RVNil) -> RVCons (RZ x') (RVCons (RZ y) RVNil)
  mtfields (Right x) = case mtfields x of
    RVCons x' RVNil -> RVCons (RS $ RZ x') (RVCons Bottom RVNil)

instance MoreTypedMemVal (Either (Int, Float) Float, Float) where
  type MTFieldTypes (Either (Int, Float) Float, Float) = '[RNS '[Int, Float], RNS '[Float], RNS '[Float]]
  mtfields (x,y) = case (mtfields x, mtfields y) of
    (RVCons x' (RVCons x'' RVNil), RVCons y' RVNil) -> RVCons x' (RVCons x'' (RVCons (RZ y') RVNil))

data RNS :: [*] -> Type where
  RZ :: x -> RNS (x ': xs)
  RS :: RNS xs -> RNS (x ': xs)
  Bottom :: RNS xs
