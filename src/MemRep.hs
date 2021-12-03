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
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# LANGUAGE StandaloneDeriving #-}

module MemRep (Product(..), Sum(..), Elt(..), Finite, Remainder(..)) where

import Generics.SOP
    ( All,
      All2,
      Code,
      Generic,
      All,
      All2,
      Code,
      Generic,
      I,
      SOP(SOP),
      NS(Z, S),
      NP((:*)),
      from,
      unI,
      K(K),
      POP,
      Proxy(Proxy),
      mapIK,
      unSOP,
      Top,
      SListI,
      unPOP,
      to )
import Data.Int (Int8, Int16)
import Data.Finite.Internal (Finite)

import Fcf ( Eval, Exp, type (++), Map)

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP

import Data.Kind ()
import Generics.SOP.NP (cpure_POP, cpure_NP)

import GHC.Base (Nat)
import GHC.TypeLits (type (+))
import Generics.SOP.NS (expand_SOP, liftA_NS, liftA_SOP)

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types
data Product :: [*] -> * where
  Nil :: Product '[]
  Cons :: (x ~ Sum a) => x -> Product xs -> Product (x ': xs)

deriving instance (All Eq xs) => Eq (Product xs)

instance (All Show xs) =>  Show (Product xs) where
  show Nil = "[]"
  show (Cons a as) = show a ++ " : " ++ show as

-- concat for Products
-- could (should) be a Semigroup instance (<>)
rvconcat :: Product x -> Product y -> Product (Eval (x ++ y))
rvconcat Nil         ys = ys
rvconcat (Cons x xs) ys = Cons x (rvconcat xs ys)

-- wrap Product in an Exp to use it as an argument to higher order type functions
data AppProduct :: x -> Exp y

type instance Eval (AppProduct x) = Product x

-----------------------------------------------------------------------
-- Typelevel sums with a empty value
data Sum :: [*] -> * where
  Pick :: x -> Remainder xs -> Sum (x ': xs)
  Skip :: Sum xs -> Sum (x ': xs)
  Empty :: Sum '[]

deriving instance (All Eq xs) => Eq (Sum xs)

-- the remainder makes it possible to known the length of the sum at runtime
data Remainder :: [*] -> * where
  Succ :: Remainder xs -> Remainder (x ': xs)
  Zero  :: Remainder '[]

deriving instance Eq (Remainder xs)

instance (All Show x) => Show (Sum x) where
  show (Pick x _) = show x
  show (Skip x)   = show x
  show Empty      = "Ø"

-----------------------------------------------------------------------
-- Functions on Products and Sums

-- stolen from https://hackage.haskell.org/package/first-class-families-0.8.0.1
-- and adapted to keep the length of the longest list
--
-- | Combine elements of two lists pairwise.
--
-- === __Example__
--
-- >>> :kind! Eval (ZipWith' (+) '[1,2,3] '[1,1])
-- Eval (ZipWith' (+) '[1,2,3] '[1,1]) :: [Nat]
-- = '[2, 3, 3]
data ZipWith' :: (a -> b -> Exp c) -> [a] -> [b] -> Exp [c]

type instance Eval (ZipWith' _f '[] _bs) = _bs
type instance Eval (ZipWith' _f _as '[]) = _as
type instance Eval (ZipWith' f (a ': as) (b ': bs)) =
  Eval (f a b) ': Eval (ZipWith' f as bs)

-- type instance Eval (ZipWithNew _f '[] _bs) = _bs
-- type instance Eval (ZipWithNew _f _as '[]) = _as
-- type instance Eval (ZipWithNew f (a ': as) (b ': bs)) =
--   Eval (f a b) ': Eval (ZipWithNew f as bs)

data (<>) :: * -> * -> Exp *

type instance Eval ((<>) (Sum x) (Sum y)) = Sum (Eval (x ++ y))

-- value level implementation of ZipWith' (<>)
-- takes the leftmost Pick that is encountered for each element of the Product
zipSum :: Product l -> Product r -> Product (Eval (ZipWith' (<>) l r))
zipSum (Cons (x :: Sum a) xs) (Cons (y :: b) ys) = Cons (takeS x y) (zipSum xs ys)
zipSum Nil ys = ys
zipSum xs Nil = xs

-- return leftmost Pick or Empty if no Pick is found
takeS :: Sum l -> Sum r -> Sum (Eval (l ++ r))
takeS (Pick l ls) r = Pick l (takeS' ls r)
takeS (Skip ls)   r = Skip (takeS ls r)
takeS Empty       r = r

takeS' :: Remainder l -> Sum r -> Remainder (Eval (l ++ r))
takeS' (Succ ls) r           = Succ (takeS' ls r)
takeS' Zero      Empty       = Zero
takeS' Zero      (Skip rs)   = Succ (takeS' Zero rs)
takeS' Zero      (Pick _ rs) = Succ (takeS'' Zero rs)

takeS'' :: Remainder l -> Remainder r -> Remainder (Eval (l ++ r))
takeS'' (Succ ls) r = Succ (takeS'' ls r)
takeS'' Zero      r = r


--------------------------------------------------------------
-- Functions to deal with splitting values back into existence
--
-- Includes an ungodly amount of boilerplate
--

splitLeft :: Product (Eval (l ++ r)) -> Product l -> Product r -> Product l
splitLeft (Cons x xs) (Cons _ ls) rs = Cons x (splitLeft xs ls rs)
splitLeft _           Nil         _  = Nil

splitRight :: Product (Eval (l ++ r)) -> Product l -> Product r -> Product r
splitRight (Cons _ xs) (Cons _ ls) rs = splitRight xs ls rs
splitRight x           Nil         _  = x

splitLeftWith :: Product (Eval (ZipWith' (<>) l r)) -> Product l -> Product r -> Product l
splitLeftWith (Cons x xs) (Cons l ls) (Cons r rs) = Cons (splitSumLeft x l r) (splitLeftWith xs ls rs)
splitLeftWith x           _         Nil  = x
splitLeftWith (Cons _ _)  Nil       _    = Nil

splitRightWith :: Product (Eval (ZipWith' (<>) l r)) -> Product l -> Product r -> Product r
splitRightWith (Cons x xs) (Cons l ls) (Cons r rs) = Cons (splitSumRight x l r) (splitRightWith xs ls rs)
splitRightWith x           Nil         _           = x
splitRightWith _           _           Nil         = Nil

-- Start of ugly boilerplate to deal with sums and remainders
splitSumRight :: Sum (Eval (l ++ r)) -> Sum l -> Sum r -> Sum r
splitSumRight x Empty _ = x
splitSumRight (Skip xs) (Skip ls) rs = splitSumRight xs ls rs
splitSumRight (Pick _ xs) (Skip ls) rs = splitSumRight2 xs ls rs
splitSumRight (Skip xs) (Pick _ ls) rs = splitSumRight3 xs ls rs
splitSumRight (Pick _ xs) (Pick _ ls) rs = splitSumRight4 xs ls rs

splitSumRight4 :: Remainder (Eval (l ++ r)) -> Remainder l -> Sum r -> Sum r
splitSumRight4 Zero      Zero      _           = Empty
splitSumRight4 (Succ xs) Zero      (Skip rs)   = Skip (splitSumRight4 xs Zero rs)
splitSumRight4 (Succ xs) Zero      (Pick _ rs) = Skip (splitSumRight5 xs Zero rs)
splitSumRight4 (Succ xs) (Succ ls) rs          = splitSumRight4 xs ls rs

splitSumRight5 :: Remainder (Eval (l ++ r)) -> Remainder l -> Remainder r -> Sum r
splitSumRight5 _ _ Zero = Empty
splitSumRight5 (Succ xs) Zero (Succ rs) = Skip (splitSumRight5 xs Zero rs)
splitSumRight5 (Succ xs) (Succ ls) rs = splitSumRight5 xs ls rs

splitSumRight3 :: Sum (Eval (l ++ r)) -> Remainder l -> Sum r -> Sum r
splitSumRight3 x           Zero      _     = x
splitSumRight3 _           _         Empty = Empty
splitSumRight3 (Pick _ xs) (Succ ls) rs    = splitSumRight4 xs ls rs
splitSumRight3 (Skip   xs) (Succ ls) rs    = splitSumRight3 xs ls rs

splitSumRight2 :: Remainder (Eval (l ++ r)) -> Sum l -> Sum r -> Sum r
splitSumRight2 _ _ Empty = Empty
splitSumRight2 (Succ xs) Empty (Skip rs) = Skip (splitSumRight2 xs Empty rs)
splitSumRight2 (Succ xs) Empty (Pick _ rs) = Skip (splitSumRight6 xs Empty rs)
splitSumRight2 (Succ xs) (Skip ls) rs = splitSumRight2 xs ls rs
splitSumRight2 (Succ xs) (Pick _ ls) rs = splitSumRight4 xs ls rs

splitSumRight6 :: Remainder (Eval (l ++ r)) -> Sum l -> Remainder r -> Sum r
splitSumRight6 (Succ xs) Empty (Succ rs) = Skip (splitSumRight6 xs Empty rs)
splitSumRight6 Zero      _     Zero      = Empty
splitSumRight6 (Succ xs) (Pick _ ls) rs = splitSumRight5 xs ls rs
splitSumRight6 (Succ xs) (Skip ls)   rs = splitSumRight6 xs ls rs

splitSumLeft :: Sum (Eval (l ++ r)) -> Sum l -> Sum r -> Sum l
splitSumLeft (Pick x xs) (Pick _ ls) rs = Pick x (splitSumLeftR xs ls rs)
splitSumLeft (Pick x xs) (Skip   ls) rs = Pick x (splitSumLeftR2 xs ls rs)
splitSumLeft (Skip   xs) (Pick _ ls) rs = Skip (splitSumLeftR4 xs ls rs)
splitSumLeft (Skip   xs) (Skip   ls) rs = Skip (splitSumLeft xs ls rs)
splitSumLeft _           Empty       _  = Empty

splitSumLeftR4 :: Sum (Eval (l ++ r)) -> Remainder l -> Sum r -> Sum l
splitSumLeftR4 _           Zero      _  = Empty
splitSumLeftR4 (Pick x xs) (Succ ls) rs = Pick x (splitSumLeftR3 xs ls rs)
splitSumLeftR4 (Skip   xs) (Succ ls) rs = Skip (splitSumLeftR4 xs ls rs)

splitSumLeftR :: Remainder (Eval (l ++ r)) -> Remainder l -> Sum r -> Remainder l
splitSumLeftR (Succ xs) (Succ ls) rs = Succ (splitSumLeftR xs ls rs)
splitSumLeftR _          Zero     _ = Zero

splitSumLeftR2 :: Remainder (Eval (l ++ r)) -> Sum l -> Sum r -> Remainder l
splitSumLeftR2 (Succ xs) (Pick _ ls) rs = Succ (splitSumLeftR3 xs ls rs)
splitSumLeftR2 _         Empty       _  = Zero
splitSumLeftR2 (Succ xs) (Skip ls)   rs = Succ (splitSumLeftR2 xs ls rs)

splitSumLeftR3 :: Remainder (Eval (l ++ r)) -> Remainder l -> Sum r -> Remainder l
splitSumLeftR3 (Succ xs) (Succ ls) rs = Succ (splitSumLeftR3 xs ls rs)
splitSumLeftR3 _         Zero     _ = Zero
-- End of ugly boilerplate to deal with sums and remainders

-----------------------------------------------------------------------
-- Elt, the king of this file
class Elt x where
  type Choices x :: [*]
  type Choices x = GChoices (SOP I (Code x))

  choices :: x -> Product (Choices x)

  default choices ::
    ( Generic x
    , Choices x ~ GChoices (SOP I (Code x))
    , GElt (SOP I (Code x))
    ) => x -> Product (Choices x)
  choices x = gchoices $ from x

  fromElt :: Product (Choices x) -> Product (Fields x) -> x

  default fromElt ::
    ( Generic x
    , (GElt (SOP I (Code x)))
    , Choices x ~ GChoices (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => Product (Choices x) -> Product (Fields x) -> x
  fromElt cs fs = to $ gfromElt cs fs

  type Fields x :: [*]
  type Fields x = GFields (SOP I (Code x))

  fields :: x -> Product (Fields x)

  default fields ::
    ( Generic x
    , Fields x ~ GFields (SOP I (Code x))
    , GElt (SOP I (Code x))
    ) => x -> Product (Fields x)
  fields x = gfields $ from x

  widths :: [Int]

  emptyChoices :: Product (Choices x)

  default emptyChoices ::
    ( GElt (SOP I (Code x))
    , Choices x ~ GChoices (SOP I (Code x))
    ) => Product (Choices x)
  emptyChoices = gemptyChoices @ (SOP I (Code x))

  emptyFields :: Product (Fields x)

  default emptyFields ::
    ( GElt (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => Product (Fields x)
  emptyFields  = gemptyFields @ (SOP I (Code x))

-----------------------------------------------------------------------
-- Instances of Elt for machine types

-- Sadly, this definition due to overlapping instances:

-- instance Base x => Elt x where
--   type Choices x = '[]
--   choices x = Nil

--   type Fields x = '[Sum '[x]]
--   mtfields x = Cons (Pick x) Nil

-- Instead, we have to do with a seperate definition per base type, which leads
-- to a horrible amount of boilerplate.
-- This is fixable with some Template Haskell, but let's not go there now.
instance Elt Int where
  type Choices Int = '[]
  choices _ = Nil

  type Fields Int = '[Sum '[Int]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance Elt Float where
  type Choices Float = '[]
  choices _ = Nil

  type Fields Float = '[Sum '[Float]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance Elt Int8 where
  type Choices Int8 = '[]
  choices _ = Nil

  type Fields Int8 = '[Sum '[Int8]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [8]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance Elt Int16 where
  type Choices Int16 = '[]
  choices _ = Nil

  type Fields Int16 = '[Sum '[Int16]]
  fields x = Cons (Pick x Zero) Nil

  fromElt Nil (Cons (Pick x Zero) Nil) = x

  widths = [16]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

-- Instance for Either, recursively defined
instance (Elt l, Elt r) => Elt (Either l r) where
  type Choices (Either l r) = Sum '[Finite 2] ': Eval (ZipWith' (<>) (Choices l) (Choices r))
  choices (Left lv)  = Cons (Pick 0 Zero) (zipSum (choices lv) (emptyChoices @ r))
  choices (Right rv) = Cons (Pick 1 Zero) (zipSum (emptyChoices @ l) (choices rv))

  type Fields (Either l r) = Eval (ZipWith' (<>) (Fields l) (Fields r))
  fields (Left lv)  = zipSum (fields lv) (emptyFields @ r)
  fields (Right rv) = zipSum (emptyFields @ l) (fields rv)

  widths = zipWith max (widths @ l) (widths @ r)

  fromElt (Cons (Pick 0 Zero) cs) fs = Left (fromElt lcs lfs)
                                        where
                                          lcs = splitLeftWith cs (emptyChoices @ l) (emptyChoices @ r)
                                          lfs = splitLeftWith fs (emptyFields @ l)  (emptyFields @ r)
  fromElt (Cons (Pick 1 Zero) cs) fs = Right (fromElt rcs rfs)
                                        where
                                          rcs = splitRightWith cs (emptyChoices @ l) (emptyChoices @ r)
                                          rfs = splitRightWith fs (emptyFields @ l) (emptyFields @ r)
  fromElt (Cons _             _)  _  = error "constructor index out of bounds"

  emptyChoices = Cons (Skip Empty) (zipSum (emptyChoices @ l) (emptyChoices @ r))
  emptyFields = zipSum (emptyFields @ l) (emptyFields @ r)


-- instance (Elt a, Elt b) => Elt (Either (a, b) (b, a)) where
--   type Choices (Either (a, b) (b, a)) = Sum '[Finite 2] ': Eval (ZipWith' (<>) (Choices (a, b)) (Choices (b, a)))
--   choices (Left x)  = Cons (Pick 0 Zero) (zipSum (choices x) (emptyChoices @ (b, a)))
--   choices (Right x) = Cons (Pick 1 Zero) (zipSum (emptyChoices @ (a,b)) (choices x))

--   type Fields (Either (a, b) (b, a)) = Fields (a, b)
--   fields (Left  (a,b)) = fields (a,b)
--   fields (Right (b,a)) = fields (a,b)

--   fromElt (Cons (Pick 0 Zero) cs) fs = Left (fromElt cs fs)
--   fromElt (Cons (Pick 1 Zero) cs) fs | (a,b) <- fromElt cs fs = Right (b,a)

  -- widths = [16]

  -- emptyChoices = Nil
  -- emptyFields = Cons (Pick 0 Zero) Nil

-- Instance for product types (tuples)
instance (Elt x, Elt y) => Elt (x, y) where
  type Choices (x,y) = Eval (Choices x ++ Choices y)
  choices (x,y) = rvconcat (choices x) (choices y)

  type Fields (x, y) = Eval (Fields x ++ Fields y)
  fields (x,y) = rvconcat (fields x) (fields y)

  widths = widths @ x ++ widths @ y

  emptyChoices = rvconcat (emptyChoices @ x) (emptyChoices @ y)
  emptyFields = rvconcat (emptyFields @ x) (emptyFields @ y)

  fromElt cs fs = (fromElt xcs xfs, fromElt ycs yfs)
                   where
                     xcs = splitLeft cs (emptyChoices @ x) (emptyChoices @ y)
                     xfs = splitLeft fs (emptyFields @ x) (emptyFields @ y)
                     ycs = splitRight cs (emptyChoices @ x) (emptyChoices @ y)
                     yfs = splitRight fs (emptyFields @ x) (emptyFields @ y)

--------------------------------------------------------------
-- Generics

-----------------------------------------------------------------------
-- GElt, the serf of this file
class GElt x where
  type GChoices x :: [*]
  gchoices :: x -> Product (GChoices x)

  type GFields x :: [*]
  gfields :: x -> Product (GFields x)

  gfromElt :: Product (GChoices x) -> Product (GFields x) -> x

  gemptyChoices :: Product (GChoices x)
  gemptyFields :: Product (GFields x)

-----------------------------------------------------------------------
-- Length of typelevel lists

-- adapted Length to lists of lists (sums of products)
type family Length (xs :: [[*]]) :: Nat where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

-- typesafe version of index_NS, implementation doesn't compile yet
-- stolen from https://hackage.haskell.org/package/sop-core-0.5.0.1/docs/src/Data.SOP.Classes.html#hindex
-- indexNS :: forall f xs x . NS f xs -> Finite (Length xs)
-- indexNS = go (0 :: Finite (Length xs))
--   where
--     go :: forall ys x . Finite x -> NS f ys -> Finite x
--     go !acc (Z _) = acc
--     go !acc (S x) = go (acc + 1) x

-----------------------------------------------------------------------
-- Whole bit of tryout code, to be removed
sopMap :: (All2 Elt xs) => SOP I xs -> SOP Product (Eval (Map (Map AppChoices) xs))
sopMap = undefined

-- :t hexpand (K ()) (SOP (S (Z (I 1.0 :* SOP.Nil))))
-- :t hexpand (I ()) (SOP (S (Z (I () :* SOP.Nil))))
-- from https://hackage.haskell.org/package/generics-sop-0.5.1.1/docs/Generics-SOP.html#t:HExpand
-- hexpand [] (SOP (S (Z ([1,2] :* "xyz" :* SOP.Nil)))) :: POP [] '[ '[Bool], '[Int, Char] ]
-- purePOP :: (All SOP.SListI xss) => SOP f xss -> POP f xss
purePOP :: (All SOP.SListI yss) => SOP I yss -> POP (K ()) yss
purePOP x = expand_SOP (K ()) $ sopHap x

sopHap :: (All SOP.SListI xss) => SOP I xss -> SOP (K ()) xss
sopHap = SOP.hliftA (mapIK (const ()))

purePOP' :: (All SOP.SListI yss) => SOP I yss -> POP (K ()) yss
purePOP' x = expand_SOP (K ()) $ sopHap x

-- -- sopHap' :: (All SOP.SListI xss) => SOP I xss -> SOP Product (Eval (Map (Map AppChoices) xss))
-- sopHap' :: (All SListI xss, All2 Elt xss) => SOP I xss -> SOP (Product <*> Choices <*> Pure) xss
-- sopHap' = mapSOP apChoices

-- Expected type: NP I x -> NP (Eval (AppProduct (Map AppChoices))) x
-- Actual type:   NP I x -> NP Product (Eval     (Map AppChoices    x))

-- something :: (All Top xss) => (All2 Elt xss) => SOP I xss -> SOP I (Product (AppChoices x))
-- something = mapNS npMap'

-- npMap' :: (All Elt xs) => NP I xs -> NP (Eval (AppProduct (Map AppChoices))) xs
-- npMap' SOP.Nil   = SOP.Nil
-- npMap' (x :* xs) = choices' (unI x) :* npMap' xs

-- choices' :: Product (Eval (Map (Map AppChoices) x))
-- choices' = undefined

-- p ~ (NP f a -> g a)
mapNS :: (All Top xss) => forall f g . (forall x . NP f x -> NP g x) -> SOP f xss -> SOP g xss
mapNS f = SOP . liftA_NS f . unSOP

npMap :: (All Elt xs) => NP I xs -> NP Product (Eval (Map AppChoices xs))
npMap SOP.Nil   = SOP.Nil
npMap (x :* xs) = choices (unI x) :* npMap xs

apChoices :: (Elt a) => I a -> Product (Choices a)
apChoices = choices . unI

mapSOP :: All SListI xss => (forall (a :: k). f a -> g a) -> SOP f xss -> SOP g xss
mapSOP = liftA_SOP

npFold :: Product ys -> NP Product xs -> Product (Eval (Foldl (++) ys xs))
npFold acc SOP.Nil   = acc
npFold acc (x :* xs) = npFold (rvconcat acc x) xs

npMapF :: (All Elt xs) => NP I xs -> NP Product (Eval (Map AppFields xs))
npMapF SOP.Nil   = SOP.Nil
npMapF (x :* xs) = fields (unI x) :* npMapF xs

-- generic instance for sums, incompete implementation
-- instance (All Elt a, All Elt b, All2 Elt cs) => GElt (SOP I (a ': b ': cs)) where
--   type GChoices (SOP I (a ': b ': cs)) =  Sum '[Finite (Length (a ': b ': cs))] ': Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) (a ': b ': cs))))))
--   gchoices (SOP xs) = Cons (Pick (finite $ toInteger $ index_NS xs) Zero) undefined

--   type GFields (SOP I (a ': b ': cs)) = Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) (a ': b ': cs))))))
--   gfields (SOP xs) = undefined

--   gemptyChoices = undefined
--   gemptyFields = undefined

-- generic instance for binary sums
instance
    ( All Elt l
    , All Elt r
    ) => GElt (SOP I '[ l, r]) where
  type GChoices (SOP I '[ l, r]) =  Sum '[Finite 2] ': Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) '[ l, r])))))
  gchoices (SOP (Z ls))     = Cons (Pick 0 Zero) (zipSum (npFold Nil (npMap ls)) (npFold Nil (convertPureChoices (pureChoices :: NP PC r))))
  gchoices (SOP (S (Z rs))) = Cons (Pick 1 Zero) (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (npMap rs)))
  gchoices (SOP (S (S _))) = error "this is not even possible"

  type GFields (SOP I '[ l, r]) = Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ l, r])))))
  gfields (SOP (Z ls))     = zipSum (npFold Nil (npMapF ls)) (npFold Nil (convertPureFields (pureFields :: NP PF r)))
  gfields (SOP (S (Z rs))) = zipSum (npFold Nil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (npMapF rs))
  gfields (SOP (S (S _))) = error "this is not even possible"

  gemptyChoices = Cons (Pick 0 Zero) (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (convertPureChoices (pureChoices :: NP PC r))))
  gemptyFields = zipSum (npFold Nil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (convertPureFields (pureFields :: NP PF r)))


-- generic instance for ternary sums
instance
    ( All Elt x
    , All Elt y
    , All Elt z
    ) => GElt (SOP I '[ x, y, z]) where
  type GChoices (SOP I '[ x, y, z]) =  Sum '[Finite 3] ': Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) '[ x, y, z])))))
  gchoices (SOP (Z xs))         = Cons (Pick 0 Zero) (zipSum (zipSum (npFold Nil (npMap xs)) (npFold Nil (convertPureChoices (pureChoices :: NP PC y)))) (npFold Nil (convertPureChoices (pureChoices :: NP PC z))))
  gchoices (SOP (S (Z ys)))     = Cons (Pick 1 Zero) (zipSum (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC x))) (npFold Nil (npMap ys))) (npFold Nil (convertPureChoices (pureChoices :: NP PC z))))
  gchoices (SOP (S (S (Z zs)))) = Cons (Pick 2 Zero) (zipSum (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC x))) (npFold Nil (convertPureChoices (pureChoices :: NP PC y)))) (npFold Nil (npMap zs)))
  -- TODO proof that this is not possible
  gchoices (SOP (S (S (S _)))) = error "this is not even possible"

  type GFields (SOP I '[ x, y, z]) = Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ x, y, z])))))
  gfields (SOP (Z xs))         = zipSum (zipSum (npFold Nil (npMapF xs)) (npFold Nil (convertPureFields (pureFields :: NP PF y)))) (npFold Nil (convertPureFields (pureFields :: NP PF z)))
  gfields (SOP (S (Z ys)))     = zipSum (zipSum (npFold Nil (convertPureFields (pureFields :: NP PF x))) (npFold Nil (npMapF ys))) (npFold Nil (convertPureFields (pureFields :: NP PF z)))
  gfields (SOP (S (S (Z zs)))) = zipSum (zipSum (npFold Nil (convertPureFields (pureFields :: NP PF x))) (npFold Nil (convertPureFields (pureFields :: NP PF y)))) (npFold Nil (npMapF zs))
  gfields (SOP (S (S (S _))))  = error "this is not even possible"

  -- gemptyChoices = Cons (Skip Empty) (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (convertPureChoices (pureChoices :: NP PC r))))
  -- gemptyFields = zipSum (npFold Nil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (convertPureFields (pureFields :: NP PF r)))


data AppChoices :: x -> Exp y

type instance Eval (AppChoices x) = Choices x

data AppFields :: x -> Exp y

type instance Eval (AppFields x) = Fields x

-- from https://hackage.haskell.org/package/first-class-families-0.8.0.1/docs/src/Fcf.Class.Foldable.html#Foldr
-- why use this instead of FoldR?
-- because this matches the way Fcf.<> works, so I don't have to prove that it is associative
data Foldl :: (a -> b -> Exp b) -> b -> t a -> Exp b

type instance Eval (Foldl f y '[]) = y
type instance Eval (Foldl f y (x ': xs)) = Eval (Foldl f (Eval (f y x)) xs)

-- generic instance for unary sums (tuples)
instance (All Elt as) => GElt (SOP I '[as]) where
  type GChoices (SOP I '[as]) = Eval (Foldl (++) '[] (Eval (Map AppChoices as)))
  gchoices (SOP (Z xs)) = npFold Nil (npMap xs)
  gchoices (SOP (S _)) = error "this is not even possible"

  type GFields (SOP I '[as]) = Eval (Foldl (++) '[] (Eval (Map AppFields as)))
  gfields (SOP (Z xs)) = npFold Nil (npMapF xs)
  gfields (SOP (S _)) = error "this is not even possible"

  gemptyChoices = npFold Nil (convertPureChoices (pureChoices :: NP PC as))
  gemptyFields = npFold Nil (convertPureFields (pureFields :: NP PF as))


-- foldPop :: NP PC xss -> Product (Eval (Foldl (++) '[] (Eval (Map AppChoices yss))))
-- foldPop x = npFold Nil (npMap xinner)

-- functions to generate pure Choices and Fields
newtype PC a = PC (Product (Choices a))

unPC :: PC a -> Product (Choices a)
unPC (PC x) = x

convertPureChoices :: NP PC xs -> NP Product (Eval (Map AppChoices xs))
convertPureChoices SOP.Nil   = SOP.Nil
convertPureChoices (x :* xs) = unPC x :* convertPureChoices xs

pureChoices :: (All Elt xs) => NP PC xs
pureChoices = cpure_NP (Proxy :: Proxy Elt) emptyChoices'

emptyChoices' :: forall x . (Elt x) => PC x
emptyChoices' = PC $ emptyChoices @ x

newtype PF a = PF (Product (Fields a))

unPF :: PF a -> Product (Fields a)
unPF (PF x) = x

convertPureFields :: NP PF xs -> NP Product (Eval (Map AppFields xs))
convertPureFields SOP.Nil   = SOP.Nil
convertPureFields (x :* xs) = unPF x :* convertPureFields xs

pureFields :: (All Elt xs) => NP PF xs
pureFields = cpure_NP (Proxy :: Proxy Elt) emptyFields'

emptyFields' :: forall x . (Elt x) => PF x
emptyFields' = PF $ emptyFields @ x

-- unused random stuff
xinner :: forall k (f :: k -> *) (xss :: [[k]]). POP f xss -> NP (NP f) xss
xinner = unPOP

try :: (All2 Elt xss) => POP PC xss
try = cpure_POP (Proxy :: Proxy Elt) emptyChoices'

-----------------------------------------------------------------------
-- Instances for some made up datatypes
data Try a b = Som a | Oth b
             deriving (GHC.Generic, Generic, Elt)

data Tuple a b = T a b
               deriving (GHC.Generic, Generic, Elt)

data Tuple5 a b c d e = T5 a b c d e
                      deriving (GHC.Generic, Generic, Elt)

data Unit = Unit
          deriving (GHC.Generic, Generic, Elt)

data MultiSum x y = First x y
                  | Second y x
                  deriving (GHC.Generic, Generic, Elt)

data Direction n e s = North n
                     | East e
                     | South s
                     deriving (GHC.Generic, Generic, Elt)

-----------------------------------------------------------------------
-- Instances for common Haskell datatypes
deriving instance Elt Bool
deriving instance Elt x => Elt (Maybe x)
-- deriving instance (Elt l, Elt r) => Elt (Either l r)
deriving instance Elt ()
-- deriving instance (Elt a, Elt b) => Elt (a,b)
