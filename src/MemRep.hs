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

module MemRep (Product(..), Sum(..), MemRep(..), Finite, Remainder(..)) where

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
      from, unI, K (K), POP, Proxy (Proxy), mapIK, unSOP, Top, SListI, unPOP )
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
data Product xs where
  Nil :: Product '[]
  Cons :: (x ~ Sum a) => x -> Product ys -> Product (x ': ys)

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

-- unused tryout to create a non higher-order ZipWith'
-- we probably need injective type families here: https://gitlab.haskell.org/ghc/ghc/-/wikis/injective-type-families
type family ZipSums (as :: [a]) (bs :: [b]) :: [c] where
  ZipSums '[]        bs       = bs
  ZipSums as        '[]       = as
  ZipSums (a ': as) (b ': bs) = a </> b ': ZipSums as bs

-- Type level append of Sum's
-- We might want to use the correct operator here, but for now this works well enough
type family (a :: *) </> (b :: *) :: * where
  Sum a </> Sum b = Sum (Eval (a ++ b))

data (<>) :: * -> * -> Exp *

type instance Eval ((<>) x y) = x </> y

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

-----------------------------------------------------------------------
-- MemRep, the king of this file
class MemRep x where
  type Choices x :: [*]
  type Choices x = GChoices (SOP I (Code x))

  choices :: x -> Product (Choices x)

  default choices ::
    ( Generic x
    , Choices x ~ GChoices (SOP I (Code x))
    , GMemRep (SOP I (Code x))
    ) => x -> Product (Choices x)
  choices x = gchoices $ from x

  type Fields x :: [*]
  type Fields x = GFields (SOP I (Code x))

  fields :: x -> Product (Fields x)

  default fields ::
    ( Generic x
    , Fields x ~ GFields (SOP I (Code x))
    , GMemRep (SOP I (Code x))
    ) => x -> Product (Fields x)
  fields x = gfields $ from x

  widths :: [Int]

  emptyChoices :: Product (Choices x)

  default emptyChoices ::
    ( GMemRep (SOP I (Code x))
    , Choices x ~ GChoices (SOP I (Code x))
    ) => Product (Choices x)
  emptyChoices = gemptyChoices @ (SOP I (Code x))

  emptyFields :: Product (Fields x)

  default emptyFields ::
    ( GMemRep (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => Product (Fields x)
  emptyFields  = gemptyFields @ (SOP I (Code x))

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

  type Fields Int = '[Sum '[Int]]
  fields x = Cons (Pick x Zero) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance MemRep Float where
  type Choices Float = '[]
  choices _ = Nil

  type Fields Float = '[Sum '[Float]]
  fields x = Cons (Pick x Zero) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance MemRep Int8 where
  type Choices Int8 = '[]
  choices _ = Nil

  type Fields Int8 = '[Sum '[Int8]]
  fields x = Cons (Pick x Zero) Nil

  widths = [8]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance MemRep Int16 where
  type Choices Int16 = '[]
  choices _ = Nil

  type Fields Int16 = '[Sum '[Int16]]
  fields x = Cons (Pick x Zero) Nil

  widths = [16]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

--------------------------------------------------------------
-- Generics

-----------------------------------------------------------------------
-- GMemRep, the serf of this file
class GMemRep x where
  type GChoices x :: [*]
  gchoices :: x -> Product (GChoices x)

  type GFields x :: [*]
  gfields :: x -> Product (GFields x)

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
sopMap :: (All2 MemRep xs) => SOP I xs -> SOP Product (Eval (Map (Map AppChoices) xs))
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
-- sopHap' :: (All SListI xss, All2 MemRep xss) => SOP I xss -> SOP (Product <*> Choices <*> Pure) xss
-- sopHap' = mapSOP apChoices

-- Expected type: NP I x -> NP (Eval (AppProduct (Map AppChoices))) x
-- Actual type:   NP I x -> NP Product (Eval     (Map AppChoices    x))

-- something :: (All Top xss) => (All2 MemRep xss) => SOP I xss -> SOP I (Product (AppChoices x))
-- something = mapNS npMap'

-- npMap' :: (All MemRep xs) => NP I xs -> NP (Eval (AppProduct (Map AppChoices))) xs
-- npMap' SOP.Nil   = SOP.Nil
-- npMap' (x :* xs) = choices' (unI x) :* npMap' xs

-- choices' :: Product (Eval (Map (Map AppChoices) x))
-- choices' = undefined

-- p ~ (NP f a -> g a)
mapNS :: (All Top xss) => forall f g . (forall x . NP f x -> NP g x) -> SOP f xss -> SOP g xss
mapNS f = SOP . liftA_NS f . unSOP

npMap :: (All MemRep xs) => NP I xs -> NP Product (Eval (Map AppChoices xs))
npMap SOP.Nil   = SOP.Nil
npMap (x :* xs) = choices (unI x) :* npMap xs

apChoices :: (MemRep a) => I a -> Product (Choices a)
apChoices = choices . unI

mapSOP :: All SListI xss => (forall (a :: k). f a -> g a) -> SOP f xss -> SOP g xss
mapSOP = liftA_SOP

npFold :: Product ys -> NP Product xs -> Product (Eval (Foldl (++) ys xs))
npFold acc SOP.Nil   = acc
npFold acc (x :* xs) = npFold (rvconcat acc x) xs

npMapF :: (All MemRep xs) => NP I xs -> NP Product (Eval (Map AppFields xs))
npMapF SOP.Nil   = SOP.Nil
npMapF (x :* xs) = fields (unI x) :* npMapF xs

-- generic instance for sums, incompete implementation
-- instance (All MemRep a, All MemRep b, All2 MemRep cs) => GMemRep (SOP I (a ': b ': cs)) where
--   type GChoices (SOP I (a ': b ': cs)) =  Sum '[Finite (Length (a ': b ': cs))] ': Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) (a ': b ': cs))))))
--   gchoices (SOP xs) = Cons (Pick (finite $ toInteger $ index_NS xs) Zero) undefined

--   type GFields (SOP I (a ': b ': cs)) = Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) (a ': b ': cs))))))
--   gfields (SOP xs) = undefined

--   gemptyChoices = undefined
--   gemptyFields = undefined

-- generic instance for binary sums
instance
    ( All MemRep l
    , All MemRep r
    ) => GMemRep (SOP I '[ l, r]) where
  type GChoices (SOP I '[ l, r]) =  Sum '[Finite 2] ': Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) '[ l, r])))))
  gchoices (SOP (Z ls))     = Cons (Pick 0 Zero) (zipSum (npFold Nil (npMap ls)) (npFold Nil (convertPureChoices (pureChoices :: NP PC r))))
  gchoices (SOP (S (Z rs))) = Cons (Pick 1 Zero) (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (npMap rs)))
  gchoices (SOP (S (S _))) = error "this is not even possible"

  type GFields (SOP I '[ l, r]) = Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ l, r])))))
  gfields (SOP (Z ls))     = zipSum (npFold Nil (npMapF ls)) (npFold Nil (convertPureFields (pureFields :: NP PF r)))
  gfields (SOP (S (Z rs))) = zipSum (npFold Nil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (npMapF rs))
  gfields (SOP (S (S _))) = error "this is not even possible"

  gemptyChoices = Cons (Skip Empty) (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (convertPureChoices (pureChoices :: NP PC r))))
  gemptyFields = zipSum (npFold Nil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (convertPureFields (pureFields :: NP PF r)))

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
instance (All MemRep as) => GMemRep (SOP I '[as]) where
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

pureChoices :: (All MemRep xs) => NP PC xs
pureChoices = cpure_NP (Proxy :: Proxy MemRep) emptyChoices'

emptyChoices' :: forall x . (MemRep x) => PC x
emptyChoices' = PC $ emptyChoices @ x

newtype PF a = PF (Product (Fields a))

unPF :: PF a -> Product (Fields a)
unPF (PF x) = x

convertPureFields :: NP PF xs -> NP Product (Eval (Map AppFields xs))
convertPureFields SOP.Nil   = SOP.Nil
convertPureFields (x :* xs) = unPF x :* convertPureFields xs

pureFields :: (All MemRep xs) => NP PF xs
pureFields = cpure_NP (Proxy :: Proxy MemRep) emptyFields'

emptyFields' :: forall x . (MemRep x) => PF x
emptyFields' = PF $ emptyFields @ x

-- unused random stuff
xinner :: forall k (f :: k -> *) (xss :: [[k]]). POP f xss -> NP (NP f) xss
xinner = unPOP

try :: (All2 MemRep xss) => POP PC xss
try = cpure_POP (Proxy :: Proxy MemRep) emptyChoices'

-----------------------------------------------------------------------
-- Instances for some made up datatypes
data Try a b = Som a | Oth b
             deriving (GHC.Generic, Generic, MemRep)

data Tuple a b = T a b
               deriving (GHC.Generic, Generic, MemRep)

data Tuple5 a b c d e = T5 a b c d e
                      deriving (GHC.Generic, Generic, MemRep)

data Unit = Unit
          deriving (GHC.Generic, Generic, MemRep)

data MultiSum x y = First x y
                  | Second y x
                  deriving (GHC.Generic, Generic, MemRep)

-----------------------------------------------------------------------
-- Instances for common Haskell datatypes
deriving instance MemRep Bool
deriving instance MemRep x => MemRep (Maybe x)
deriving instance (MemRep l, MemRep r) => MemRep (Either l r)
deriving instance MemRep ()
deriving instance (MemRep a, MemRep b) => MemRep (a,b)
