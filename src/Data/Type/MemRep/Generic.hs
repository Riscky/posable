{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.Type.MemRep.Generic where

import Generics.SOP hiding (Nil)
import Generics.SOP.NP hiding (Nil)
import Data.Finite (Finite, combineProduct, combineSum)
import Data.Type.MemRep.MemRep
import Data.Type.MemRep.Representation

import Data.Kind (Type)

import qualified Generics.SOP as SOP

import GHC.Base (Nat)
import GHC.TypeLits (KnownNat, type (*), type (+))

-- generic instance for n-ary sums (so for everything)
instance
  ( All2 MemRep xss
  , KnownNat (Sums (MapProducts (Map2Choices xss)))
  , All2 KnownNat (Map2Choices xss)
  , All KnownNat (MapProducts (Map2Choices xss))
  ) => GMemRep (SOP I xss) where

  type GChoices (SOP I xss) = Sums (MapProducts (Map2Choices xss))
  gchoices x = sums $ mapProducts $ map2choices $ unSOP x

  type GFields (SOP I xss) = FoldMerge (MapAppends (Map2Fields xss))
  gfields (SOP x)         = foldMerge
                              (mapAppendsT $ (pureMap2Fields @xss))
                              (mapAppends (map2Fields x))
  
  gemptyFields = foldMergeT $ mapAppendsT $ (pureMap2Fields @xss)

--------------------------------------------------------------------------------
-- Supporting types and classes
--------------------------------------------------------------------------------

type family MapChoices (xs :: f x) :: f Nat where
  MapChoices '[] = '[]
  MapChoices (x ': xs) = Choices x ': MapChoices xs


type family Map2Choices (xss :: f (g x)) :: f (g Nat) where
  Map2Choices '[] = '[]
  Map2Choices (xs ': xss) = MapChoices xs ': Map2Choices xss


type family MapFields (xs :: f x) :: f [[Type]] where
  MapFields '[] = '[]
  MapFields (x ': xs) = Fields x ': MapFields xs


type family Map2Fields (xss :: f (g x)) :: f (g [[Type]]) where
  Map2Fields '[] = '[]
  Map2Fields (xs ': xss) = MapFields xs ': Map2Fields xss


type family Products (xs :: f Nat) :: Nat where
  Products '[] = 1
  Products (x ': xs) = x * Products xs

type family MapProducts (xss :: f (g Nat)) :: f Nat where
  MapProducts '[] = '[]
  MapProducts (xs ': xss) = Products xs ': MapProducts xss

type family Sums (xs :: f Nat) :: Nat where
  Sums '[] = 0
  Sums (x ': xs) = x + Sums xs

--------------------------------------------------------------------------------
-- Functions that deal with Choices
--------------------------------------------------------------------------------

mapChoices :: forall xs . (All MemRep xs) => NP I xs -> NP Finite (MapChoices xs)
mapChoices SOP.Nil   = SOP.Nil
mapChoices (x :* xs) = choices (unI x) :* mapChoices xs

map2choices :: (All2 MemRep xss) => NS (NP I) xss -> NS (NP Finite) (Map2Choices xss)
map2choices (Z x) = Z (mapChoices x)
map2choices (S xs) = S (map2choices xs)

sums :: All KnownNat xs => NS Finite xs -> Finite (Sums xs)
sums (Z y) = combineSum (Left y)
sums (S ys) = combineSum (Right (sums ys))

mapProducts :: (All2 KnownNat xss) => NS (NP Finite) xss -> NS Finite (MapProducts xss)
mapProducts (Z x) = Z (combineProducts x)
mapProducts (S xs) = S (mapProducts xs)

combineProducts :: (All KnownNat xs) => NP Finite xs -> Finite (Products xs)
combineProducts SOP.Nil = 0
combineProducts (y :* ys) = combineProduct (y, combineProducts ys)

--------------------------------------------------------------------------------
-- Functions that deal with Fields
--------------------------------------------------------------------------------

mapFields :: forall xs . (All MemRep xs) => NP I xs -> NP Product (MapFields xs)
mapFields SOP.Nil   = SOP.Nil
mapFields (x :* xs) = fields (unI x) :* mapFields xs

map2Fields :: (All2 MemRep xss) => NS (NP I) xss -> NS (NP Product) (Map2Fields xss)
map2Fields (Z x) = Z (mapFields x)
map2Fields (S xs) = S (map2Fields xs)

mapAppends :: NS (NP Product) xss -> NS Product (MapAppends xss)
mapAppends (Z x) = Z (appends x)
mapAppends (S xs) = S (mapAppends xs)

appends :: NP Product xs -> Product (Appends xs)
appends SOP.Nil   = Nil
appends (x :* xs) = concatP x (appends xs)

foldMerge :: NP ProductType xss -> NS Product xss -> Product (FoldMerge xss)
foldMerge SOP.Nil   _      = Nil
foldMerge (_ :* xs) (Z y)  = zipSumLeft y (foldMergeT xs)
foldMerge (x :* xs) (S ys) = zipSumRight x (foldMerge xs ys)

appendsT :: NP ProductType xs -> ProductType (Appends xs)
appendsT SOP.Nil   = PTNil
appendsT (x :* xs) = concatPT x (appendsT xs)

mapAppendsT :: NP (NP ProductType) xss -> NP ProductType (MapAppends xss)
mapAppendsT SOP.Nil = SOP.Nil
mapAppendsT (x :* xs) = appendsT x :* mapAppendsT xs

foldMergeT :: NP ProductType xss -> ProductType (FoldMerge xss)
foldMergeT SOP.Nil = PTNil
foldMergeT (x :* xs) = zipSumT x (foldMergeT xs)

--------------------------------------------------------------------------------
-- Functions that deal with creating values from types

newtype PF a = PF (ProductType (Fields a))

pureMapFields :: forall xs . (All MemRep xs) => NP ProductType (MapFields xs)
pureMapFields = convertPureFields (pureFields @xs)
  where
    convertPureFields :: NP PF ys -> NP ProductType (MapFields ys)
    convertPureFields SOP.Nil   = SOP.Nil
    convertPureFields ((PF x) :* xs) = x :* convertPureFields xs

    pureFields :: (All MemRep zs) => NP PF zs
    pureFields = cpure_NP (Proxy :: Proxy MemRep) purePF

    purePF :: forall x . (MemRep x) => PF x
    purePF = PF $ emptyFields @x

newtype NPT a = NPT (NP (ProductType) (MapFields a))

pureMap2Fields :: forall xss . (All2 MemRep xss) => NP (NP ProductType) (Map2Fields xss)
pureMap2Fields = convertPure2Fields (pure2Fields @xss)
  where
    convertPure2Fields :: NP NPT yss -> NP (NP ProductType) (Map2Fields yss)
    convertPure2Fields SOP.Nil   = SOP.Nil
    convertPure2Fields ((NPT x) :* xs) = x :* convertPure2Fields xs

    pure2Fields :: (All2 MemRep zss) => NP NPT zss
    pure2Fields = cpure_NP (Proxy :: Proxy (All MemRep)) pureNPT

    pureNPT :: forall xs . (All MemRep xs) => NPT xs
    pureNPT = NPT $ pureMapFields @xs

-------------------------------------------------------
-- Functions to get back to the SOP representation

unAppends :: Product (Appends xs) -> NP ProductType xs -> NP Product xs
unAppends (Cons x xs) ((PTCons _ ys) :* yss) = (Cons x xs') :* ys'
  where
    (xs' :* ys') = unAppends xs (ys :* yss)
unAppends xs          (PTNil :* yss)         = Nil :* (unAppends xs yss)
unAppends Nil         SOP.Nil                = SOP.Nil

mapUnAppends :: NS Product (MapAppends xss) -> NP (NP ProductType) xss -> NS (NP Product) xss
mapUnAppends (Z x)  (y :* _)  = Z (unAppends x y)
mapUnAppends (S xs) (_ :* ys) = S (mapUnAppends xs ys)
