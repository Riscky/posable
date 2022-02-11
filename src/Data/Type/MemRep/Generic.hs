{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE NoStarIsType            #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.Type.MemRep.Generic (GMemRep) where

import           Data.Finite                     (Finite, combineProduct,
                                                  combineSum, separateProduct,
                                                  separateSum)
import           Data.Type.MemRep.MemRep
import           Data.Type.MemRep.Representation
import           Generics.SOP                    hiding (Nil)
import           Generics.SOP.NP                 hiding (Nil)

import           Data.Kind                       (Type)

import qualified Generics.SOP                    as SOP

import           GHC.Base                        (Nat)
import           GHC.TypeLits                    (KnownNat, type (*), type (+))


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

  gfromMemRep cs fs = SOP (comapFromMemRep cs' fs')
    where
      cs' = unSums cs (pureChoices2 @xss)
      fs' = unMerge fs (pureAppendsFields @xss)

--------------------------------------------------------------------------------
-- Supporting types and classes
--------------------------------------------------------------------------------

type family MapChoices (xs :: f x) = (r :: f Nat) | r -> f where
  MapChoices '[] = '[]
  MapChoices (x ': xs) = Choices x ': MapChoices xs


type family Map2Choices (xss :: f (g x)) :: f (g Nat) where
  Map2Choices '[] = '[]
  Map2Choices (xs ': xss) = MapChoices xs ': Map2Choices xss


type family MapFields (xs :: f x) = (r :: f [[Type]]) | r -> f where
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
map2choices (Z x)  = Z (mapChoices x)
map2choices (S xs) = S (map2choices xs)

sums :: All KnownNat xs => NS Finite xs -> Finite (Sums xs)
sums (Z y)  = combineSum (Left y)
sums (S ys) = combineSum (Right (sums ys))

mapProducts :: (All2 KnownNat xss) => NS (NP Finite) xss -> NS Finite (MapProducts xss)
mapProducts (Z x)  = Z (combineProducts x)
mapProducts (S xs) = S (mapProducts xs)

combineProducts :: (All KnownNat xs) => NP Finite xs -> Finite (Products xs)
combineProducts SOP.Nil   = 0
combineProducts (y :* ys) = combineProduct (y, combineProducts ys)

--------------------------------------------------------------------------------
-- Functions that deal with Fields
--------------------------------------------------------------------------------

mapFields :: forall xs . (All MemRep xs) => NP I xs -> NP Product (MapFields xs)
mapFields SOP.Nil   = SOP.Nil
mapFields (x :* xs) = fields (unI x) :* mapFields xs

map2Fields :: (All2 MemRep xss) => NS (NP I) xss -> NS (NP Product) (Map2Fields xss)
map2Fields (Z x)  = Z (mapFields x)
map2Fields (S xs) = S (map2Fields xs)

mapAppends :: NS (NP Product) xss -> NS Product (MapAppends xss)
mapAppends (Z x)  = Z (appends x)
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
mapAppendsT SOP.Nil   = SOP.Nil
mapAppendsT (x :* xs) = appendsT x :* mapAppendsT xs

foldMergeT :: NP ProductType xss -> ProductType (FoldMerge xss)
foldMergeT SOP.Nil   = PTNil
foldMergeT (x :* xs) = zipSumT x (foldMergeT xs)

--------------------------------------------------------------------------------
-- Functions that deal with creating Products from types

newtype ProductFields a = ProductFields (Product (Fields a))

newtype ProductFieldsT a = ProductFieldsT (ProductType (Fields a))

newtype ProductAppendsFields a = ProductAppendsFields (Product (Appends (MapFields a)))

newtype ProductAppendsFieldsT a = ProductAppendsFieldsT (ProductType (Appends (MapFields a)))

newtype ProductMapFieldsT a = ProductMapFieldsT (NP (ProductType) (MapFields a))

pureMapFields :: forall xs . (All MemRep xs) => NP ProductType (MapFields xs)
pureMapFields = convert $ pureFields @xs
  where
    convert :: NP ProductFieldsT ys -> NP ProductType (MapFields ys)
    convert SOP.Nil         = SOP.Nil
    convert ((ProductFieldsT x) :* xs) = x :* convert xs

pureFields :: (All MemRep xs) => NP ProductFieldsT xs
pureFields = cpure_NP (Proxy :: Proxy MemRep) pureProductFields
  where
    pureProductFields :: forall x . (MemRep x) => ProductFieldsT x
    pureProductFields = ProductFieldsT $ emptyFields @x

pureMap2Fields :: forall xss . (All2 MemRep xss) => NP (NP ProductType) (Map2Fields xss)
pureMap2Fields = convert $ pure2Fields @xss
  where
    convert :: NP ProductMapFieldsT yss -> NP (NP ProductType) (Map2Fields yss)
    convert SOP.Nil         = SOP.Nil
    convert ((ProductMapFieldsT x) :* xs) = x :* convert xs

pure2Fields :: (All2 MemRep zss) => NP ProductMapFieldsT zss
pure2Fields = cpure_NP (Proxy :: Proxy (All MemRep)) pureProductMapFieldsT
  where
    pureProductMapFieldsT :: forall xs . (All MemRep xs) => ProductMapFieldsT xs
    pureProductMapFieldsT = ProductMapFieldsT $ pureMapFields @xs

pureAppendsFields :: forall xss . (All2 MemRep xss) => NP ProductAppendsFieldsT xss
pureAppendsFields = convert $ pure2Fields @xss
  where
    convert :: NP ProductMapFieldsT yss -> NP ProductAppendsFieldsT yss
    convert SOP.Nil         = SOP.Nil
    convert ((ProductMapFieldsT x) :* xs) = (ProductAppendsFieldsT (appendsT x) :* convert xs)

--------------------------------------------------------------------------------
-- Functions that deal with creating Choices from types

newtype FChoices a = FChoices (Finite (Choices a))

newtype ProductsMapChoices a = ProductsMapChoices (Finite (Products (MapChoices a)))

newtype FMapChoices a = FMapChoices (NP (Finite) (MapChoices a))

pureChoices2 :: forall xss . (All2 KnownNat (Map2Choices xss)) => (All2 MemRep xss) => NP ProductsMapChoices xss
pureChoices2 = convert $ pure2Choices @xss
  where
    convert :: (All2 KnownNat (Map2Choices yss)) => NP FMapChoices yss -> NP ProductsMapChoices yss
    convert SOP.Nil         = SOP.Nil
    convert ((FMapChoices x) :* xs) = (ProductsMapChoices (combineProducts x) :* convert xs)

pureMapChoices :: forall xs . (All MemRep xs) => NP Finite (MapChoices xs)
pureMapChoices = convert $ pureChoices @xs
  where
    convert :: NP FChoices ys -> NP Finite (MapChoices ys)
    convert SOP.Nil        = SOP.Nil
    convert ((FChoices x) :* xs) = x :* convert xs
    
pureChoices :: (All MemRep xs) => NP FChoices xs
pureChoices = cpure_NP (Proxy :: Proxy MemRep) pureFChoices
  where
    pureFChoices :: forall x . (MemRep x) => FChoices x
    pureFChoices = FChoices $ emptyChoices @x

pure2Choices :: (All2 MemRep xss) => NP FMapChoices xss
pure2Choices = cpure_NP (Proxy :: Proxy (All MemRep)) pureFMapChoices
  where
    pureFMapChoices :: forall xs . (All MemRep xs) => FMapChoices xs
    pureFMapChoices = FMapChoices $ pureMapChoices @xs

-------------------------------------------------------
-- Functions to get back to the SOP representation

unAppends :: ProductAppendsFields xs -> NP ProductFieldsT xs -> NP ProductFields xs
unAppends (ProductAppendsFields Nil) SOP.Nil     = SOP.Nil
unAppends (ProductAppendsFields xs)  (ProductFieldsT ys :* yss) = ProductFields x' :* (unAppends (ProductAppendsFields xs') yss)
  where
    (x', xs') = unConcatP xs ys

separateProducts :: (All KnownNat (MapChoices xs)) => ProductsMapChoices xs -> NP FChoices xs -> NP FChoices xs
separateProducts _ SOP.Nil   = SOP.Nil
separateProducts (ProductsMapChoices x) (_ :* ys) = FChoices x' :* (separateProducts (ProductsMapChoices xs) ys)
  where
    (x', xs)  = separateProduct x

zipFromMemRep :: All MemRep xs => NP FChoices xs -> NP ProductFields xs -> NP I xs
zipFromMemRep SOP.Nil SOP.Nil = SOP.Nil
zipFromMemRep (FChoices c :* cs) (ProductFields f :* fs) = I (fromMemRep c f) :* zipFromMemRep cs fs

unMerge :: Product (FoldMerge (MapAppends (Map2Fields xss))) -> NP ProductAppendsFieldsT xss -> NS ProductAppendsFields xss
unMerge _ SOP.Nil = error "Cannot construct empty sum"
unMerge xs ((ProductAppendsFieldsT y) :* (ys :: NP ProductAppendsFieldsT xs)) = case splitProduct xs y (foldMergeT2 @xs ys) of
  Left l  -> Z (ProductAppendsFields l)
  Right r -> S (unMerge r ys)

foldMergeT2 :: NP ProductAppendsFieldsT xss -> ProductType (FoldMerge (MapAppends (Map2Fields xss)))
foldMergeT2 SOP.Nil                       = PTNil
foldMergeT2 ((ProductAppendsFieldsT x) :* xs) = zipSumT x (foldMergeT2 xs)

unSums :: (All KnownNat (MapProducts (Map2Choices xs))) => Finite (Sums (MapProducts (Map2Choices xs))) -> NP ProductsMapChoices xs -> NS ProductsMapChoices xs
unSums _ SOP.Nil = error "Cannot construct empty sum"
unSums x (_ :* ys) = case separateSum x of
  Left x'  -> Z (ProductsMapChoices x')
  Right x' -> S (unSums x' ys)

comapFromMemRep :: (All2 KnownNat (Map2Choices xss), All2 MemRep xss) => NS ProductsMapChoices xss -> NS ProductAppendsFields xss -> NS (NP I) xss
comapFromMemRep (Z cs) (Z fs) = Z (zipFromMemRep cs' fs')
  where
    cs' = separateProducts cs (pureChoices)
    fs' = unAppends fs (pureFields)
comapFromMemRep (S cs) (S fs) = S (comapFromMemRep cs fs)
comapFromMemRep _ _  = error "Choices and Fields of unequal length"
