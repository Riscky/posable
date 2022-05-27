{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE DefaultSignatures       #-}
{-# LANGUAGE ExplicitNamespaces      #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE NoStarIsType            #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Exports the `POSable` class, which has a generic implementation `GPOSable`.
--   Also re-exports Generic.SOP, which is needed to derive POSable.
module Generics.POSable.POSable (POSable(..), Generic, Finite) where

import           Data.Finite                     (combineProduct, combineSum,
                                                  separateProduct, separateSum)
import           Generics.POSable.Representation
import           Generics.SOP                    hiding (Nil, shift)
import           Generics.SOP.NP                 hiding (Nil)

import           Data.Kind                       (Type)

import qualified Generics.SOP                    as SOP

import           GHC.Base                        (Nat)
import           GHC.TypeLits                    (KnownNat, type (*), type (+))

import           Data.Finite.Internal

-- | POSable, the base of this library. Provide a compact memory representation
--   for a type and a function to get back to the original type.
--   This memory representation consist of `choices`, that represent all
--   constructor choices in the type in a single Finite integer, and `fields`
--   which represents all values in the type as a Product of Sums, which can
--   be mapped to a struct-of-arrays representation for use in array-based
--   languages like Accelerate.
class (KnownNat (Choices x)) => POSable x where
  type Choices x :: Nat
  type Choices x = GChoices (SOP I (Code x))

  choices :: x -> Finite (Choices x)
  default choices ::
    ( Generic x
    , (GPOSable (SOP I (Code x)))
    , GChoices (SOP I (Code x)) ~ Choices x
    ) => x -> Finite (Choices x)
  choices x = gchoices $ from x

  emptyChoices :: Finite (Choices x)
  emptyChoices = 0

  fromPOSable :: Finite (Choices x) -> Product (Fields x) -> x

  default fromPOSable ::
    ( Generic x
    , GPOSable (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    , Choices x ~ GChoices (SOP I (Code x))
    ) => Finite (Choices x) -> Product (Fields x) -> x
  fromPOSable cs fs = to $ gfromPOSable cs fs

  type Fields x :: [[Type]]
  type Fields x = GFields (SOP I (Code x))

  fields :: x -> Product (Fields x)

  default fields ::
    ( Generic x
    , Fields x ~ GFields (SOP I (Code x))
    , GPOSable (SOP I (Code x))
    ) => x -> Product (Fields x)
  fields x = gfields $ from x

  emptyFields :: ProductType (Fields x)

  default emptyFields ::
    ( GPOSable (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => ProductType (Fields x)
  emptyFields  = gemptyFields @(SOP I (Code x))


-----------------------------------------------------------------------
-- | Generic implementation of POSable,
class (KnownNat (GChoices x)) => GPOSable x where
  type GChoices x :: Nat
  gchoices :: x -> Finite (GChoices x)

  type GFields x :: [[Type]]
  gfields :: x -> Product (GFields x)

  gfromPOSable :: Finite (GChoices x) -> Product (GFields x) -> x

  gemptyFields :: ProductType (GFields x)

-----------------------------------------------------------------------
-- Generic instance for POSable
instance
  ( All2 POSable xss
  , KnownNat (Sums (MapProducts (Map2Choices xss)))
  , All2 KnownNat (Map2Choices xss)
  , All KnownNat (MapProducts (Map2Choices xss))
  , KnownNat (Length xss)
  ) => GPOSable (SOP I xss) where

  type GChoices (SOP I xss) = Sums (MapProducts (Map2Choices xss))
  gchoices x = sums $ mapProducts $ map2choices $ unSOP x

  type GFields (SOP I xss) = FoldMerge (MapConcat (Map2Fields xss))
  gfields (SOP x)         = foldMerge
                              (mapConcatT (pureMap2Fields @xss))
                              (mapConcat (map2Fields x))

  gemptyFields = foldMergeT $ mapConcatT (pureMap2Fields @xss)

  gfromPOSable cs fs = SOP (mapFromPOSable cs' fs (pureConcatFields @xss))
    where
      cs' = unSums cs (pureChoices2 @xss)

--------------------------------------------------------------------------------
-- Supporting types and classes
--------------------------------------------------------------------------------

type family Length (xs :: [x]) :: Nat where
  Length '[] = 0
  Length (x ': xs) = Length xs + 1

type family MapLength (xss :: [[x]]) :: [Nat] where
  MapLength '[] = '[]
  MapLength (x ': xs) = Length x ': MapLength xs

type family MapChoices (xs :: [Type]) :: [Nat] where
  MapChoices '[] = '[]
  MapChoices (x ': xs) = Choices x ': MapChoices xs


type family Map2Choices (xss :: [[Type]]) :: [[Nat]] where
  Map2Choices '[] = '[]
  Map2Choices (xs ': xss) = MapChoices xs ': Map2Choices xss


type family MapFields (xs :: [Type]) :: [[[Type]]] where
  MapFields '[] = '[]
  MapFields (x ': xs) = Fields x ': MapFields xs


type family Map2Fields (xss :: [[Type]]) :: [[[[Type]]]] where
  Map2Fields '[] = '[]
  Map2Fields (xs ': xss) = MapFields xs ': Map2Fields xss


type family Products (xs :: [Nat]) :: Nat where
  Products '[] = 1
  Products (x ': xs) = x * Products xs

type family MapProducts (xss :: [[Nat]]) :: [Nat] where
  MapProducts '[] = '[]
  MapProducts (xs ': xss) = Products xs ': MapProducts xss

type family Sums (xs :: [Nat]) :: Nat where
  Sums '[] = 0
  Sums (x ': xs) = x + Sums xs

--------------------------------------------------------------------------------
-- Functions that deal with Choices
--------------------------------------------------------------------------------

mapChoices :: forall xs . (All POSable xs) => NP I xs -> NP Finite (MapChoices xs)
mapChoices SOP.Nil   = SOP.Nil
mapChoices (x :* xs) = choices (unI x) :* mapChoices xs

map2choices :: (All2 POSable xss) => NS (NP I) xss -> NS (NP Finite) (Map2Choices xss)
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

mapFields :: forall xs . (All POSable xs) => NP I xs -> NP Product (MapFields xs)
mapFields SOP.Nil   = SOP.Nil
mapFields (x :* xs) = fields (unI x) :* mapFields xs

map2Fields :: (All2 POSable xss) => NS (NP I) xss -> NS (NP Product) (Map2Fields xss)
map2Fields (Z x)  = Z (mapFields x)
map2Fields (S xs) = S (map2Fields xs)

mapConcat :: NS (NP Product) xss -> NS Product (MapConcat xss)
mapConcat (Z x)  = Z (appends x)
mapConcat (S xs) = S (mapConcat xs)

appends :: NP Product xs -> Product (Concat xs)
appends SOP.Nil   = Nil
appends (x :* xs) = concatP x (appends xs)

foldMerge :: NP ProductType xss -> NS Product xss -> Product (FoldMerge xss)
foldMerge (_ :* SOP.Nil) (Z y)   = y
foldMerge (_ :* SOP.Nil) (S _)   = error "Reached an inaccessible pattern"
foldMerge SOP.Nil   _            = Nil
foldMerge (_ :* x' :* xs) (Z y)  = merge $ Left (y, foldMergeT (x' :* xs))
foldMerge (x :* x' :* xs) (S ys) = merge $ Right (x, foldMerge (x' :* xs) ys)

appendsT :: NP ProductType xs -> ProductType (Concat xs)
appendsT SOP.Nil   = PTNil
appendsT (x :* xs) = concatPT x (appendsT xs)

mapConcatT :: NP (NP ProductType) xss -> NP ProductType (MapConcat xss)
mapConcatT SOP.Nil   = SOP.Nil
mapConcatT (x :* xs) = appendsT x :* mapConcatT xs

foldMergeT :: NP ProductType xss -> ProductType (FoldMerge xss)
foldMergeT (x :* SOP.Nil)  = x
foldMergeT SOP.Nil         = PTNil
foldMergeT (x :* x' :* xs) = mergeT x (foldMergeT (x' :* xs))

--------------------------------------------------------------------------------
-- Functions that deal with creating Products from types

newtype ProductFields a = ProductFields (Product (Fields a))

newtype ProductFieldsT a = ProductFieldsT (ProductType (Fields a))

newtype ProductConcatFieldsT a = ProductConcatFieldsT (ProductType (Concat (MapFields a)))

newtype ProductMapFieldsT a = ProductMapFieldsT (NP ProductType (MapFields a))

pureMapFields :: forall xs . (All POSable xs) => NP ProductType (MapFields xs)
pureMapFields = convert $ pureFields @xs
  where
    convert :: NP ProductFieldsT ys -> NP ProductType (MapFields ys)
    convert SOP.Nil                  = SOP.Nil
    convert (ProductFieldsT x :* xs) = x :* convert xs

pureFields :: (All POSable xs) => NP ProductFieldsT xs
pureFields = cpure_NP (Proxy :: Proxy POSable) pureProductFields
  where
    pureProductFields :: forall x . (POSable x) => ProductFieldsT x
    pureProductFields = ProductFieldsT $ emptyFields @x

pureMap2Fields :: forall xss . (All2 POSable xss) => NP (NP ProductType) (Map2Fields xss)
pureMap2Fields = convert $ pure2Fields @xss
  where
    convert :: NP ProductMapFieldsT yss -> NP (NP ProductType) (Map2Fields yss)
    convert SOP.Nil                     = SOP.Nil
    convert (ProductMapFieldsT x :* xs) = x :* convert xs

pure2Fields :: (All2 POSable zss) => NP ProductMapFieldsT zss
pure2Fields = cpure_NP (Proxy :: Proxy (All POSable)) pureProductMapFieldsT
  where
    pureProductMapFieldsT :: forall xs . (All POSable xs) => ProductMapFieldsT xs
    pureProductMapFieldsT = ProductMapFieldsT $ pureMapFields @xs

pureConcatFields :: forall xss . (All2 POSable xss) => NP ProductConcatFieldsT xss
pureConcatFields = convert $ pure2Fields @xss
  where
    convert :: NP ProductMapFieldsT yss -> NP ProductConcatFieldsT yss
    convert SOP.Nil         = SOP.Nil
    convert (ProductMapFieldsT x :* xs) = ProductConcatFieldsT (appendsT x) :* convert xs

--------------------------------------------------------------------------------
-- Functions that deal with creating Choices from types

newtype FChoices a = FChoices (Finite (Choices a))

newtype ProductsMapChoices a = ProductsMapChoices (Finite (Products (MapChoices a)))

newtype FMapChoices a = FMapChoices (NP Finite (MapChoices a))

pureChoices2 :: forall xss . (All2 KnownNat (Map2Choices xss)) => (All2 POSable xss) => NP ProductsMapChoices xss
pureChoices2 = convert $ pure2Choices @xss
  where
    convert :: (All2 KnownNat (Map2Choices yss)) => NP FMapChoices yss -> NP ProductsMapChoices yss
    convert SOP.Nil         = SOP.Nil
    convert (FMapChoices x :* xs) = ProductsMapChoices (combineProducts x) :* convert xs

pureMapChoices :: forall xs . (All POSable xs) => NP Finite (MapChoices xs)
pureMapChoices = convert $ pureChoices @xs
  where
    convert :: NP FChoices ys -> NP Finite (MapChoices ys)
    convert SOP.Nil            = SOP.Nil
    convert (FChoices x :* xs) = x :* convert xs

pureChoices :: (All POSable xs) => NP FChoices xs
pureChoices = cpure_NP (Proxy :: Proxy POSable) pureFChoices
  where
    pureFChoices :: forall x . (POSable x) => FChoices x
    pureFChoices = FChoices $ emptyChoices @x

pure2Choices :: (All2 POSable xss) => NP FMapChoices xss
pure2Choices = cpure_NP (Proxy :: Proxy (All POSable)) pureFMapChoices
  where
    pureFMapChoices :: forall xs . (All POSable xs) => FMapChoices xs
    pureFMapChoices = FMapChoices $ pureMapChoices @xs

-------------------------------------------------------
-- Functions to get back to the SOP representation

separateProducts :: (All KnownNat (MapChoices xs)) => ProductsMapChoices xs -> NP FChoices xs -> NP FChoices xs
separateProducts _ SOP.Nil   = SOP.Nil
separateProducts (ProductsMapChoices x) (_ :* ys) = FChoices x' :* separateProducts (ProductsMapChoices xs) ys
  where
    (x', xs)  = separateProduct x

zipFromPOSable :: All POSable xs => NP FChoices xs -> NP ProductFields xs -> NP I xs
zipFromPOSable SOP.Nil SOP.Nil = SOP.Nil
zipFromPOSable (FChoices c :* cs) (ProductFields f :* fs) = I (fromPOSable c f) :* zipFromPOSable cs fs

foldMergeT2 :: NP ProductConcatFieldsT xss -> ProductType (FoldMerge (MapConcat (Map2Fields xss)))
foldMergeT2 (ProductConcatFieldsT x :* SOP.Nil)  = x
foldMergeT2 SOP.Nil                              = PTNil
foldMergeT2 (ProductConcatFieldsT x :* x' :* xs) = mergeT x (foldMergeT2 (x' :* xs))

unSums :: (All KnownNat (MapProducts (Map2Choices xs))) => Finite (Sums (MapProducts (Map2Choices xs))) -> NP ProductsMapChoices xs -> NS ProductsMapChoices xs
unSums _ SOP.Nil = error "Cannot construct empty sum"
unSums x (_ :* ys) = case separateSum x of
  Left x'  -> Z (ProductsMapChoices x')
  Right x' -> S (unSums x' ys)

mapFromPOSable
  :: forall xss .
  ( All2 KnownNat (Map2Choices xss)
  , All2 POSable xss
  ) => NS ProductsMapChoices xss
  -> Product (FoldMerge (MapConcat (Map2Fields xss)))
  -> NP ProductConcatFieldsT xss
  -> NS (NP I) xss
mapFromPOSable (Z cs) fs fts@(_ :* _ :* _) = Z (zipFromPOSable cs' ( unConcat (unMergeLeft fs fts) pureFields))
  where
    cs' = separateProducts cs pureChoices
mapFromPOSable (S cs) fs fts@(_ :* _ :* _) = S (mapFromPOSable cs (unMergeRight fs fts) (tl fts))
mapFromPOSable (Z cs) fs (_ :* SOP.Nil) = Z (zipFromPOSable cs' (unConcat fs pureFields))
  where
    cs' = separateProducts cs pureChoices
mapFromPOSable (S cs) _ fts@(_ :* SOP.Nil) = S (mapFromPOSable cs Nil (tl fts))

unConcat :: Product (Concat (MapFields xs)) -> NP ProductFieldsT xs -> NP ProductFields xs
unConcat Nil SOP.Nil     = SOP.Nil
unConcat xs  (ProductFieldsT ys :* yss) = ProductFields x' :* unConcat xs' yss
  where
    (x', xs') = unConcatP xs ys

unMergeLeft :: forall xs xss . Product (Merge (Concat (MapFields xs)) (FoldMerge (MapConcat (Map2Fields xss)))) -> NP ProductConcatFieldsT (xs ': xss) -> Product (Concat (MapFields xs))
unMergeLeft xs (ProductConcatFieldsT y :* ys) = splitLeft xs y (foldMergeT2 @xss ys)

unMergeRight :: forall xs xss . Product (Merge (Concat (MapFields xs)) (FoldMerge (MapConcat (Map2Fields xss)))) -> NP ProductConcatFieldsT (xs ': xss) -> Product (FoldMerge (MapConcat (Map2Fields xss)))
unMergeRight xs (ProductConcatFieldsT y :* ys) = splitRight xs y (foldMergeT2 @xss ys)
