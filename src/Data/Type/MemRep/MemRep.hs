{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE DefaultSignatures       #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE NoStarIsType            #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.Type.MemRep.MemRep (MemRep(..), GMemRep(..), Generic) where

import           Data.Finite                     (Finite, combineProduct,
                                                  combineSum, separateProduct,
                                                  separateSum)
import           Data.Type.MemRep.Representation
import           Generics.SOP                    hiding (Nil)
import           Generics.SOP.NP                 hiding (Nil)

import           Data.Kind                       (Type)

import qualified Generics.SOP                    as SOP

import           GHC.Base                        (Nat)
import           GHC.TypeLits                    (KnownNat, type (*), type (+))

-----------------------------------------------------------------------
-- MemRep, the king of this file
class (KnownNat (Choices x)) => MemRep x where
  type Choices x :: Nat
  type Choices x = GChoices (SOP I (Code x))

  choices :: x -> Finite (Choices x)
  default choices ::
    ( Generic x
    , (GMemRep (SOP I (Code x)))
    , GChoices (SOP I (Code x)) ~ Choices x
    ) => x -> Finite (Choices x)
  choices x = gchoices $ from x

  emptyChoices :: Finite (Choices x)
  emptyChoices = 0

  fromMemRep :: Finite (Choices x) -> Product (Fields x) -> x

  default fromMemRep ::
    ( Generic x
    , (GMemRep (SOP I (Code x)))
    , Fields x ~ GFields (SOP I (Code x))
    , Choices x ~ GChoices (SOP I (Code x))
    ) => Finite (Choices x) -> Product (Fields x) -> x
  fromMemRep cs fs = to $ gfromMemRep cs fs

  type Fields x :: [[Type]]
  type Fields x = GFields (SOP I (Code x))

  fields :: x -> Product (Fields x)

  default fields ::
    ( Generic x
    , Fields x ~ GFields (SOP I (Code x))
    , GMemRep (SOP I (Code x))
    ) => x -> Product (Fields x)
  fields x = gfields $ from x

  emptyFields :: ProductType (Fields x)

  default emptyFields ::
    ( GMemRep (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => ProductType (Fields x)
  emptyFields  = gemptyFields @(SOP I (Code x))

--------------------------------------------------------------
-- Generics

-----------------------------------------------------------------------
-- GMemRep, the serf of this file
class (KnownNat (GChoices x)) => GMemRep x where
  type GChoices x :: Nat
  gchoices :: x -> Finite (GChoices x)

  type GFields x :: [[Type]]
  gfields :: x -> Product (GFields x)

  gfromMemRep :: Finite (GChoices x) -> Product (GFields x) -> x

  gemptyFields :: ProductType (GFields x)

-----------------------------------------------------------------------
-- Generic instance for MemRep
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
                              (mapAppendsT (pureMap2Fields @xss))
                              (mapAppends (map2Fields x))

  gemptyFields = foldMergeT $ mapAppendsT (pureMap2Fields @xss)

  gfromMemRep cs fs = SOP (mapFromMemRep cs' fs (pureAppendsFields @xss))
    where
      cs' = unSums cs (pureChoices2 @xss)

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

newtype ProductAppendsFieldsT a = ProductAppendsFieldsT (ProductType (Appends (MapFields a)))

newtype ProductMapFieldsT a = ProductMapFieldsT (NP ProductType (MapFields a))

pureMapFields :: forall xs . (All MemRep xs) => NP ProductType (MapFields xs)
pureMapFields = convert $ pureFields @xs
  where
    convert :: NP ProductFieldsT ys -> NP ProductType (MapFields ys)
    convert SOP.Nil                  = SOP.Nil
    convert (ProductFieldsT x :* xs) = x :* convert xs

pureFields :: (All MemRep xs) => NP ProductFieldsT xs
pureFields = cpure_NP (Proxy :: Proxy MemRep) pureProductFields
  where
    pureProductFields :: forall x . (MemRep x) => ProductFieldsT x
    pureProductFields = ProductFieldsT $ emptyFields @x

pureMap2Fields :: forall xss . (All2 MemRep xss) => NP (NP ProductType) (Map2Fields xss)
pureMap2Fields = convert $ pure2Fields @xss
  where
    convert :: NP ProductMapFieldsT yss -> NP (NP ProductType) (Map2Fields yss)
    convert SOP.Nil                     = SOP.Nil
    convert (ProductMapFieldsT x :* xs) = x :* convert xs

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
    convert (ProductMapFieldsT x :* xs) = ProductAppendsFieldsT (appendsT x) :* convert xs

--------------------------------------------------------------------------------
-- Functions that deal with creating Choices from types

newtype FChoices a = FChoices (Finite (Choices a))

newtype ProductsMapChoices a = ProductsMapChoices (Finite (Products (MapChoices a)))

newtype FMapChoices a = FMapChoices (NP Finite (MapChoices a))

pureChoices2 :: forall xss . (All2 KnownNat (Map2Choices xss)) => (All2 MemRep xss) => NP ProductsMapChoices xss
pureChoices2 = convert $ pure2Choices @xss
  where
    convert :: (All2 KnownNat (Map2Choices yss)) => NP FMapChoices yss -> NP ProductsMapChoices yss
    convert SOP.Nil         = SOP.Nil
    convert (FMapChoices x :* xs) = ProductsMapChoices (combineProducts x) :* convert xs

pureMapChoices :: forall xs . (All MemRep xs) => NP Finite (MapChoices xs)
pureMapChoices = convert $ pureChoices @xs
  where
    convert :: NP FChoices ys -> NP Finite (MapChoices ys)
    convert SOP.Nil            = SOP.Nil
    convert (FChoices x :* xs) = x :* convert xs

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

separateProducts :: (All KnownNat (MapChoices xs)) => ProductsMapChoices xs -> NP FChoices xs -> NP FChoices xs
separateProducts _ SOP.Nil   = SOP.Nil
separateProducts (ProductsMapChoices x) (_ :* ys) = FChoices x' :* separateProducts (ProductsMapChoices xs) ys
  where
    (x', xs)  = separateProduct x

zipFromMemRep :: All MemRep xs => NP FChoices xs -> NP ProductFields xs -> NP I xs
zipFromMemRep SOP.Nil SOP.Nil = SOP.Nil
zipFromMemRep (FChoices c :* cs) (ProductFields f :* fs) = I (fromMemRep c f) :* zipFromMemRep cs fs

foldMergeT2 :: NP ProductAppendsFieldsT xss -> ProductType (FoldMerge (MapAppends (Map2Fields xss)))
foldMergeT2 SOP.Nil                         = PTNil
foldMergeT2 (ProductAppendsFieldsT x :* xs) = zipSumT x (foldMergeT2 xs)

unSums :: (All KnownNat (MapProducts (Map2Choices xs))) => Finite (Sums (MapProducts (Map2Choices xs))) -> NP ProductsMapChoices xs -> NS ProductsMapChoices xs
unSums _ SOP.Nil = error "Cannot construct empty sum"
unSums x (_ :* ys) = case separateSum x of
  Left x'  -> Z (ProductsMapChoices x')
  Right x' -> S (unSums x' ys)

mapFromMemRep :: forall xss . (All2 KnownNat (Map2Choices xss), All2 MemRep xss) => NS ProductsMapChoices xss -> Product (FoldMerge (MapAppends (Map2Fields xss))) -> NP ProductAppendsFieldsT xss -> NS (NP I) xss
mapFromMemRep (Z cs) fs fts = Z (zipFromMemRep cs' ( unAppends (unMergeLeft fs fts) pureFields))
  where
    cs' = separateProducts cs pureChoices
mapFromMemRep (S cs) fs fts = S (mapFromMemRep cs (unMergeRight fs fts) (tl fts))

unAppends :: Product (Appends (MapFields xs)) -> NP ProductFieldsT xs -> NP ProductFields xs
unAppends Nil SOP.Nil     = SOP.Nil
unAppends xs  (ProductFieldsT ys :* yss) = ProductFields x' :* unAppends xs' yss
  where
    (x', xs') = unConcatP xs ys

unMergeLeft :: forall xs xss . Product (Merge (Appends (MapFields xs)) (FoldMerge (MapAppends (Map2Fields xss)))) -> NP ProductAppendsFieldsT (xs ': xss) -> Product (Appends (MapFields xs))
unMergeLeft xs (ProductAppendsFieldsT y :* ys) = splitProductLeft xs y (foldMergeT2 @xss ys)

unMergeRight :: forall xs xss . Product (Merge (Appends (MapFields xs)) (FoldMerge (MapAppends (Map2Fields xss)))) -> NP ProductAppendsFieldsT (xs ': xss) -> Product (FoldMerge (MapAppends (Map2Fields xss)))
unMergeRight xs (ProductAppendsFieldsT y :* ys) = splitProductRight xs y (foldMergeT2 @xss ys)
