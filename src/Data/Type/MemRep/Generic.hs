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
      fs' = unMerge fs (pureNPProductMapFieldsT @xss)

pureNPProductMapFieldsT :: forall xss . (All2 MemRep xss) => NP ProductMapFieldsT xss
pureNPProductMapFieldsT = convert $ pure2Fields @xss

convert :: NP NPT xss -> NP ProductMapFieldsT xss
convert SOP.Nil         = SOP.Nil
convert ((NPT x) :* xs) = (ProductMapFieldsT (appendsT x) :* convert xs)

pureChoices2 :: forall xss . (All2 KnownNat (Map2Choices xss)) => (All2 MemRep xss) => NP FiniteMapChoices xss
pureChoices2 = convertC $ pure2Choices @xss

convertC :: (All2 KnownNat (Map2Choices xss)) => NP NPC xss -> NP FiniteMapChoices xss
convertC SOP.Nil         = SOP.Nil
convertC ((NPC x) :* xs) = (FiniteMapChoices (combineProducts x) :* convertC xs)

unMerge :: Product (FoldMerge (MapAppends (Map2Fields xss))) -> NP ProductMapFieldsT xss -> NS ProductMapFields xss
unMerge _ SOP.Nil = error "Cannot construct empty sum"
unMerge xs ((ProductMapFieldsT y) :* (ys :: NP ProductMapFieldsT xs)) = case splitHorizontal xs y (foldMergeT2 @xs ys) of
  Left l  -> Z (ProductMapFields l)
  Right r -> S (unMerge r ys)

foldMergeT2 :: NP ProductMapFieldsT xss -> ProductType (FoldMerge (MapAppends (Map2Fields xss)))
foldMergeT2 SOP.Nil                       = PTNil
foldMergeT2 ((ProductMapFieldsT x) :* xs) = zipSumT x (foldMergeT2 xs)

newtype FiniteMapChoices a = FiniteMapChoices (Finite (Products (MapChoices a)))

newtype ProductMapFields a = ProductMapFields (Product (Appends (MapFields a)))

newtype ProductMapFieldsT a = ProductMapFieldsT (ProductType (Appends (MapFields a)))

unSums :: (All KnownNat (MapProducts (Map2Choices xs))) => Finite (Sums (MapProducts (Map2Choices xs))) -> NP FiniteMapChoices xs -> NS FiniteMapChoices xs
unSums _ SOP.Nil = error "Cannot construct empty sum"
unSums x (_ :* ys) = case separateSum x of
  Left x'  -> Z (FiniteMapChoices x')
  Right x' -> S (unSums x' ys)

comapFromMemRep :: (All2 KnownNat (Map2Choices xss), All2 MemRep xss) => NS FiniteMapChoices xss -> NS ProductMapFields xss -> NS (NP I) xss
comapFromMemRep (Z cs) (Z fs) = Z (zipFromMemRep cs' fs')
  where
    cs' = separateProducts cs (pureChoices)
    fs' = unAppends fs (pureFields)
comapFromMemRep (S cs) (S fs) = S (comapFromMemRep cs fs)
comapFromMemRep _ _  = error "Choices and Fields of unequal length"


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
-- Functions that deal with creating values from types

newtype PF a = PF (Product (Fields a))

newtype PFT a = PFT (ProductType (Fields a))

pureMapFields :: forall xs . (All MemRep xs) => NP ProductType (MapFields xs)
pureMapFields = convertPureFields (pureFields @xs)
  where
    convertPureFields :: NP PFT ys -> NP ProductType (MapFields ys)
    convertPureFields SOP.Nil         = SOP.Nil
    convertPureFields ((PFT x) :* xs) = x :* convertPureFields xs

pureFields :: (All MemRep zs) => NP PFT zs
pureFields = cpure_NP (Proxy :: Proxy MemRep) purePFT

purePFT :: forall x . (MemRep x) => PFT x
purePFT = PFT $ emptyFields @x

newtype NPT a = NPT (NP (ProductType) (MapFields a))

pureMap2Fields :: forall xss . (All2 MemRep xss) => NP (NP ProductType) (Map2Fields xss)
pureMap2Fields = convertPure2Fields (pure2Fields @xss)
  where
    convertPure2Fields :: NP NPT yss -> NP (NP ProductType) (Map2Fields yss)
    convertPure2Fields SOP.Nil         = SOP.Nil
    convertPure2Fields ((NPT x) :* xs) = x :* convertPure2Fields xs

pure2Fields :: (All2 MemRep zss) => NP NPT zss
pure2Fields = cpure_NP (Proxy :: Proxy (All MemRep)) pureNPT

pureNPT :: forall xs . (All MemRep xs) => NPT xs
pureNPT = NPT $ pureMapFields @xs

-------------------------------------------------------
-- Functions to get back to the SOP representation

unConcatP :: Product (x ++ y) -> ProductType x -> (Product x, Product y)
unConcatP xs PTNil                  = (Nil, xs)
unConcatP (Cons x xs) (PTCons _ ts) = (Cons x xs', ys')
  where
    (xs', ys') = unConcatP xs ts

unAppends :: ProductMapFields xs -> NP PFT xs -> NP PF xs
unAppends (ProductMapFields Nil) SOP.Nil     = SOP.Nil
unAppends (ProductMapFields xs)  (PFT ys :* yss) = PF x' :* (unAppends (ProductMapFields xs') yss)
  where
    (x', xs') = unConcatP xs ys

separateProducts :: (All KnownNat (MapChoices xs)) => FiniteMapChoices xs -> NP PC xs -> NP PC xs
separateProducts _ SOP.Nil   = SOP.Nil
separateProducts (FiniteMapChoices x) (_ :* ys) = PC x' :* (separateProducts (FiniteMapChoices xs) ys)
  where
    (x', xs)  = separateProduct x

newtype PC a = PC (Finite (Choices a))

pureMapChoices :: forall xs . (All MemRep xs) => NP Finite (MapChoices xs)
pureMapChoices = convertPureChoices (pureChoices @xs)
  where
    convertPureChoices :: NP PC ys -> NP Finite (MapChoices ys)
    convertPureChoices SOP.Nil        = SOP.Nil
    convertPureChoices ((PC x) :* xs) = x :* convertPureChoices xs

pureChoices :: (All MemRep xs) => NP PC xs
pureChoices = cpure_NP (Proxy :: Proxy MemRep) purePC

purePC :: forall x . (MemRep x) => PC x
purePC = PC $ emptyChoices @x

newtype NPC a = NPC (NP (Finite) (MapChoices a))

pure2Choices :: (All2 MemRep xss) => NP NPC xss
pure2Choices = cpure_NP (Proxy :: Proxy (All MemRep)) pureNPC

pureNPC :: forall xs . (All MemRep xs) => NPC xs
pureNPC = NPC $ pureMapChoices @xs

zipFromMemRep :: All MemRep xs => NP PC xs -> NP PF xs -> NP I xs
zipFromMemRep SOP.Nil SOP.Nil = SOP.Nil
zipFromMemRep (PC c :* cs) (PF f :* fs) = I (fromMemRep c f) :* zipFromMemRep cs fs

-------------------------------------------------------------------------------
-- Functions that deal with unmerging Products

splitHorizontal :: Product (Merge l r) -> ProductType l -> ProductType r -> Either (Product l) (Product r)
-- Base case: both products are of the same length
splitHorizontal (Cons x Nil) (PTCons l PTNil) (PTCons _ PTNil) = case splitSum x l of
  Left l'  -> Left (Cons l' Nil)
  Right r' -> Right (Cons r' Nil)
-- Base case: Right is longer
splitHorizontal x           PTNil         _             = Right x
-- Base case: Left is longer
splitHorizontal x           _             PTNil         = Left x
-- unsafeCoerce to prevent having to prove that x :: Sum (l ++ r)
splitHorizontal (Cons x xs) (PTCons l ls) (PTCons _ rs) = case splitSum x l of
  Left l'-> case splitHorizontal xs ls rs of
    Left ls' -> Left (Cons l' ls')
    Right _  -> error "Cannot split in Right and Left at the same time"
  Right r' -> case splitHorizontal xs ls rs of
    Right rs' -> Right (Cons r' rs')
    Left _    -> error "Cannot split in Right and Left at the same time"


splitSum :: Sum (l ++ r) -> SumType l -> Either (Sum l) (Sum r)
splitSum (Pick x)  (STSucc _ _)  = Left (Pick x)
splitSum xs        STZero        = Right xs
splitSum (Skip xs) (STSucc _ ls) = case splitSum xs ls of
  Left l  -> Left (Skip l)
  Right r -> Right r
