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

-- generic instance for unary sums (tuples)
instance (
    (All KnownNat (MapChoices as))
  , (KnownNat (NatProductType (MapChoices as)))
  , All MemRep as
  , (NatProduct (MapChoices as))
  ) => GMemRep (SOP I '[as]) where
  type GChoices (SOP I '[ as]) = SumOfProducts (Map2Choices '[ as])
  gchoices x = combineSumsOfProducts $ map2choices $ unSOP x

  type GFields (SOP I '[as]) = Appends (MapFields as)
  gfields (SOP (Z xs)) = appends (mapFields xs)
  gfields (SOP (S _)) = error "this is not even possible"

  gemptyFields = appendsT (pureMapFields @as)

  gfromMemRep cs fs = undefined -- SOP (Z $ generate cs fs (pureChoices :: NP PC as) (pureFields :: NP PF as))


-- generic instance for binary sums
instance
    ( KnownNat (GChoices (SOP I '[ l, r]))
    , (KnownNat (NatProductType (MapChoices l)))
    , (All KnownNat (MapChoices l))
    , (All KnownNat (MapChoices r))
    , KnownNat (NatProductType (MapChoices r))
    , All MemRep l
    , All MemRep r
    , (NatProduct (MapChoices l))
    , (NatProduct (MapChoices r))
    ) => GMemRep (SOP I '[ l, r]) where
  type GChoices (SOP I '[ l, r]) = SumOfProducts (Map2Choices '[ l, r])
  gchoices x = combineSumsOfProducts $ map2choices $ unSOP x


  type GFields (SOP I '[ l, r]) = FoldMerge (MapAppends (Map2Fields ('[ l, r])))
  gfields (SOP (Z ls))     = zipSumLeft
                              (appends (mapFields ls))
                              (appendsT ((pureMapFields @r)))
  gfields (SOP (S (Z rs))) = zipSumRight
                                (appendsT ( (pureMapFields @l)))
                                (appends (mapFields rs))
  gfields (SOP (S (S _))) = error "this is not even possible"

  gemptyFields = zipSumT
                  (appendsT
                    (pureMapFields @l))
                  (appendsT
                    (pureMapFields @r))


-- generic instance for ternary sums
instance
  ( All MemRep x
  , All MemRep y
  , All MemRep z
  , (KnownNat (NatProductType (MapChoices x)))
  , (KnownNat (NatProductType (MapChoices y)))
  , (KnownNat (NatProductType (MapChoices z)))
  , (All KnownNat (MapChoices x))
  , (All KnownNat (MapChoices y))
  , (All KnownNat (MapChoices z))
  , (NatProduct (MapChoices x))
  , (NatProduct (MapChoices y))
  , (NatProduct (MapChoices z))
  ) => GMemRep (SOP I '[ x, y, z]) where
  type GChoices (SOP I '[ x, y, z]) = SumOfProducts (Map2Choices '[ x, y, z])
  gchoices x = combineSumsOfProducts $ map2choices $ unSOP x

  type GFields (SOP I '[ x, y, z]) = FoldMerge (MapAppends (Map2Fields '[ x, y, z]))
  -- gfields (SOP x)         = undefined $ mapAppends (map2Fields x)
  gfields (SOP (S (Z ys)))     = zipSumRight
                                  (appendsT (pureMapFields @x))
                                  (zipSumLeft
                                    (appends (mapFields ys))
                                    (appendsT ((pureMapFields @z))))
  gfields (SOP (S (S (Z zs)))) = zipSumRight
                                    (appendsT (pureMapFields @x))
                                    (zipSumRight
                                      (appendsT (pureMapFields @y))
                                      (appends (mapFields zs)))
  gfields (SOP (S (S (S _))))  = error "this is not even possible"

  gemptyFields = zipSumT
                    (appendsT (pureMapFields @x))
                    (zipSumT
                      (appendsT (pureMapFields @y))
                      (appendsT (pureMapFields @z)))


-- generic instance for n-ary sums (so for everything)
-- instance
--   ( All2 MemRep xss
--   , (KnownNat (SumOfProducts (Map2Choices xss)))
--   , (All2 KnownNat (Map2Choices xss))
--   , (All NatProduct (Map2Choices xss))
--   ) => GMemRep (SOP I xss) where
--   type GChoices (SOP I xss) = SumOfProducts (Map2Choices xss)
--   gchoices x = combineSumsOfProducts $ map2choices $ unSOP x

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
  

class (All KnownNat x, KnownNat (NatProductType x)) => NatProduct x where
  type NatProductType x :: Nat

instance NatProduct '[] where
  type NatProductType '[] = 1

instance (KnownNat x, All KnownNat xs, KnownNat (NatProductType xs)) => NatProduct (x ': xs) where
  type NatProductType (x ': xs) = x * NatProductType xs
  

type family SumOfProducts (xss :: f (g Nat)) :: Nat where
  SumOfProducts '[] = 0
  SumOfProducts (xs ': xss) = NatProductType xs + SumOfProducts xss

--------------------------------------------------------------------------------
-- Supporting functions
--------------------------------------------------------------------------------

mapChoices :: forall xs . (All MemRep xs) => NP I xs -> NP Finite (MapChoices xs)
mapChoices SOP.Nil   = SOP.Nil
mapChoices (x :* xs) = choices (unI x) :* mapChoices xs

map2choices :: (All2 MemRep xss) => NS (NP I) xss -> NS (NP Finite) (Map2Choices xss)
map2choices (Z x) = Z (mapChoices x)
map2choices (S xs) = S (map2choices xs)


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

combineSumsOfProducts :: (All2 KnownNat xss, All NatProduct xss) => NS (NP Finite) xss -> Finite (SumOfProducts xss)
combineSumsOfProducts (Z y) = combineSum (Left (combineProducts y))
combineSumsOfProducts (S ys) = combineSum (Right (combineSumsOfProducts ys))

foldMergeMapAppends :: NS (NP Product) xss -> Product (FoldMerge (MapAppends xss))
foldMergeMapAppends = undefined

combineProducts :: (All KnownNat xs) => NP Finite xs -> Finite (NatProductType xs)
combineProducts SOP.Nil = 0
combineProducts (y :* ys) = combineProduct (y, combineProducts ys)

appendsT :: NP ProductType xs -> ProductType (Appends xs)
appendsT SOP.Nil   = PTNil
appendsT (x :* xs) = concatPT x (appendsT xs)

mapAppendsT :: NP (NP ProductType) xss -> NP ProductType (MapAppends xss)
mapAppendsT SOP.Nil = SOP.Nil
mapAppendsT (x :* xs) = appendsT x :* mapAppendsT xs


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
