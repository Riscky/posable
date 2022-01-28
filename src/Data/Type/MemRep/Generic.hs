{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.Type.MemRep.Generic where

import Generics.SOP hiding (Nil)
import Generics.SOP.NP hiding (Nil)
import Data.Finite (Finite, combineProduct, combineSum)
import Data.Type.MemRep.MemRep
import Data.Type.MemRep.Representation

import Fcf ( Eval, Exp, type (++), Map)

import qualified Generics.SOP as SOP

import GHC.Base (Nat)
import GHC.TypeLits (KnownNat, type (*), type (+))

-- generic instance for unary sums (tuples)
-- instance (
--     (All KnownNat (MapChoices as))
--   , (KnownNat (NatProductType (MapChoices as)))
--   , All MemRep as
--   ) => GMemRep (SOP I '[as]) where
--   -- type GChoices (SOP I '[as]) = NatProductType (MapChoices as)
--   gchoices (SOP (Z xs)) = combineProducts (npMapC xs)
--   gchoices (SOP _) = error "rare situ"

--   type GFields (SOP I '[as]) = Eval (Foldl (++) '[] (Eval (Map AppFields as)))
--   gfields (SOP (Z xs)) = npFold Nil (npMapF xs)
--   gfields (SOP (S _)) = error "this is not even possible"

--   gemptyFields = npFoldT PTNil (convertPureFields (pureFields :: NP PF as))

--   gfromMemRep cs fs = undefined -- SOP (Z $ generate cs fs (pureChoices :: NP PC as) (pureFields :: NP PF as))


-- generic instance for binary sums
-- instance
--     ( KnownNat (GChoices (SOP I '[ l, r]))
--     , (KnownNat (NatProductType (MapChoices l)))
--     , (All KnownNat (MapChoices l))
--     , (All KnownNat (MapChoices r))
--     , KnownNat (NatProductType (MapChoices r))
--     , All MemRep l
--     , All MemRep r
--     ) => GMemRep (SOP I '[ l, r]) where
--   -- type GChoices (SOP I '[ l, r]) = NatProductType (MapChoices l) + NatProductType (MapChoices r)
--   gchoices (SOP (Z xs)) = combineSum $ Left (combineProducts (npMapC xs))
--   gchoices (SOP (S (Z xs))) = combineSum $ Right (combineProducts $ npMapC xs)
--   gchoices _ = error "rare situ"


--   type GFields (SOP I '[ l, r]) = Eval (Foldl (ZipWith' (++)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ l, r])))))
--   gfields (SOP (Z ls))     = zipSumLeft (npFold Nil (npMapF ls)) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))
--   gfields (SOP (S (Z rs))) = zipSumRight (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (npMapF rs))
--   gfields (SOP (S (S _))) = error "this is not even possible"

--   gemptyFields = zipSumT (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))


-- generic instance for ternary sums
-- instance
--   ( All MemRep x
--   , All MemRep y
--   , All MemRep z
--   , (KnownNat (NatProductType (MapChoices x)))
--   , (KnownNat (NatProductType (MapChoices y)))
--   , (KnownNat (NatProductType (MapChoices z)))
--   , (All KnownNat (MapChoices x))
--   , (All KnownNat (MapChoices y))
--   , (All KnownNat (MapChoices z))
--   ) => GMemRep (SOP I '[ x, y, z]) where

--   type GFields (SOP I '[ x, y, z]) = Eval (Foldl (ZipWith' (++)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ x, y, z])))))
--   gfields (SOP (Z xs))         = zipSumLeft (zipSumLeft (npFold Nil (npMapF xs)) (npFoldT PTNil (convertPureFields (pureFields :: NP PF y)))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF z)))
--   gfields (SOP (S (Z ys)))     = zipSumLeft (zipSumRight (npFoldT PTNil (convertPureFields (pureFields :: NP PF x))) (npFold Nil (npMapF ys))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF z)))
--   gfields (SOP (S (S (Z zs)))) = zipSumRight (zipSumT (npFoldT PTNil (convertPureFields (pureFields :: NP PF x))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF y)))) (npFold Nil (npMapF zs))
--   gfields (SOP (S (S (S _))))  = error "this is not even possible"

--   gemptyFields = undefined -- zipSumT (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))


-- generic instance for n-ary sums (so for everything)
instance
  ( All2 MemRep xss
  , (KnownNat (SumOfProducts (Map2Choices xss)))
  , (All2 KnownNat (Map2Choices xss))
  , (All NatProduct (Map2Choices xss))
  ) => GMemRep (SOP I xss) where
  type GChoices (SOP I xss) = SumOfProducts (Map2Choices xss)
  gchoices x = combineSumsOfProducts $ map2choices $ unSOP x

--------------------------------------------------------------------------------
-- Supporting types and classes
--------------------------------------------------------------------------------

type family MapChoices (xs :: f x) :: f Nat where
  MapChoices '[] = '[]
  MapChoices (x ': xs) = Choices x ': MapChoices xs


type family Map2Choices (xss :: f (g x)) :: f (g Nat) where
  Map2Choices '[] = '[]
  Map2Choices (xs ': xss) = MapChoices xs ': Map2Choices xss


class (All KnownNat x, KnownNat (NatProductType x)) => NatProduct x where
  type NatProductType x :: Nat

instance NatProduct '[] where
  type NatProductType '[] = 1

instance (KnownNat x, All KnownNat xs, KnownNat (NatProductType xs)) => NatProduct (x ': xs) where
  type NatProductType (x ': xs) = x GHC.TypeLits.* NatProductType xs
  

type family SumOfProducts (xss :: f (g Nat)) :: Nat where
  SumOfProducts '[] = 0
  SumOfProducts (xs ': xss) = NatProductType xs + SumOfProducts xss


data AppFields :: x -> Exp y

type instance Eval (AppFields x) = Fields x


newtype PF a = PF (ProductType (Fields a))

--------------------------------------------------------------------------------
-- Supporting functions
--------------------------------------------------------------------------------

npMapC :: forall xs . (All MemRep xs) => NP I xs -> NP Finite (MapChoices xs)
npMapC SOP.Nil   = SOP.Nil
npMapC (x :* xs) = choices (unI x) :* npMapC xs


map2choices :: (All2 MemRep xss) => NS (NP I) xss -> NS (NP Finite) (Map2Choices xss)
map2choices (Z x) = Z (npMapC x)
map2choices (S xs) = S (map2choices xs)


combineSumsOfProducts :: (All2 KnownNat xss, All NatProduct xss) => NS (NP Finite) xss -> Finite (SumOfProducts xss)
combineSumsOfProducts (Z y) = combineSum (Left (combineProducts y))
combineSumsOfProducts (S ys) = combineSum (Right (combineSumsOfProducts ys))

npFold :: Product ys -> NP Product xs -> Product (Eval (Foldl (++) ys xs))
npFold acc SOP.Nil   = acc
npFold acc (x :* xs) = npFold (concatP acc x) xs

npFoldT :: ProductType ys -> NP ProductType xs -> ProductType (Eval (Foldl (++) ys xs))
npFoldT acc SOP.Nil   = acc
npFoldT acc (x :* xs) = npFoldT (concatPT acc x) xs

npMapF :: (All MemRep xs) => NP I xs -> NP Product (Eval (Map AppFields xs))
npMapF SOP.Nil   = SOP.Nil
npMapF (x :* xs) = fields (unI x) :* npMapF xs

combineProducts :: (All KnownNat xs) => NP Finite xs -> Finite (NatProductType xs)
combineProducts SOP.Nil = 0
combineProducts (y :* ys) = combineProduct (y, combineProducts ys)

unPF :: PF a -> ProductType (Fields a)
unPF (PF x) = x

convertPureFields :: NP PF xs -> NP ProductType (Eval (Map AppFields xs))
convertPureFields SOP.Nil   = SOP.Nil
convertPureFields (x :* xs) = unPF x :* convertPureFields xs

pureFields :: (All MemRep xs) => NP PF xs
pureFields = cpure_NP (Proxy :: Proxy MemRep) emptyFields'

emptyFields' :: forall x . (MemRep x) => PF x
emptyFields' = PF $ emptyFields @x
