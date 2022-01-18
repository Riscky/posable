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
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.Type.MemRep where

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
      Proxy(Proxy),
      to )
import Data.Finite.Internal (Finite)

import Fcf ( Eval, Exp, type (++), Map)

import qualified Generics.SOP as SOP

import Data.Kind (Type)
import Generics.SOP.NP (cpure_NP)

import GHC.Base (Nat)
import GHC.TypeLits (type (+))

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types
data ProductType :: [[Type]] -> Type where
  PTNil :: ProductType '[]
  PTCons :: SumType x -> ProductType xs -> ProductType (x ': xs)

data Product :: [[Type]] -> Type where
  Nil :: Product '[]
  Cons :: Sum x -> Product xs -> Product (x ': xs)

deriving instance (All2 Eq xs) => Eq (Product xs)

instance (All2 Show xs) => Show (ProductType xs) where
  show PTNil = "[]"
  show (PTCons a as) = show a ++ " : " ++ show as

instance (All2 Show xs) =>  Show (Product xs) where
  show Nil = "[]"
  show (Cons a as) = show a ++ " : " ++ show as

-- concat for Products
-- could (should) be a Semigroup instance (<>)
rvconcat :: Product x -> Product y -> Product (Eval (x ++ y))
rvconcat Nil         ys = ys
rvconcat (Cons x xs) ys = Cons x (rvconcat xs ys)

rvconcatT :: ProductType x -> ProductType y -> ProductType (Eval (x ++ y))
rvconcatT PTNil         ys = ys
rvconcatT (PTCons x xs) ys = PTCons x (rvconcatT xs ys)

-- wrap Product in an Exp to use it as an argument to higher order type functions
data AppProduct :: x -> Exp y

type instance Eval (AppProduct x) = Product x

-----------------------------------------------------------------------
-- Typelevel sums with a empty value
data SumType :: [Type] -> Type where
  STSucc :: x -> SumType xs -> SumType (x ': xs)
  STZero :: SumType '[]

data Sum :: [Type] -> Type where
  Pick :: x -> Sum (x ': xs)
  Skip :: Sum xs -> Sum (x ': xs)
  Undef :: Sum '[]

deriving instance (All Eq xs) => Eq (Sum xs)

instance (All Show x) => Show (SumType x) where
  show (STSucc x STZero) = show x
  show (STSucc x xs)     = show x ++ "|" ++ show xs
  show STZero            = "empty"

instance (All Show x) => Show (Sum x) where
  show (Pick x) = show x
  show (Skip x) = show x
  show Undef    = "undefined"

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

-- value level implementation of ZipWith' (++)
-- takes the leftmost Pick that is encountered for each element of the Product

zipSumRight :: ProductType l -> Product r -> Product (Eval (ZipWith' (++) l r))
zipSumRight (PTCons x xs) (Cons y ys) = Cons (takeRight x y) (zipSumRight xs ys)
zipSumRight PTNil ys = ys
zipSumRight xs Nil = makeUndefProduct xs

makeUndefProduct :: ProductType x -> Product x
makeUndefProduct (PTCons y ys) = Cons (makeEmpty y) (makeUndefProduct ys)
makeUndefProduct PTNil         = Nil

zipSumLeft :: Product l -> ProductType r -> Product (Eval (ZipWith' (++) l r))
zipSumLeft (Cons x xs) (PTCons y ys) = Cons (takeLeft x y) (zipSumLeft xs ys)
zipSumLeft Nil         (PTCons y ys) = Cons (makeEmpty y) (zipSumLeft Nil ys)
zipSumLeft xs          PTNil         = xs

makeEmpty :: SumType xs -> Sum xs
makeEmpty (STSucc _ xs) = Skip (makeEmpty xs)
makeEmpty STZero        = Undef

zipSumT :: ProductType l -> ProductType r -> ProductType (Eval (ZipWith' (++) l r))
zipSumT (PTCons x xs) (PTCons y ys) = PTCons (takeST x y) (zipSumT xs ys)
zipSumT PTNil ys = ys
zipSumT xs PTNil = xs

takeST :: SumType l -> SumType r -> SumType (Eval (l ++ r))
takeST (STSucc l ls) rs = STSucc l (takeST ls rs)
takeST STZero        rs = rs

takeLeft :: Sum l -> SumType r -> Sum (Eval (l ++ r))
takeLeft (Pick l)  _  = Pick l
takeLeft (Skip ls) rs = Skip (takeLeft ls rs)
takeLeft Undef     rs = makeEmpty rs

takeRight :: SumType l -> Sum r -> Sum (Eval (l ++ r))
takeRight = undefined

-----------------------------------------------------------------------
-- MemRep, the king of this file
class MemRep x where
  type Choices x :: [[Type]]
  type Choices x = GChoices (SOP I (Code x))

  choices :: x -> Product (Choices x)

  default choices ::
    ( Generic x
    , Choices x ~ GChoices (SOP I (Code x))
    , GMemRep (SOP I (Code x))
    ) => x -> Product (Choices x)
  choices x = gchoices $ from x

  fromMemRep :: Product (Choices x) -> Product (Fields x) -> x

  default fromMemRep ::
    ( Generic x
    , (GMemRep (SOP I (Code x)))
    , Choices x ~ GChoices (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => Product (Choices x) -> Product (Fields x) -> x
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

  widths :: [Int]

  emptyChoices :: ProductType (Choices x)

  default emptyChoices ::
    ( GMemRep (SOP I (Code x))
    , Choices x ~ GChoices (SOP I (Code x))
    ) => ProductType (Choices x)
  emptyChoices = gemptyChoices @(SOP I (Code x))

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
class GMemRep x where
  type GChoices x :: [[Type]]
  gchoices :: x -> Product (GChoices x)

  type GFields x :: [[Type]]
  gfields :: x -> Product (GFields x)

  gfromMemRep :: Product (GChoices x) -> Product (GFields x) -> x

  gemptyChoices :: ProductType (GChoices x)
  gemptyFields :: ProductType (GFields x)

-----------------------------------------------------------------------
-- Length of typelevel lists

-- adapted Length to lists of lists (sums of products)
type family Length (xs :: [[Type]]) :: Nat where
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

npMap :: (All MemRep xs) => NP I xs -> NP Product (Eval (Map AppChoices xs))
npMap SOP.Nil   = SOP.Nil
npMap (x :* xs) = choices (unI x) :* npMap xs

npFold :: Product ys -> NP Product xs -> Product (Eval (Foldl (++) ys xs))
npFold acc SOP.Nil   = acc
npFold acc (x :* xs) = npFold (rvconcat acc x) xs

npFoldT :: ProductType ys -> NP ProductType xs -> ProductType (Eval (Foldl (++) ys xs))
npFoldT acc SOP.Nil   = acc
npFoldT acc (x :* xs) = npFoldT (rvconcatT acc x) xs

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
  type GChoices (SOP I '[ l, r]) =  '[Finite 2] ': Eval (Foldl (ZipWith' (++)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) '[ l, r])))))
  gchoices (SOP (Z ls))     = Cons (Pick 0) (zipSumLeft (npFold Nil (npMap ls)) (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC r))))
  gchoices (SOP (S (Z rs))) = Cons (Pick 1) (zipSumRight (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (npMap rs)))
  gchoices (SOP (S (S _))) = error "this is not even possible"

  type GFields (SOP I '[ l, r]) = Eval (Foldl (ZipWith' (++)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ l, r])))))
  gfields (SOP (Z ls))     = zipSumLeft (npFold Nil (npMapF ls)) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))
  gfields (SOP (S (Z rs))) = zipSumRight (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (npMapF rs))
  gfields (SOP (S (S _))) = error "this is not even possible"

  gemptyChoices = PTCons (STSucc 0 STZero) (zipSumT (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC l))) (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC r))))
  gemptyFields = zipSumT (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))


-- generic instance for ternary sums
instance
    ( All MemRep x
    , All MemRep y
    , All MemRep z
    ) => GMemRep (SOP I '[ x, y, z]) where
  type GChoices (SOP I '[ x, y, z]) = '[Finite 3] ': Eval (Foldl (ZipWith' (++)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) '[ x, y, z])))))
  gchoices (SOP (Z xs))         = Cons (Pick 0) (zipSumLeft (zipSumLeft (npFold Nil (npMap xs)) (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC y)))) (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC z))))
  gchoices (SOP (S (Z ys)))     = Cons (Pick 1) (zipSumLeft (zipSumRight (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC x))) (npFold Nil (npMap ys))) (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC z))))
  gchoices (SOP (S (S (Z zs)))) = Cons (Pick 2) (zipSumRight (zipSumT (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC x))) (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC y)))) (npFold Nil (npMap zs)))
  -- TODO proof that this is not possible
  gchoices (SOP (S (S (S _)))) = error "this is not even possible"

  type GFields (SOP I '[ x, y, z]) = Eval (Foldl (ZipWith' (++)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ x, y, z])))))
  gfields (SOP (Z xs))         = zipSumLeft (zipSumLeft (npFold Nil (npMapF xs)) (npFoldT PTNil (convertPureFields (pureFields :: NP PF y)))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF z)))
  gfields (SOP (S (Z ys)))     = zipSumLeft (zipSumRight (npFoldT PTNil (convertPureFields (pureFields :: NP PF x))) (npFold Nil (npMapF ys))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF z)))
  gfields (SOP (S (S (Z zs)))) = zipSumRight (zipSumT (npFoldT PTNil (convertPureFields (pureFields :: NP PF x))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF y)))) (npFold Nil (npMapF zs))
  gfields (SOP (S (S (S _))))  = error "this is not even possible"

  -- gemptyChoices = Cons (Skip Empty) (zipSumT (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC l))) (npFoldT PTNil (convertPureChoices (pureChoices :: NP PC r))))
  -- gemptyFields = zipSumT (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))


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

  gemptyChoices = npFoldT PTNil (convertPureChoices (pureChoices :: NP PC as))
  gemptyFields = npFoldT PTNil (convertPureFields (pureFields :: NP PF as))

  gfromMemRep cs fs = undefined -- SOP (Z $ generate cs fs (pureChoices :: NP PC as) (pureFields :: NP PF as))

-- convertC :: Product (Eval (Foldl (++) (Choices x) (Eval (Map AppChoices xs)))) -> Product (Choices x FcfM.<> Eval (Foldl (++) '[] (Eval (Map AppChoices xs))))
-- convertC x = undefined

-- convertF :: Product (Eval (Foldl (++) (Fields x) (Eval (Map AppFields xs)))) -> Product (Fields x FcfM.<> Eval (Foldl (++) '[] (Eval (Map AppFields xs))))
-- convertF x = undefined

-- generate :: (All MemRep as) => Product (Eval (Foldl (++) '[] (Eval (Map AppChoices as)))) -> Product (Eval (Foldl (++) '[] (Eval (Map AppFields as)))) -> NP PC as -> NP PF as -> NP I as
-- generate _  _ SOP.Nil   SOP.Nil    = SOP.Nil
-- generate cs fs (x :* xs) (y :* ys) = SOP.I (fromMemRep xc xf) :* generate xcs xfs xs ys
--                                     where
--                                       (xc, xcs) = split (undefined cs) (unPC x) (npFold PTNil (convertPureChoices xs))
--                                       (xf, xfs) = split (undefined fs) (unPF y) (npFold PTNil (convertPureFields ys))

split :: Product (Eval (l ++ r)) -> ProductType l -> ProductType r -> (Product l, Product r)
split (Cons x xs) (PTCons _ ls) rs    = (Cons x ls', rs')
  where
    (ls', rs') = split xs ls rs
split xs          PTNil         _    = (Nil, xs)

splitHorizontal :: Product (Eval (ZipWith' (++) l r)) -> ProductType l -> ProductType r -> (Product l, Product r)
splitHorizontal Nil PTNil         PTNil         = (Nil, Nil)
splitHorizontal x   PTNil         (PTCons _ _) = (Nil, x)
splitHorizontal x   (PTCons _ _)  PTNil         = (x, Nil)
splitHorizontal (Cons x xs) (PTCons l ls) (PTCons r rs) = (Cons l' ls', Cons r' rs')
  where
    (l', r') = splitSum x l r
    (ls', rs') = splitHorizontal xs ls rs

splitSum :: Sum (Eval (l ++ r)) -> SumType l -> SumType r -> (Sum l, Sum r)
splitSum (Pick x)  (STSucc _ _)  rs = (Pick x, makeEmpty rs)
splitSum (Skip xs) (STSucc _ ls) rs = (Skip l', r')
  where
    (l', r') = splitSum xs ls rs
splitSum xs        STZero        _  = (Undef, xs)

-- foldPop :: NP PC xss -> Product (Eval (Foldl (++) '[] (Eval (Map AppChoices yss))))
-- foldPop x = npFold Nil (npMap xinner)

-- functions to generate pure Choices and Fields
newtype PC a = PC (ProductType (Choices a))

unPC :: PC a -> ProductType (Choices a)
unPC (PC x) = x

convertPureChoices :: NP PC xs -> NP ProductType (Eval (Map AppChoices xs))
convertPureChoices SOP.Nil   = SOP.Nil
convertPureChoices (x :* xs) = unPC x :* convertPureChoices xs

pureChoices :: (All MemRep xs) => NP PC xs
pureChoices = cpure_NP (Proxy :: Proxy MemRep) emptyChoices'

emptyChoices' :: forall x . (MemRep x) => PC x
emptyChoices' = PC $ emptyChoices @x

newtype PF a = PF (ProductType (Fields a))

unPF :: PF a -> ProductType (Fields a)
unPF (PF x) = x

convertPureFields :: NP PF xs -> NP ProductType (Eval (Map AppFields xs))
convertPureFields SOP.Nil   = SOP.Nil
convertPureFields (x :* xs) = unPF x :* convertPureFields xs

pureFields :: (All MemRep xs) => NP PF xs
pureFields = cpure_NP (Proxy :: Proxy MemRep) emptyFields'

emptyFields' :: forall x . (MemRep x) => PF x
emptyFields' = PF $ emptyFields @x
