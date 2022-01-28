{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}


module Data.Type.MemRep.Representation where

import Fcf ( Eval, Exp, type (++))
import Generics.SOP (All, All2)
import Data.Kind

import Unsafe.Coerce (unsafeCoerce)

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types

-- Types without values
data ProductType :: [[Type]] -> Type where
  PTNil :: ProductType '[]
  PTCons :: SumType x -> ProductType xs -> ProductType (x ': xs)

instance (All2 Show xs) => Show (ProductType xs) where
  show PTNil = "[]"
  show (PTCons a as) = show a ++ " : " ++ show as

concatPT :: ProductType x -> ProductType y -> ProductType (Eval (x ++ y))
concatPT PTNil ys = ys
concatPT (PTCons x xs) ys = PTCons x (concatPT xs ys)

-- Values
data Product :: [[Type]] -> Type where
  Nil :: Product '[]
  Cons :: Sum x -> Product xs -> Product (x ': xs)

deriving instance (All2 Eq xs) => Eq (Product xs)

instance (All2 Show xs) => Show (Product xs) where
  show Nil = "[]"
  show (Cons a as) = show a ++ " : " ++ show as

concatP :: Product x -> Product y -> Product (Eval (x ++ y))
concatP Nil         ys = ys
concatP (Cons x xs) ys = Cons x (concatP xs ys)


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

----------------------------------------
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

-- from https://hackage.haskell.org/package/first-class-families-0.8.0.1/docs/src/Fcf.Class.Foldable.html#Foldr
-- why use this instead of FoldR?
-- because this matches the way Fcf.<> works, so I don't have to prove that it is associative
data Foldl :: (a -> b -> Exp b) -> b -> t a -> Exp b

type instance Eval (Foldl f y '[]) = y
type instance Eval (Foldl f y (x ': xs)) = Eval (Foldl f (Eval (f y x)) xs)


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
takeRight (STSucc _ ls) rs = Skip (takeRight ls rs)
takeRight STZero        rs = rs

split :: Product (Eval (l ++ r)) -> ProductType l -> ProductType r -> (Product l, Product r)
split (Cons x xs) (PTCons _ ls) rs = (Cons x ls', rs')
  where
    (ls', rs') = split xs ls rs
split xs PTNil _ = (Nil, xs)

split3 :: Product (Eval (Eval (x ++ y) ++ z)) -> ProductType x -> ProductType y -> ProductType z -> (Product x, (Product y, Product z))
split3 (Cons a as) (PTCons _ xs) ys zs = (Cons a xs', yz)
  where
    (xs', yz) = split3 as xs ys zs
split3 as PTNil ys zs = (Nil, split as ys zs)

-- Using unsafeCoerce because I can't get the typechecker to understand Foldl
splits :: Product (Eval (Foldl (++) '[] xs)) -> ProductTypes xs -> Products xs
splits (Cons x xs) (PSTCons (PTCons _ ys) yss) = unsafeCoerce $ PSCons (Cons x xs') ys'
  where
    PSCons xs' ys' = splits (unsafeCoerce xs) (PSTCons ys yss)
splits xs          (PSTCons PTNil yss)         = PSCons Nil (splits xs yss)
splits Nil         PSTNil                      = PSNil
splits Nil         (PSTCons (PTCons _ _) _) = error "types are not equivalent"

data ProductTypes :: [[[Type]]] -> Type where
  PSTCons :: ProductType x -> ProductTypes xs -> ProductTypes (x ': xs)
  PSTNil  :: ProductTypes '[]

data Products :: [[[Type]]] -> Type where
  PSCons :: Product x -> Products xs -> Products (x ': xs)
  PSNil  :: Products '[]

splitHorizontal :: Product (Eval (ZipWith' (++) l r)) -> ProductType l -> ProductType r -> (Product l, Product r)
splitHorizontal Nil PTNil         PTNil         = (Nil, Nil)
splitHorizontal x   PTNil         (PTCons _ _) = (Nil, x)
splitHorizontal x   (PTCons _ _)  PTNil         = (x, Nil)
splitHorizontal (Cons x xs) (PTCons l ls) (PTCons r rs) = (Cons l' ls', Cons r' rs')
  where
    (l', r') = splitSum x l r
    (ls', rs') = splitHorizontal xs ls rs

splitHorizontal3 :: Product (Eval (ZipWith' (++) (Eval (ZipWith' (++) x y)) z)) -> ProductType x -> ProductType y -> ProductType z -> (Product x, Product y, Product z)
splitHorizontal3 Nil PTNil         PTNil         PTNil         = (Nil, Nil, Nil)
splitHorizontal3 a   (PTCons _ _)  PTNil         PTNil         = (a, Nil, Nil)
splitHorizontal3 a   PTNil         (PTCons _ _)  PTNil         = (Nil, a, Nil)
splitHorizontal3 a   PTNil         PTNil         (PTCons _ _ ) = (Nil, Nil, a)
splitHorizontal3 a   x             y             PTNil         = (x', y', Nil)
  where
    (x', y') = splitHorizontal a x y
splitHorizontal3 a   x             PTNil         z             = (x', Nil, z')
  where
    (x', z') = splitHorizontal a x z
splitHorizontal3 a   PTNil         y             z             = (Nil, y', z')
  where
    (y', z') = splitHorizontal a y z
splitHorizontal3 (Cons a as) (PTCons x xs) (PTCons y ys) (PTCons z zs) = (Cons x' xs', Cons y' ys', Cons z' zs')
  where
    (x', y', z') = splitSum3 a x y z
    (xs', ys', zs') = splitHorizontal3 as xs ys zs

splitSum :: Sum (Eval (l ++ r)) -> SumType l -> SumType r -> (Sum l, Sum r)
splitSum (Pick x)  (STSucc _ _)  rs = (Pick x, makeEmpty rs)
splitSum (Skip xs) (STSucc _ ls) rs = (Skip l', r')
  where
    (l', r') = splitSum xs ls rs
splitSum xs        STZero        _  = (Undef, xs)

splitSum3 :: Sum (Eval (Eval (x ++ y) ++ z)) -> SumType x -> SumType y -> SumType z -> (Sum x, Sum y, Sum z)
splitSum3 (Pick a)  (STSucc _ _)  ys zs = (Pick a, makeEmpty ys, makeEmpty zs)
splitSum3 as        STZero        ys zs  = (Undef, ys', zs')
  where
    (ys', zs') = splitSum as ys zs
splitSum3 (Skip as) (STSucc _ xs) ys zs = (Skip xs', ys', zs')
  where
    (xs', ys', zs') = splitSum3 as xs ys zs
