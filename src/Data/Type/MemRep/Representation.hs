{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}


module Data.Type.MemRep.Representation
  ( type (++)
  , ProductType(..)
  , concatPT
  , Product(..)
  , concatP
  , SumType(..)
  , Sum(..)
  , Merge
  , FoldMerge
  , MapAppends
  , Appends
  , zipSumT
  , zipSumLeft
  , zipSumRight
) where
import Generics.SOP (All, All2)
import Data.Kind

infixr 5 ++
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': xs ++ ys

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types

-- Types without values
data ProductType :: [[Type]] -> Type where
  PTNil :: ProductType '[]
  PTCons :: SumType x -> ProductType xs -> ProductType (x ': xs)

instance (All2 Show xs) => Show (ProductType xs) where
  show PTNil = "[]"
  show (PTCons a as) = show a ++ " : " ++ show as

concatPT :: ProductType x -> ProductType y -> ProductType (x ++ y)
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

concatP :: Product x -> Product y -> Product (x ++ y)
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
-- Type functions on lists

type family Appends (xss :: f (g x)) :: g x where
  Appends '[] = '[]
  Appends (xs ': xss) = xs ++ Appends xss

type family MapAppends (xsss :: f (g (h x))) :: f (h x) where
  MapAppends '[] = '[]
  MapAppends (xss ': xsss) = Appends xss ': MapAppends xsss

type family Merge (xs :: f x) (ys :: f y) :: f z where
  Merge '[] bs = bs
  Merge as '[] = as
  Merge (a ': as) (b ': bs) = (a ++ b) ': Merge as bs

type family FoldMerge (xss :: f (g x)) :: g x where
  FoldMerge '[] = '[]
  FoldMerge (a ': as) = Merge a (FoldMerge as)

----------------------------------------
-- Functions on Products and Sums

zipSumRight :: ProductType l -> Product r -> Product (Merge l r)
zipSumRight (PTCons x xs) (Cons y ys) = Cons (takeRight x y) (zipSumRight xs ys)
zipSumRight PTNil ys = ys
zipSumRight xs Nil = makeUndefProduct xs

makeUndefProduct :: ProductType x -> Product x
makeUndefProduct (PTCons y ys) = Cons (makeEmpty y) (makeUndefProduct ys)
makeUndefProduct PTNil         = Nil

zipSumLeft :: Product l -> ProductType r -> Product (Merge l r)
zipSumLeft (Cons x xs) (PTCons y ys) = Cons (takeLeft x y) (zipSumLeft xs ys)
zipSumLeft Nil         (PTCons y ys) = Cons (makeEmpty y) (zipSumLeft Nil ys)
zipSumLeft xs          PTNil         = xs

makeEmpty :: SumType xs -> Sum xs
makeEmpty (STSucc _ xs) = Skip (makeEmpty xs)
makeEmpty STZero        = Undef

zipSumT :: ProductType l -> ProductType r -> ProductType (Merge l r)
zipSumT (PTCons x xs) (PTCons y ys) = PTCons (takeST x y) (zipSumT xs ys)
zipSumT PTNil ys = ys
zipSumT xs PTNil = xs

takeST :: SumType l -> SumType r -> SumType (l ++ r)
takeST (STSucc l ls) rs = STSucc l (takeST ls rs)
takeST STZero        rs = rs

takeLeft :: Sum l -> SumType r -> Sum (l ++ r)
takeLeft (Pick l)  _  = Pick l
takeLeft (Skip ls) rs = Skip (takeLeft ls rs)
takeLeft Undef     rs = makeEmpty rs

takeRight :: SumType l -> Sum r -> Sum (l ++ r)
takeRight (STSucc _ ls) rs = Skip (takeRight ls rs)
takeRight STZero        rs = rs
