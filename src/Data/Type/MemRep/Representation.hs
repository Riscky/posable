{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}


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
  , splitSum
  , splitProduct
  , splitProductLeft
  , splitProductRight
  , unConcatP
) where
import           Data.Kind
import           Generics.SOP (All, All2)

import Unsafe.Coerce (unsafeCoerce)

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
  show PTNil         = "PTNil"
  show (PTCons a as) = "PTCons " ++ show a ++ " (" ++ show as ++ ")"

concatPT :: ProductType x -> ProductType y -> ProductType (x ++ y)
concatPT PTNil ys         = ys
concatPT (PTCons x xs) ys = PTCons x (concatPT xs ys)

-- Values
data Product :: [[Type]] -> Type where
  Nil :: Product '[]
  Cons :: Sum x -> Product xs -> Product (x ': xs)

deriving instance (All2 Eq xs) => Eq (Product xs)

instance (All2 Show xs) => Show (Product xs) where
  show Nil         = "Nil"
  show (Cons a as) = "Cons " ++ show a ++ " (" ++ show as ++ ")"

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
  show (STSucc x xs)     = "STSucc " ++ show x ++ " (" ++ show xs ++ ")"
  show STZero            = "STZero"

instance (All Show x) => Show (Sum x) where
  show (Pick x) = "Pick " ++ show x
  show (Skip x) = "Skip " ++ show x
  show Undef    = "Undef"

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
zipSumRight PTNil ys                  = ys
zipSumRight xs Nil                    = makeUndefProduct xs

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
zipSumT PTNil ys                    = ys
zipSumT xs PTNil                    = xs

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

splitProductRight :: Product (Merge l r) -> ProductType l -> ProductType r -> Product r
splitProductRight xs PTNil _ = xs
splitProductRight _  _ PTNil = Nil
splitProductRight (Cons x xs) (PTCons l ls) (PTCons r rs) = Cons (splitSumRight x l r) (splitProductRight xs ls rs)

splitProductLeft :: Product (Merge l r) -> ProductType l -> ProductType r -> Product l
splitProductLeft _ PTNil _ = Nil
splitProductLeft xs _ PTNil = xs
splitProductLeft (Cons x xs) (PTCons l ls) (PTCons r rs) = Cons (splitSumLeft x l r) (splitProductLeft xs ls rs)

splitProduct :: Product (Merge l r) -> ProductType l -> ProductType r -> Either (Product l) (Product r)
splitProduct (Cons x xs) (PTCons l ls) (PTCons r rs) = case splitSum x l r of
  Left l'-> Left $ Cons l' $ splitProductLeft xs ls rs
  Right r' -> Right $ Cons r' $ splitProductRight xs ls rs
splitProduct (Cons x xs) PTNil (PTCons r rs) = case splitSum x STZero r of
  Left _ -> Left Nil
  Right r' -> Right $ Cons r' $ splitProductRight xs PTNil rs
-- unsafe to prevent proving (x ++ '[]) ~ x
splitProduct (Cons x xs) (PTCons l ls) PTNil = case splitSum (unsafeCoerce x) l STZero of
  Left l' -> Left $ Cons l' $ splitProductLeft xs ls PTNil
  Right _ -> Right Nil
splitProduct Nil PTNil PTNil = error "No clue what to do here"

splitSum :: Sum (l ++ r) -> SumType l -> SumType r -> Either (Sum l) (Sum r)
splitSum (Pick x)  (STSucc _ _)  _ = Left (Pick x)
splitSum xs        STZero        _ = Right xs
splitSum (Skip xs) (STSucc _ ls) rs = case splitSum xs ls rs of
  Left l  -> Left (Skip l)
  Right r -> Right r

splitSumRight :: Sum (l ++ r) -> SumType l -> SumType r -> Sum r
splitSumRight xs        STZero        _ = xs
splitSumRight (Pick _)  (STSucc _ _)  _ = error "Value not in Right"
splitSumRight (Skip xs) (STSucc _ ls) rs = splitSumRight xs ls rs

splitSumLeft :: Sum (l ++ r) -> SumType l -> SumType r -> Sum l
splitSumLeft (Pick x)  (STSucc _ _) _  = Pick x
splitSumLeft _        STZero        _  = Undef -- or error?
splitSumLeft (Skip xs) (STSucc _ ls) rs = Skip $ splitSumLeft xs ls rs

unConcatP :: Product (x ++ y) -> ProductType x -> (Product x, Product y)
unConcatP xs PTNil                  = (Nil, xs)
unConcatP (Cons x xs) (PTCons _ ts) = (Cons x xs', ys')
  where
    (xs', ys') = unConcatP xs ts
