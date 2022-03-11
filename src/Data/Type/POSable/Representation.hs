{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | This module exports the `Product` and `Sum` type, and type- and valuelevel
--   functions on these types.
module Data.Type.POSable.Representation
  ( type (++)
  , ProductType(..)
  , concatPT
  , Product(..)
  , concatP
  , SumType(..)
  , Sum(..)
  , Merge
  , FoldMerge
  , MapConcat
  , Concat
  , GroundType(..)
  , zipSumT
  , zipSumLeft
  , zipSumRight
  , splitProductLeft
  , splitProductRight
  , unConcatP
) where
import           Data.Kind
import           Generics.SOP (All, All2)

-- | Concatenation of typelevel lists
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': xs ++ ys

infixr 5 ++

-----------------------------------------------------------------------
-- Ground type class, can be filled by the library's user

class GroundType a where
  type TypeRep a :: Type

  mkTypeRep :: TypeRep a

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types

-- | Type witness for `Product`
data ProductType :: [[Type]] -> Type where
  PTNil :: ProductType '[]
  PTCons :: SumType x -> ProductType xs -> ProductType (x ': xs)

-- instance (All2 Show xs) => Show (ProductType xs) where
--   show PTNil         = "PTNil"
--   show (PTCons a as) = "PTCons " ++ show a ++ " (" ++ show as ++ ")"

-- | Concatenates `ProductType` values
concatPT :: ProductType x -> ProductType y -> ProductType (x ++ y)
concatPT PTNil ys         = ys
concatPT (PTCons x xs) ys = PTCons x (concatPT xs ys)

-- | Typelevel product of `Sum`s with values
data Product :: [[Type]] -> Type where
  Nil :: Product '[]
  Cons :: Sum x -> Product xs -> Product (x ': xs)

deriving instance (All2 Eq xs) => Eq (Product xs)

instance (All2 Show xs) => Show (Product xs) where
  show Nil         = "Nil"
  show (Cons a as) = "Cons " ++ show a ++ " (" ++ show as ++ ")"

-- | Concatenates `Product` values
concatP :: Product x -> Product y -> Product (x ++ y)
concatP Nil         ys = ys
concatP (Cons x xs) ys = Cons x (concatP xs ys)

-- | Type witness for `Sum`
data SumType :: [Type] -> Type where
  STSucc :: (GroundType x) => TypeRep x -> SumType xs -> SumType (x ': xs)
  STZero :: SumType '[]

-- | Typelevel sum, contains one value from the typelevel list of types, or
--   undefined.
data Sum :: [Type] -> Type where
  Pick :: (GroundType x) => x -> Sum (x ': xs)
  Skip :: (GroundType x) => Sum xs -> Sum (x ': xs)
  Undef :: Sum '[]

deriving instance (All Eq xs) => Eq (Sum xs)

type family MapTypeRep (xsss :: f x) :: f y where
  MapTypeRep '[] = '[]
  MapTypeRep (x ': xs) = TypeRep x ': MapTypeRep xs

instance (All Show (MapTypeRep x)) => Show (SumType x) where
  show (STSucc x xs) = "STSucc " ++ show x ++ " (" ++ show xs ++ ")"
  show STZero        = "STZero"

instance (All Show x) => Show (Sum x) where
  show (Pick x) = "Pick " ++ show x
  show (Skip x) = "Skip " ++ show x
  show Undef    = "Undef"

-- only used in examples
data A
data B
data C
data D
data E
data F
data G
data H

----------------------------------------
-- Type functions on lists

-- | Concatenate a list of lists, typelevel equivalent of
--
-- > concat :: [[a]] -> [a]`
--
--    Example:
--
-- >>> :kind! Concat '[ '[A, B], '[C, D]]
-- Concat '[ '[A, B], '[C, D]] :: [Type]
-- = '[A, B, C, D]
--
type family Concat (xss :: f (g x)) :: g x where
  Concat '[] = '[]
  Concat (xs ': xss) = xs ++ Concat xss

-- | Map `Concat` over a list (of lists, of lists), typelevel equivalent of
--
-- > map . concat :: [[[a]]] -> [[a]]
--
--   Example:
--
-- >>> :kind! MapConcat '[ '[ '[A, B], '[C, D]], '[[E, F], '[G, H]]]
-- MapConcat '[ '[ '[A, B], '[C, D]], '[[E, F], '[G, H]]] :: [[Type]]
-- = '[ '[A, B, C, D], '[E, F, G, H]]
--
type family MapConcat (xsss :: f (g (h x))) :: f (h x) where
  MapConcat '[] = '[]
  MapConcat (xss ': xsss) = Concat xss ': MapConcat xsss

-- | Zip two lists of lists with  ++` as operator, while keeping the length of
--   the longest outer list
--
--   Example:
--
-- >>> :kind! Merge '[ '[A, B, C], '[D, E]] '[ '[F, G]]
-- Merge '[ '[A, B, C], '[D, E]] '[ '[F, G]] :: [[Type]]
-- = '[ '[A, B, C, F, G], '[D, E]]
--
type family Merge (xs :: f (g x)) (ys :: g (f x)) :: g (f x) where
  Merge '[] bs = bs
  Merge as '[] = as
  Merge (a ': as) (b ': bs) = (a ++ b) ': Merge as bs

-- | Fold `Merge` over a list (of lists, of lists)
--
--   Example:
--
-- >>> :kind! FoldMerge '[ '[ '[A, B, C], '[D, E]], '[ '[F, G]], '[ '[H]]]
-- FoldMerge '[ '[ '[A, B, C], '[D, E]], '[ '[F, G]], '[ '[H]]] :: [[Type]]
-- = '[ '[A, B, C, F, G, H], '[D, E]]
--
type family FoldMerge (xss :: f (g x)) :: g x where
  FoldMerge '[] = '[]
  FoldMerge (a ': as) = Merge a (FoldMerge as)

----------------------------------------
-- Functions on Products and Sums

-- | Merge a `ProductType` and a `Product`, putting the values of the `Product` in
--   the right argument of `Merge`
zipSumRight :: ProductType l -> Product r -> Product (Merge l r)
zipSumRight (PTCons x xs) (Cons y ys) = Cons (takeRight x y) (zipSumRight xs ys)
zipSumRight PTNil ys                  = ys
zipSumRight xs Nil                    = makeUndefProduct xs

makeUndefProduct :: ProductType x -> Product x
makeUndefProduct (PTCons y ys) = Cons (makeEmpty y) (makeUndefProduct ys)
makeUndefProduct PTNil         = Nil

-- | Merge a `ProductType` and a `Product`, putting the values of the `Product`
--   in the left argument of `Merge`
zipSumLeft :: Product l -> ProductType r -> Product (Merge l r)
zipSumLeft (Cons x xs) (PTCons y ys) = Cons (takeLeft x y) (zipSumLeft xs ys)
zipSumLeft Nil         (PTCons y ys) = Cons (makeEmpty y) (zipSumLeft Nil ys)
zipSumLeft xs          PTNil         = xs

makeEmpty :: SumType xs -> Sum xs
makeEmpty (STSucc _ xs) = Skip (makeEmpty xs)
makeEmpty STZero        = Undef

-- | Merge two `ProductType`s
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

-- | UnMerge a `Product`, using two `ProductType`s as witnesses for the left and
--   right argument of `Merge`. Produces a value of type Product right
splitProductRight :: Product (Merge l r) -> ProductType l -> ProductType r -> Product r
splitProductRight xs PTNil _ = xs
splitProductRight _  _ PTNil = Nil
splitProductRight (Cons x xs) (PTCons l ls) (PTCons r rs) = Cons (splitSumRight x l r) (splitProductRight xs ls rs)

-- | UnMerge a `Product`, using two `ProductType`s as witnesses for the left and
--   right argument of `Merge`. Produces a value of type Product left
splitProductLeft :: Product (Merge l r) -> ProductType l -> ProductType r -> Product l
splitProductLeft _ PTNil _ = Nil
splitProductLeft xs _ PTNil = xs
splitProductLeft (Cons x xs) (PTCons l ls) (PTCons r rs) = Cons (splitSumLeft x l r) (splitProductLeft xs ls rs)

splitSumRight :: Sum (l ++ r) -> SumType l -> SumType r -> Sum r
splitSumRight xs        STZero        _  = xs
splitSumRight (Pick _)  (STSucc _ _)  r  = undefSum r
  where
    undefSum :: SumType x -> Sum x
    undefSum STZero        = Undef
    undefSum (STSucc _ xs) = Skip $ undefSum xs
splitSumRight (Skip xs) (STSucc _ ls) rs = splitSumRight xs ls rs

splitSumLeft :: Sum (l ++ r) -> SumType l -> SumType r -> Sum l
splitSumLeft (Pick x)  (STSucc _ _) _   = Pick x
splitSumLeft _        STZero        _   = Undef -- or error?
splitSumLeft (Skip xs) (STSucc _ ls) rs = Skip $ splitSumLeft xs ls rs

-- | UnConcat a `Product`, using a `ProductType` as the witness for the first
--   argument of `++`. Produces a tuple with the first and second argument of `++`
unConcatP :: Product (x ++ y) -> ProductType x -> (Product x, Product y)
unConcatP xs PTNil                  = (Nil, xs)
unConcatP (Cons x xs) (PTCons _ ts) = (Cons x xs', ys')
  where
    (xs', ys') = unConcatP xs ts
