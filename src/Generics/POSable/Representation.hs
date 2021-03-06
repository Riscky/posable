{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | This module exports the `Product` and `Sum` type, and type- and valuelevel
--   functions on these types.
module Generics.POSable.Representation
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
  , Ground(..)
  , mergeT
  , merge
  , splitLeft
  , splitRight
  , unConcatP
  , Undef(..)
) where
import           Data.Kind
import           Data.Typeable (Typeable)
import           GHC.Generics  as GHC
import           Generics.SOP  as SOP (All, All2, Generic)

-- | Concatenation of typelevel lists
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': xs ++ ys

infixr 5 ++


-- | The set of types that can exist in the sums.
--   This set can be extended by the user by providing an instance of Ground
--   for their types. The mkGround function gives a default value for the type.
--   Ground depends on Typeable, as this makes it possible for library users
--   to inspect the types of the contents of the sums.
class (Typeable a) => Ground a where
  mkGround :: a

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types

-- | Type witness for `Product`
data ProductType :: [[Type]] -> Type where
  PTNil :: ProductType '[]
  PTCons :: SumType x -> ProductType xs -> ProductType (x ': xs)

instance (All2 Show (Map2TypeRep xs)) => Show (ProductType xs) where
  show PTNil         = "PTNil"
  show (PTCons a as) = "PTCons" ++ show a ++ " (" ++ show as ++ ")"

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
  STSucc :: (Ground x) => x -> SumType xs -> SumType (x ': xs)
  STZero :: SumType '[]

-- | Typelevel sum, contains one value from the typelevel list of types, or
--   undefined.
data Sum :: [Type] -> Type where
  Pick :: (Ground x) => x -> Sum (x ': xs)
  Skip :: (Ground x) => Sum xs -> Sum (x ': xs)

data Undef = Undef
  deriving (Eq, Show, GHC.Generic, SOP.Generic)

-- Undef is the only default Ground, because we need to mark when no value
-- is when 2 non-equal-lenght types are zipped
instance Ground Undef where
  mkGround = Undef

deriving instance (All Eq xs) => Eq (Sum xs)

type family MapTypeRep (xs :: [Type]) :: [Type] where
  MapTypeRep '[] = '[]
  MapTypeRep (x ': xs) = x ': MapTypeRep xs

type family Map2TypeRep (xss :: [[Type]]) :: [[Type]] where
  Map2TypeRep '[] = '[]
  Map2TypeRep (x ': xs) = MapTypeRep x ': Map2TypeRep xs

instance (All Show (MapTypeRep xs)) => Show (SumType xs) where
  show (STSucc x xs) = "STSucc" ++ show x ++ "(" ++ show xs ++ ")"
  show STZero        = "STZero"

instance (All Show x) => Show (Sum x) where
  show (Pick x) = "Pick " ++ show x
  show (Skip x) = "Skip " ++ show x

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
type family Concat (xss :: [[x]]) :: [x] where
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
type family MapConcat (xsss :: [[[x]]]) :: [[x]] where
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
type family Merge (xs :: [[Type]]) (ys :: [[Type]]) :: [[Type]] where
  Merge '[] '[] = '[]
  Merge '[] (b ': bs) = (Undef ': b) ': Merge '[] bs
  Merge (a ': as) '[] = (a ++ '[Undef]) ': Merge as '[]
  Merge (a ': as) (b ': bs) = (a ++ b) ': Merge as bs

-- | Fold `Merge` over a list (of lists, of lists)
--
--   Example:
--
-- >>> :kind! FoldMerge '[ '[ '[A, B, C], '[D, E]], '[ '[F, G]], '[ '[H]]]
-- FoldMerge '[ '[ '[A, B, C], '[D, E]], '[ '[F, G]], '[ '[H]]] :: [[Type]]
-- = '[ '[A, B, C, F, G, H], '[D, E]]
--
type family FoldMerge (xss :: [[[Type]]]) :: [[Type]] where
  FoldMerge '[a] = a
  FoldMerge (a ': as) = Merge a (FoldMerge as)
  FoldMerge '[] = '[]

----------------------------------------
-- Functions on Products and Sums

-- | Merge a `ProductType` and a `Product`, putting the values of the `Product` in
--   the right argument of `Merge`
zipSumRight :: ProductType l -> Product r -> Product (Merge l r)
zipSumRight PTNil         Nil         = Nil
zipSumRight PTNil         (Cons y ys) = Cons (takeRightUndef y) (zipSumRight PTNil ys)
zipSumRight (PTCons x xs) Nil         = Cons (makeUndefRight x) (zipSumRight xs Nil)
zipSumRight (PTCons x xs) (Cons y ys) = Cons (takeRight x y) (zipSumRight xs ys)

makeUndefRight :: SumType x -> Sum (x ++ '[Undef])
makeUndefRight (STSucc _ xs) = Skip (makeUndefRight xs)
makeUndefRight STZero        = Pick Undef

makeUndefLeft :: SumType x -> Sum (Undef ': x)
makeUndefLeft _ = Pick Undef

takeRightUndef :: Sum r -> Sum (Undef ': r)
takeRightUndef = Skip

takeLeftUndef :: Sum x -> Sum (x ++ '[Undef])
takeLeftUndef (Pick x)  = Pick x
takeLeftUndef (Skip xs) = Skip (takeLeftUndef xs)

-- | Merge a `ProductType` and a `Product`
merge :: Either (Product l, ProductType r) (ProductType l, Product r) -> Product (Merge l r)
merge (Left (l, r))  = zipSumLeft l r
merge (Right (l, r)) = zipSumRight l r

-- | Merge a `ProductType` and a `Product`, putting the values of the `Product`
--   in the left argument of `Merge`
zipSumLeft :: Product l -> ProductType r -> Product (Merge l r)
zipSumLeft Nil         PTNil         = Nil
zipSumLeft Nil         (PTCons y ys) = Cons (makeUndefLeft y) (zipSumLeft Nil ys)
zipSumLeft (Cons x xs) PTNil         = Cons (takeLeftUndef x) (zipSumLeft xs PTNil)
zipSumLeft (Cons x xs) (PTCons y ys) = Cons (takeLeft x y) (zipSumLeft xs ys)

-- | Merge two `ProductType`s
mergeT :: ProductType l -> ProductType r -> ProductType (Merge l r)
mergeT PTNil PTNil                 = PTNil
mergeT PTNil (PTCons y ys)         = PTCons (makeUndefLeftT y) (mergeT PTNil ys)
mergeT (PTCons x xs) PTNil         = PTCons (makeUndefRightT x) (mergeT xs PTNil)
mergeT (PTCons x xs) (PTCons y ys) = PTCons (takeST x y) (mergeT xs ys)

makeUndefRightT :: SumType x -> SumType (x ++ '[Undef])
makeUndefRightT (STSucc x xs) = STSucc x (makeUndefRightT xs)
makeUndefRightT STZero        = STSucc Undef STZero

makeUndefLeftT :: SumType x -> SumType (Undef ': x)
makeUndefLeftT = STSucc Undef

takeST :: SumType l -> SumType r -> SumType (l ++ r)
takeST (STSucc l ls) rs = STSucc l (takeST ls rs)
takeST STZero        rs = rs

takeLeft :: Sum l -> SumType r -> Sum (l ++ r)
takeLeft (Pick l)  _  = Pick l
takeLeft (Skip ls) rs = Skip (takeLeft ls rs)

takeRight :: SumType l -> Sum r -> Sum (l ++ r)
takeRight (STSucc _ ls) rs = Skip (takeRight ls rs)
takeRight STZero        rs = rs

-- | UnMerge a `Product`, using two `ProductType`s as witnesses for the left and
--   right argument of `Merge`. Produces a value of type Product right
splitRight :: Product (Merge l r) -> ProductType l -> ProductType r -> Product r
splitRight (Cons x xs) PTNil (PTCons _ rs) = Cons (removeUndefLeft x) (splitRight xs PTNil rs)
splitRight _  _ PTNil = Nil
splitRight (Cons x xs) (PTCons l ls) (PTCons r rs) = Cons (splitSumRight x l r) (splitRight xs ls rs)

removeUndefLeft :: Sum (Undef ': x) -> Sum x
removeUndefLeft (Pick Undef) = error "Undefined value where I expected an actual value"
removeUndefLeft (Skip xs)    = xs

removeUndefRight :: SumType x -> Sum (x ++ '[Undef]) -> Sum x
removeUndefRight STZero        _            = error "Undefined value where I expected an actual value"
removeUndefRight (STSucc _ _)  (Pick y)     = Pick y
removeUndefRight (STSucc _ xs) (Skip ys) = Skip (removeUndefRight xs ys)

-- | UnMerge a `Product`, using two `ProductType`s as witnesses for the left and
--   right argument of `Merge`. Produces a value of type Product left
splitLeft :: Product (Merge l r) -> ProductType l -> ProductType r -> Product l
splitLeft _ PTNil _ = Nil
splitLeft (Cons x xs) (PTCons l ls) PTNil = Cons (removeUndefRight l x) (splitLeft xs ls PTNil)
splitLeft (Cons x xs) (PTCons l ls) (PTCons r rs) = Cons (splitSumLeft x l r) (splitLeft xs ls rs)

splitSumRight :: Sum (l ++ r) -> SumType l -> SumType r -> Sum r
splitSumRight xs        STZero        _  = xs
splitSumRight (Pick _)  (STSucc _ _)  _  = error "No value found in right side of Sum"
splitSumRight (Skip xs) (STSucc _ ls) rs = splitSumRight xs ls rs

splitSumLeft :: Sum (l ++ r) -> SumType l -> SumType r -> Sum l
splitSumLeft (Pick x)  (STSucc _ _) _   = Pick x
splitSumLeft _        STZero        _   = error "No value value found in left side of Sum"
splitSumLeft (Skip xs) (STSucc _ ls) rs = Skip $ splitSumLeft xs ls rs

-- | UnConcat a `Product`, using a `ProductType` as the witness for the first
--   argument of `++`. Produces a tuple with the first and second argument of `++`
unConcatP :: Product (x ++ y) -> ProductType x -> (Product x, Product y)
unConcatP xs PTNil                  = (Nil, xs)
unConcatP (Cons x xs) (PTCons _ ts) = (Cons x xs', ys')
  where
    (xs', ys') = unConcatP xs ts
