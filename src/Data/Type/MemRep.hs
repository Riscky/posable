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
{-# LANGUAGE NoStarIsType #-}

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
import Data.Finite (Finite, finite)

import Fcf ( Eval, Exp, type (++), Map, type (+))

import qualified Generics.SOP as SOP

import Data.Kind (Type)
import Generics.SOP.NP (cpure_NP)

import GHC.Base (Nat)
import GHC.TypeLits (type (*), natVal, KnownNat)

import Unsafe.Coerce (unsafeCoerce)

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

instance (All2 Show xs) => Show (Product xs) where
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
takeRight (STSucc _ ls) rs = Skip (takeRight ls rs)
takeRight STZero        rs = rs

  -- data SumType :: [Type] -> Type where
  --   STSucc :: x -> SumType xs -> SumType (x ': xs)
  --   STZero :: SumType '[]
  
  -- data Sum :: [Type] -> Type where
  --   Pick :: x -> Sum (x ': xs)
  --   Skip :: Sum xs -> Sum (x ': xs)
  --   Undef :: Sum '[]
  

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

  emptyChoices :: Integer
  default emptyChoices :: (GMemRep (SOP I (Code x))) => Integer
  emptyChoices = gemptyChoices @(SOP I (Code x))

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

  widths :: [Int]

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
class (KnownNat (GChoices x)) =>  GMemRep x where
  type GChoices x :: Nat
  gchoices :: x -> Finite (GChoices x)

  gemptyChoices :: Integer

  type GFields x :: [[Type]]
  gfields :: x -> Product (GFields x)

  gfromMemRep :: Finite (GChoices x) -> Product (GFields x) -> x

  gemptyFields :: ProductType (GFields x)

-----------------------------------------------------------------------
-- Length of typelevel lists

-- adapted Length to lists of lists (sums of products)
type family Length (xs :: [[Type]]) :: Nat where
  Length '[] = 0
  Length (x ': xs) = Eval (1 + Length xs)

-- typesafe version of index_NS, implementation doesn't compile yet
-- stolen from https://hackage.haskell.org/package/sop-core-0.5.0.1/docs/src/Data.SOP.Classes.html#hindex
-- indexNS :: forall f xs x . NS f xs -> Finite (Length xs)
-- indexNS = go (0 :: Finite (Length xs))
--   where
--     go :: forall ys x . Finite x -> NS f ys -> Finite x
--     go !acc (Z _) = acc
--     go !acc (S x) = go (acc + 1) x

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
  type GChoices (SOP I '[ l, r]) = 0 -- TODO Choices l + Choices r
  -- gchoices (SOP (Z ls))     = finite 0
  -- gchoices (SOP (S (Z rs))) = finite (emptyChoices @l)
  -- gchoices (SOP (S (S _))) = error "this is not even possible"

  type GFields (SOP I '[ l, r]) = Eval (Foldl (ZipWith' (++)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ l, r])))))
  gfields (SOP (Z ls))     = zipSumLeft (npFold Nil (npMapF ls)) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))
  gfields (SOP (S (Z rs))) = zipSumRight (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (npMapF rs))
  gfields (SOP (S (S _))) = error "this is not even possible"

  gemptyFields = zipSumT (npFoldT PTNil (convertPureFields (pureFields :: NP PF l))) (npFoldT PTNil (convertPureFields (pureFields :: NP PF r)))


-- generic instance for ternary sums
instance
    ( All MemRep x
    , All MemRep y
    , All MemRep z
    ) => GMemRep (SOP I '[ x, y, z]) where
  type GChoices (SOP I '[ x, y, z]) = 0 -- TODO
  -- gchoices (SOP (Z xs))         = finite 0
  -- gchoices (SOP (S (Z ys)))     = emptyChoices @x
  -- gchoices (SOP (S (S (Z zs)))) = emptyChoices @x + emptyChoices @y
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
  type GChoices (SOP I '[as]) = 1
  -- gchoices _ = finite 0

  type GFields (SOP I '[as]) = Eval (Foldl (++) '[] (Eval (Map AppFields as)))
  gfields (SOP (Z xs)) = npFold Nil (npMapF xs)
  gfields (SOP (S _)) = error "this is not even possible"

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
