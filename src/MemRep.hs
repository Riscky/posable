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
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module MemRep where

import Generics.SOP
    ( All,
      All2,
      Code,
      Generic,
      All,
      All2,
      Code,
      Generic,
      I(I),
      SOP(SOP),
      NS(Z, S),
      NP((:*)),
      from, unI, hliftA, K (K), hliftA2, HPure (hpure, hcpure), Prod, HAp (hap), fn, type (-.->), HIndex (hindex), POP, Proxy (Proxy), HExpand (hexpand), mapIK, unSOP, Top, SListI, unPOP )
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Finite.Internal (Finite, finite)

import Fcf ( Eval, Exp, type (++), Map, Foldr, type (<*>), type (=<<), type (<=<), type (<$>), Pure)

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP

import Data.Kind
import Generics.SOP.NP (collapse_NP, map_NP, pure_POP, liftA_NP, cpure_POP, cpure_NP)
import Generics.SOP.Classes (hliftA2, HPure (hpure))
import Generics.SOP.Constraint (SListIN)

import Data.Type.Equality ( gcastWith, type (:~:)(..), sym )
import qualified Fcf.Class.Monoid as FcfM
import GHC.Base (Nat)
import GHC.TypeLits (type (+))
import Generics.SOP.NS (index_NS, ap_SOP, expand_SOP, liftA_NS, unSOP, liftA_SOP)

-----------------------------------------------------------------------
-- Heterogeneous lists with explicit types
data Product xs where
  Nil :: Product '[]
  Cons :: (x ~ Sum a) => x -> Product ys -> Product (x ': ys)

instance (All Show xs) =>  Show (Product xs) where
  show Nil = "[]"
  show (Cons a as) = show a ++ " : " ++ show as

-- concat for Products
-- could (should) be a Semigroup instance (<>)
rvconcat :: Product x -> Product y -> Product (Eval (x ++ y))
rvconcat Nil         ys = ys
rvconcat (Cons x xs) ys = Cons x (rvconcat xs ys)

-----------------------------------------------------------------------
-- Typelevel sums with a empty value
-- TODO: naming
-- The semantics of this thing is: first Pick is relevant value, if there
-- are more Pick they can be replaced by Skips
data Sum :: [*] -> * where
  Pick :: x -> Remainder xs -> Sum (x ': xs)
  Skip :: Sum xs -> Sum (x ': xs)
  Empty :: Sum '[]

data Remainder :: [*] -> * where
  Succ :: Remainder xs -> Remainder (x ': xs)
  Zero  :: Remainder '[]

instance (All Show x) => Show (Sum x) where
  show (Pick x xs) = show x
  show (Skip x)    = show x
  show Empty       = "Ø"

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


-- we probably need injective type families here: https://gitlab.haskell.org/ghc/ghc/-/wikis/injective-type-families
type family ZipSums (as :: [a]) (bs :: [b]) :: [c] where
  ZipSums '[]        bs       = bs
  ZipSums as        '[]       = as
  ZipSums (a ': as) (b ': bs) = a </> b ': ZipSums as bs

data (<>) :: * -> * -> Exp *

type instance Eval ((<>) x y) = x </> y

-- Type level append of Sum's
-- We might want to use the correct operator here, but for now this works well enough
type family (a :: *) </> (b :: *) :: * where
  Sum a </> Sum b = Sum (Eval (a ++ b))

-- value level implementation of ZipWith' (<>)
-- takes the leftmost zip that is encountered
zipSum :: Product l -> Product r -> Product (Eval (ZipWith' (<>) l r))
zipSum (Cons (x :: Sum a) xs) (Cons (y :: b) ys) = Cons (takeS x y) (zipSum xs ys)
zipSum Nil ys = ys
zipSum xs Nil = xs

-- return leftmost Pick or Empty if no Pick is found
takeS :: Sum l -> Sum r -> Sum (Eval (l ++ r))
takeS (Pick l ls) r = Pick l (takeS' ls r)
takeS (Skip ls)   r = Skip (takeS ls r)
takeS Empty       r = r

takeS' :: Remainder l -> Sum r -> Remainder (Eval (l ++ r))
takeS' (Succ ls) r           = Succ (takeS' ls r)
takeS' Zero      Empty       = Zero
takeS' Zero      (Skip rs)   = Succ (takeS' Zero rs)
takeS' Zero      (Pick r rs) = Succ (takeS'' Zero rs)

takeS'' :: Remainder l -> Remainder r -> Remainder (Eval (l ++ r))
takeS'' (Succ ls) r = Succ (takeS'' ls r)
takeS'' Zero      r = r

-----------------------------------------------------------------------
-- MemRep, the king of this file
class MemRep x where
  type Choices x :: [*]
  type Choices x = GChoices (SOP I (Code x))

  choices :: x -> Product (Choices x)

  default choices ::
    ( Generic x
    , Choices x ~ GChoices (SOP I (Code x))
    , GMemRep (SOP I (Code x))
    ) => x -> Product (Choices x)
  choices x = gchoices $ from x

  type Fields x :: [*]
  type Fields x = GFields (SOP I (Code x))

  fields :: x -> Product (Fields x)

  default fields ::
    ( Generic x
    , Fields x ~ GFields (SOP I (Code x))
    , GMemRep (SOP I (Code x))
    ) => x -> Product (Fields x)
  fields x = gfields $ from x

  widths :: [Int]

  emptyChoices :: Product (Choices x)

  default emptyChoices ::
    ( GMemRep (SOP I (Code x))
    , Choices x ~ GChoices (SOP I (Code x))
    ) => Product (Choices x)
  emptyChoices = gemptyChoices @ (SOP I (Code x))

  emptyFields :: Product (Fields x)

  default emptyFields ::
    ( GMemRep (SOP I (Code x))
    , Fields x ~ GFields (SOP I (Code x))
    ) => Product (Fields x)
  emptyFields  = gemptyFields @ (SOP I (Code x))

------------------------------------------------------------------------
-- Some types to gain understanding of MemRep instances for more complex
-- types

data Direction l m r = Lef l
                     | Mid m
                     | Rig r

data Mult a b c d = Fst a b
                  | Snd c d

-----------------------------------------------------------------------
-- Instances of MemRep for machine types

-- Sadly, this definition does not work but gives the following error:
-- 'Conflicting family instance declarations'
-- as soon as any other instance of Choices or Fields is declared
-- This is related to this GHC issue: https://gitlab.haskell.org/ghc/ghc/-/issues/4259
-- and won't be fixed very soon probably

-- instance Base x => MemRep x where
--   type Choices x = '[]
--   choices x = Nil

--   type Fields x = '[Sum '[x]]
--   mtfields x = Cons (Pick x) Nil

-- Instead, we have to do with a seperate definition per base type, which leads
-- to a horrible amount of boilerplate.
-- This is fixable with some Template Haskell, but let's not go there now.
instance MemRep Int where
  type Choices Int = '[]
  choices _ = Nil

  type Fields Int = '[Sum '[Int]]
  fields x = Cons (Pick x Zero) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance MemRep Float where
  type Choices Float = '[]
  choices _ = Nil

  type Fields Float = '[Sum '[Float]]
  fields x = Cons (Pick x Zero) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance MemRep Int8 where
  type Choices Int8 = '[]
  choices _ = Nil

  type Fields Int8 = '[Sum '[Int8]]
  fields x = Cons (Pick x Zero) Nil

  widths = [8]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

instance MemRep Int16 where
  type Choices Int16 = '[]
  choices _ = Nil

  type Fields Int16 = '[Sum '[Int16]]
  fields x = Cons (Pick x Zero) Nil

  widths = [16]

  emptyChoices = Nil
  emptyFields = Cons (Skip Empty) Nil

-----------------------------------------------------------------------
-- Instances of MemRep that should be generically derived in the future

-- Instance for Boolean
instance MemRep Bool where
  type Choices Bool = '[Sum '[Finite 2]]
  choices False = Cons (Pick 0 Zero) Nil
  choices True  = Cons (Pick 1 Zero) Nil

  type Fields Bool = '[]
  fields _ = Nil

  widths = []

  emptyChoices = Cons (Skip Empty) Nil
  emptyFields  = Nil

-- Instance for Maybe
instance (MemRep a) => MemRep (Maybe a) where
  type Choices (Maybe a) = Sum '[Finite 2] ': Choices a
  choices Nothing  = Cons (Pick 0 Zero) (emptyChoices @ a)
  choices (Just x) = Cons (Pick 1 Zero) (choices x)

  type Fields (Maybe a) = Fields a
  fields Nothing  = emptyFields @ a
  fields (Just x) = fields x

  widths = widths @ a

  emptyChoices = Cons (Skip Empty) (emptyChoices @ a)
  emptyFields  = emptyFields @ a

-- Instance for Either, recursively defined
instance (MemRep l, MemRep r) => MemRep (Either l r) where
  type Choices (Either l r) = Sum '[Finite 2] ': Eval (ZipWith' (<>) (Choices l) (Choices r))
  choices (Left lv)  = Cons (Pick 0 Zero) (zipSum (choices lv) (emptyChoices @ r))
  choices (Right rv) = Cons (Pick 1 Zero) (zipSum (emptyChoices @ l) (choices rv))

  type Fields (Either l r) = Eval (ZipWith' (<>) (Fields l) (Fields r))
  fields (Left lv)  = zipSum (fields lv) (emptyFields @ r)
  fields (Right rv) = zipSum (emptyFields @ l) (fields rv)

  widths = zipWith max (widths @ l) (widths @ r)

  emptyChoices = Cons (Skip Empty) (zipSum (emptyChoices @ l) (emptyChoices @ r))
  emptyFields = zipSum (emptyFields @ l) (emptyFields @ r)

-- Instance for Direction type
instance
    ( MemRep l
    , MemRep m
    , MemRep r)
    => MemRep (Direction l m r) where
  type Choices (Direction l m r) = Sum '[Finite 3] ': Eval (ZipWith' (<>) (Choices l) (Eval (ZipWith' (<>) (Choices m) (Choices r))))
  choices (Lef lv) = Cons (Pick 0 Zero) (zipSum  (choices lv)       (zipSum  (emptyChoices @ m) (emptyChoices @ r)))
  choices (Mid mv) = Cons (Pick 1 Zero) (zipSum (emptyChoices @ l) (zipSum  (choices mv)       (emptyChoices @ r)))
  choices (Rig rv) = Cons (Pick 2 Zero) (zipSum (emptyChoices @ l) (zipSum (emptyChoices @ m) (choices rv)))

  type Fields (Direction l m r) = Eval (ZipWith' (<>) (Fields l) (Eval (ZipWith' (<>) (Fields m) (Fields r))))
  fields (Lef lv) = zipSum  (fields lv)       (zipSum  (emptyFields @ m) (emptyFields @ r))
  fields (Mid mv) = zipSum (emptyFields @ l) (zipSum  (fields mv)       (emptyFields @ r))
  fields (Rig rv) = zipSum (emptyFields @ l) (zipSum (emptyFields @ m) (fields rv))

  widths = zipWith max (widths @ l) (zipWith max (widths @ m) (widths @ r))

  emptyChoices = Cons (Skip Empty) (zipSum (emptyChoices @ l) (zipSum (emptyChoices @ m) (emptyChoices @ r)))
  emptyFields = zipSum (emptyFields @ l) (zipSum (emptyFields @ m) (emptyFields @ r))


-- Instance for Mult type
instance
    ( MemRep a
    , MemRep b
    , MemRep c
    , MemRep d)
    => MemRep (Mult a b c d) where
  type Choices (Mult a b c d) = Sum '[Finite 2] ': Eval (ZipWith' (<>) (Eval (Choices a ++ Choices b)) (Eval (Choices c ++ Choices d)))
  choices (Fst av bv) = Cons (Pick 0 Zero) (zipSum (rvconcat (choices av) (choices bv)) (rvconcat (emptyChoices @ c) (emptyChoices @ d)))
  choices (Snd cv dv) = Cons (Pick 1 Zero) (zipSum (rvconcat (emptyChoices @ a) (emptyChoices @ b)) (rvconcat (choices cv) (choices dv)))

  type Fields (Mult a b c d) = Eval (ZipWith' (<>) (Eval (Fields a ++ Fields b)) (Eval (Fields c ++ Fields d)))
  fields (Fst av bv) = zipSum (rvconcat (fields av) (fields bv)) (rvconcat (emptyFields @ c) (emptyFields @ d))
  fields (Snd cv dv) = zipSum (rvconcat (emptyFields @ a) (emptyFields @ b)) (rvconcat (fields cv) (fields dv))

  widths = zipWith max (widths @ a ++ widths @ b) (widths @ c ++ widths @ d)

  emptyChoices = Cons (Skip Empty) (zipSum (rvconcat (emptyChoices @ a) (emptyChoices @ b)) (rvconcat (emptyChoices @ c) (emptyChoices @ d)))
  emptyFields = zipSum (rvconcat (emptyFields @ a) (emptyFields @ b)) (rvconcat (emptyFields @ c) (emptyFields @ d))

-- Instance for product types (tuples)
-- Recursively defined, because concatenation is a whole lot easier then zipWith (++)
instance (MemRep x, MemRep y) => MemRep (x, y) where
  type Choices (x,y) = Eval (Choices x ++ Choices y)
  choices (x,y) = rvconcat (choices x) (choices y)

  type Fields (x, y) = Eval (Fields x ++ Fields y)
  fields (x,y) = rvconcat (fields x) (fields y)

  widths = widths @ x ++ widths @ y

  emptyChoices = rvconcat (emptyChoices @ x) (emptyChoices @ y)
  emptyFields = rvconcat (emptyFields @ x) (emptyFields @ y)

-- Instance for 3-tuples
instance (MemRep x, MemRep y, MemRep z) => MemRep (x, y, z) where
  type Choices (x,y,z) = Eval (Choices x ++ Eval (Choices y ++ Choices z))
  choices (x,y,z) = rvconcat (choices x) $ rvconcat (choices y) (choices z)

  type Fields (x,y,z) = Eval (Fields x ++ Eval (Fields y ++ Fields z))
  fields (x,y,z) = rvconcat (fields x) $ rvconcat (fields y) (fields z)

  widths = widths @ x ++ widths @ y ++ widths @ z

  emptyChoices = rvconcat (emptyChoices @ x) $ rvconcat (emptyChoices @ y) (emptyChoices @ z)
  emptyFields = rvconcat (emptyFields @ x) $ rvconcat (emptyFields @ y) (emptyFields @ z)

--------------------------------------------------------------
-- Generics

-----------------------------------------------------------------------
-- GMemRep, the serf of this file
class GMemRep x where
  type GChoices x :: [*]
  gchoices :: x -> Product (GChoices x)

  type GFields x :: [*]
  gfields :: x -> Product (GFields x)

  gemptyChoices :: Product (GChoices x)
  gemptyFields :: Product (GFields x)

-- adapted Length to lists of lists (sums of products)
type family Length (xs :: [[*]]) :: Nat where
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

sopMap :: (All2 MemRep xs) => SOP I xs -> SOP Product (Eval (Map (Map AppChoices) xs))
sopMap = undefined

-- :t hexpand (K ()) (SOP (S (Z (I 1.0 :* SOP.Nil))))
-- :t hexpand (I ()) (SOP (S (Z (I () :* SOP.Nil))))
-- from https://hackage.haskell.org/package/generics-sop-0.5.1.1/docs/Generics-SOP.html#t:HExpand
-- hexpand [] (SOP (S (Z ([1,2] :* "xyz" :* SOP.Nil)))) :: POP [] '[ '[Bool], '[Int, Char] ]
-- purePOP :: (All SOP.SListI xss) => SOP f xss -> POP f xss
purePOP :: (All SOP.SListI yss) => SOP I yss -> POP (K ()) yss
purePOP x = expand_SOP (K ()) $ sopHap x

sopHap :: (All SOP.SListI xss) => SOP I xss -> SOP (K ()) xss
sopHap = SOP.hliftA (mapIK (const ()))

purePOP' :: (All SOP.SListI yss) => SOP I yss -> POP (K ()) yss
purePOP' x = expand_SOP (K ()) $ sopHap x

-- -- sopHap' :: (All SOP.SListI xss) => SOP I xss -> SOP Product (Eval (Map (Map AppChoices) xss))
-- sopHap' :: (All SListI xss, All2 MemRep xss) => SOP I xss -> SOP (Product <*> Choices <*> Pure) xss
-- sopHap' = mapSOP apChoices

data AppProduct :: x -> Exp y

type instance Eval (AppProduct x) = Product x

-- Expected type: NP I x -> NP (Eval (AppProduct (Map AppChoices))) x
-- Actual type:   NP I x -> NP Product (Eval     (Map AppChoices    x))

-- something :: (All Top xss) => (All2 MemRep xss) => SOP I xss -> SOP I (Product (AppChoices x))
-- something = mapNS npMap'

-- npMap' :: (All MemRep xs) => NP I xs -> NP (Eval (AppProduct (Map AppChoices))) xs
-- npMap' SOP.Nil   = SOP.Nil
-- npMap' (x :* xs) = choices' (unI x) :* npMap' xs

-- choices' :: Product (Eval (Map (Map AppChoices) x))
-- choices' = undefined

-- p ~ (NP f a -> g a)
mapNS :: (All Top xss) => forall f g . (forall x . NP f x -> NP g x) -> SOP f xss -> SOP g xss
mapNS f = SOP . liftA_NS f . unSOP

npMap :: (All MemRep xs) => NP I xs -> NP Product (Eval (Map AppChoices xs))
npMap SOP.Nil   = SOP.Nil
npMap (x :* xs) = choices (unI x) :* npMap xs

apChoices :: (MemRep a) => I a -> Product (Choices a)
apChoices = choices . unI

mapSOP :: All SListI xss => (forall (a :: k). f a -> g a) -> SOP f xss -> SOP g xss
mapSOP = liftA_SOP

npFold :: Product ys -> NP Product xs -> Product (Eval (Foldl (++) ys xs))
npFold acc SOP.Nil   = acc
npFold acc (x :* xs) = npFold (rvconcat acc x) xs

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

-- instance for Either-like types
instance
    ( All MemRep l
    , All MemRep r
    ) => GMemRep (SOP I '[ l, r]) where
  type GChoices (SOP I '[ l, r]) =  Sum '[Finite 2] ': Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppChoices) '[ l, r])))))
  gchoices (SOP (Z ls))     = Cons (Pick 0 Zero) (zipSum (npFold Nil (npMap ls)) (npFold Nil (convertPureChoices (pureChoices :: NP PC r))))
  gchoices (SOP (S (Z rs))) = Cons (Pick 1 Zero) (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (npMap rs)))
  gchoices (SOP (S (S x))) = error "this is not even possible"

  type GFields (SOP I '[ l, r]) = Eval (Foldl (ZipWith' (<>)) '[] (Eval (Map (Foldl (++) '[]) (Eval (Map (Map AppFields) '[ l, r])))))
  gfields (SOP (Z ls))     = zipSum (npFold Nil (npMapF ls)) (npFold Nil (convertPureFields (pureFields :: NP PF r)))
  gfields (SOP (S (Z rs))) = zipSum (npFold Nil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (npMapF rs))
  gfields (SOP (S (S x))) = error "this is not even possible"

  gemptyChoices = Cons (Skip Empty) (zipSum (npFold Nil (convertPureChoices (pureChoices :: NP PC l))) (npFold Nil (convertPureChoices (pureChoices :: NP PC r))))
  gemptyFields = zipSum (npFold Nil (convertPureFields (pureFields :: NP PF l))) (npFold Nil (convertPureFields (pureFields :: NP PF r)))

data AppChoices :: x -> Exp y

data AppPC :: Exp y

type instance Eval (AppChoices x) = Choices x

data AppFields :: x -> Exp y

type instance Eval (AppFields x) = Fields x

-- from https://hackage.haskell.org/package/first-class-families-0.8.0.1/docs/src/Fcf.Class.Foldable.html#Foldr
-- why use this instead of FoldR?
-- because this matches the way Fcf.<> works, so I don't have to prove that it is associative
data Foldl :: (a -> b -> Exp b) -> b -> t a -> Exp b

type instance Eval (Foldl f y '[]) = y
type instance Eval (Foldl f y (x ': xs)) = Eval (Foldl f (Eval (f y x)) xs)

-- generic instance for 1-sums (tuples)
instance (All MemRep as) => GMemRep (SOP I '[as]) where
  type GChoices (SOP I '[as]) = Eval (Foldl (++) '[] (Eval (Map AppChoices as)))
  gchoices (SOP (Z xs)) = npFold Nil (npMap xs)
  gchoices (SOP (S _)) = error "this is not even possible"

  type GFields (SOP I '[as]) = Eval (Foldl (++) '[] (Eval (Map AppFields as)))
  gfields (SOP (Z xs)) = npFold Nil (npMapF xs)
  gfields (SOP (S _)) = error "this is not even possible"

  gemptyChoices = npFold Nil (convertPureChoices (pureChoices :: NP PC as))
  gemptyFields = npFold Nil (convertPureFields (pureFields :: NP PF as))


-- foldPop :: NP PC xss -> Product (Eval (Foldl (++) '[] (Eval (Map AppChoices yss))))
-- foldPop x = npFold Nil (npMap xinner)

-- functions to generate pure Choices and Fields
newtype PC a = PC (Product (Choices a))

unPC :: PC a -> Product (Choices a)
unPC (PC x) = x

convertPureChoices :: NP PC xs -> NP Product (Eval (Map AppChoices xs))
convertPureChoices SOP.Nil   = SOP.Nil
convertPureChoices (x :* xs) = unPC x :* convertPureChoices xs

pureChoices :: (All MemRep xs) => NP PC xs
pureChoices = cpure_NP (Proxy :: Proxy MemRep) emptyChoices'

emptyChoices' :: forall x . (MemRep x) => PC x
emptyChoices' = PC $ emptyChoices @ x

newtype PF a = PF (Product (Fields a))

unPF :: PF a -> Product (Fields a)
unPF (PF x) = x

convertPureFields :: NP PF xs -> NP Product (Eval (Map AppFields xs))
convertPureFields SOP.Nil   = SOP.Nil
convertPureFields (x :* xs) = unPF x :* convertPureFields xs

pureFields :: (All MemRep xs) => NP PF xs
pureFields = cpure_NP (Proxy :: Proxy MemRep) emptyFields'

emptyFields' :: forall x . (MemRep x) => PF x
emptyFields' = PF $ emptyFields @ x

-- unused random stuff
xinner :: forall k (f :: k -> *) (xss :: [[k]]). POP f xss -> NP (NP f) xss
xinner = unPOP

try :: (All2 MemRep xss) => POP PC xss
try = cpure_POP (Proxy :: Proxy MemRep) emptyChoices'

-- either equivalent type:
data Try a b = Som a | Oth b
             deriving (GHC.Generic, Generic, MemRep)

data Tuple a b = T a b
               deriving (GHC.Generic, Generic, MemRep)

data Tuple5 a b c d e = T5 a b c d e
                      deriving (GHC.Generic, Generic, MemRep)

data Unit = Unit
          deriving (GHC.Generic, Generic, MemRep)

data MultiSum x y = First x y
                  | Second y x
                  deriving (GHC.Generic, Generic, MemRep)
