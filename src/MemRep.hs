{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
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
      from )
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Finite.Internal (Finite)

import Fcf

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP

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
data Sum :: [*] -> * where
  Pick :: x -> Sum (x ': xs)
  Next :: Sum xs -> Sum (x ': xs)
  Empty :: Sum xs

instance (All Show x) => Show (Sum x) where
  show (Pick x) = show x
  show (Next x) = show x
  show Empty = "Ø"

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


data (<>) :: * -> * -> Exp *

type instance Eval ((<>) x y) = x </> y

-- Type level append of Sum's
-- We might want to use the correct operator here, but for now this works well enough
type family (a :: *) </> (b :: *) :: * where
  Sum a </> Sum b = Sum (Eval (a ++ b))

-- Value level implementation of ZipWith' (<>)
rnsConcat :: Product l -> Product r -> Product (Eval (ZipWith' (<>) l r))
rnsConcat (Cons (x :: Sum a) xs) (Cons (y :: Sum b) ys) = Cons Empty (rnsConcat xs ys)
rnsConcat Nil ys = ys
rnsConcat xs Nil = xs

-- Proofs to convice the compiler that Choices and Fields contain Sum's
class IsSum x where
  -- It has proven to be quite hard to write a working instance for takeRight
  -- This is due to Empty in left, which makes it hard to know how many Next's have to be applied
  -- We could have done some typeOf trickery:
  -- https://hackage.haskell.org/package/base-4.15.0.0/docs/Data-Typeable.html#v:typeOf
  -- but that requires runtime evaluation of types, which is not ideal
  -- We now split Sum '[] and Sum (x':xs) into seperate instances of IsSum
  takeRight :: (x ~ Sum l) => Sum l -> Sum r -> Sum (Eval (l ++ r))

-- This brings the IsSum constraint in scope for all Sum x
-- We don't need a definition of takeRight because the instances (IsSum '[]) and (IsSum (x:xs))
-- together cover all possible values of Sum
instance {-# OVERLAPPABLE #-} IsSum (Sum x) where

instance {-# OVERLAPPING #-} IsSum (Sum '[]) where
  takeRight _ ys = ys

instance {-# OVERLAPPING #-} (IsSum (Sum xs)) => IsSum (Sum (x:xs)) where
  takeRight (a :: Sum (x:xs)) (ys :: Sum r) = Next (takeRight (Empty :: Sum xs) ys :: (Sum (Eval (xs ++ r))))

-- takeLeft and takeRight version of rnsConcat
-- We should probably merge them in a polymorphic thing (or even drop rnsConcat,
-- since it is functionaly equivalent to applying zipLeft (or zipRight) on 2 empty values)
zipLeft :: Product l -> Product r -> Product (Eval (ZipWith' (<>) l r))
zipLeft (Cons (x :: a) xs) (Cons (y :: b) ys) = Cons (takeLeft x y) (zipLeft xs ys)
zipLeft Nil ys = ys
zipLeft xs Nil = xs

takeLeft :: Sum l -> Sum r -> Sum (Eval (l ++ r))
takeLeft Empty  _ = Empty
takeLeft (Pick x) _ = Pick x
takeLeft (Next x) ys = Next (takeLeft x ys)

zipRight :: Product l -> Product r -> Product (Eval (ZipWith' (<>) l r))
zipRight (Cons (x :: Sum a) xs) (Cons (y :: b) ys) = Cons (takeRight x y) (zipRight xs ys)
zipRight Nil ys = ys
zipRight xs Nil = xs

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
  fields x = Cons (Pick x) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

instance MemRep Float where
  type Choices Float = '[]
  choices _ = Nil

  type Fields Float = '[Sum '[Float]]
  fields x = Cons (Pick x) Nil

  widths = [32]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

instance MemRep Int8 where
  type Choices Int8 = '[]
  choices _ = Nil

  type Fields Int8 = '[Sum '[Int8]]
  fields x = Cons (Pick x) Nil

  widths = [8]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

instance MemRep Int16 where
  type Choices Int16 = '[]
  choices _ = Nil

  type Fields Int16 = '[Sum '[Int16]]
  fields x = Cons (Pick x) Nil

  widths = [16]

  emptyChoices = Nil
  emptyFields = Cons Empty Nil

-----------------------------------------------------------------------
-- Instances of MemRep that should be generically derived in the future

-- Instance for Boolean
instance MemRep Bool where
  type Choices Bool = '[Sum '[Finite 2]]
  choices False = Cons (Pick 0) Nil
  choices True  = Cons (Pick 1) Nil

  type Fields Bool = '[]
  fields _ = Nil

  widths = []

  emptyChoices = Cons Empty Nil
  emptyFields  = Nil

-- Instance for Maybe
instance (MemRep a) => MemRep (Maybe a) where
  type Choices (Maybe a) = Eval ('[Sum '[Finite 2]] ++ Choices a)
  choices Nothing  = Cons (Pick 0) (emptyChoices @ a)
  choices (Just x) = Cons (Pick 1) (choices x)

  type Fields (Maybe a) = Fields a
  fields Nothing  = emptyFields @ a
  fields (Just x) = fields x

  widths = widths @ a

  emptyChoices = Cons Empty (emptyChoices @ a)
  emptyFields  = emptyFields @ a

-- Instance for Either, recursively defined
instance (MemRep l, MemRep r) => MemRep (Either l r) where
  type Choices (Either l r) = Eval ('[Sum '[Finite 2]] ++ Eval (ZipWith' (<>) (Choices l) (Choices r)))
  choices (Left lv)  = Cons (Pick 0) (zipLeft (choices lv) (emptyChoices @ r))
  choices (Right rv) = Cons (Pick 1) (zipRight (emptyChoices @ l) (choices rv))

  type Fields (Either l r) = Eval (ZipWith' (<>) (Fields l) (Fields r))
  fields (Left lv)  = zipLeft (fields lv) (emptyFields @ r)
  fields (Right rv) = zipRight (emptyFields @ l) (fields rv)

  widths = zipWith max (widths @ l) (widths @ r)

  emptyChoices = Cons Empty (rnsConcat (emptyChoices @ l) (emptyChoices @ r))
  emptyFields = rnsConcat (emptyFields @ l) (emptyFields @ r)

-- Instance for Direction type
instance
    ( MemRep l
    , MemRep m
    , MemRep r)
    => MemRep (Direction l m r) where
  type Choices (Direction l m r) = Eval ('[Sum '[Finite 3]] ++ Eval (ZipWith' (<>) (Choices l) (Eval (ZipWith' (<>) (Choices m) (Choices r)))))
  choices (Lef lv) = Cons (Pick 0) (zipLeft  (choices lv)       (zipLeft  (emptyChoices @ m) (emptyChoices @ r)))
  choices (Mid mv) = Cons (Pick 1) (zipRight (emptyChoices @ l) (zipLeft  (choices mv)       (emptyChoices @ r)))
  choices (Rig rv) = Cons (Pick 2) (zipRight (emptyChoices @ l) (zipRight (emptyChoices @ m) (choices rv)))

  type Fields (Direction l m r) = Eval (ZipWith' (<>) (Fields l) (Eval (ZipWith' (<>) (Fields m) (Fields r))))
  fields (Lef lv) = zipLeft  (fields lv)       (zipLeft  (emptyFields @ m) (emptyFields @ r))
  fields (Mid mv) = zipRight (emptyFields @ l) (zipLeft  (fields mv)       (emptyFields @ r))
  fields (Rig rv) = zipRight (emptyFields @ l) (zipRight (emptyFields @ m) (fields rv))

  widths = zipWith max (widths @ l) (zipWith max (widths @ m) (widths @ r))

  emptyChoices = Cons Empty (rnsConcat (emptyChoices @ l) (rnsConcat (emptyChoices @ m) (emptyChoices @ r)))
  emptyFields = rnsConcat (emptyFields @ l) (rnsConcat (emptyFields @ m) (emptyFields @ r))


-- Instance for Mult type
instance
    ( MemRep a
    , MemRep b
    , MemRep c
    , MemRep d)
    => MemRep (Mult a b c d) where
  type Choices (Mult a b c d) = Eval ('[Sum '[Finite 2]] ++ Eval (ZipWith' (<>) (Eval (Choices a ++ Choices b)) (Eval (Choices c ++ Choices d))))
  choices (Fst av bv) = Cons (Pick 0) (zipLeft (rvconcat (choices av) (choices bv)) (rvconcat (emptyChoices @ c) (emptyChoices @ d)))
  choices (Snd cv dv) = Cons (Pick 1) (zipRight (rvconcat (emptyChoices @ a) (emptyChoices @ b)) (rvconcat (choices cv) (choices dv)))

  type Fields (Mult a b c d) = Eval (ZipWith' (<>) (Eval (Fields a ++ Fields b)) (Eval (Fields c ++ Fields d)))
  fields (Fst av bv) = zipLeft (rvconcat (fields av) (fields bv)) (rvconcat (emptyFields @ c) (emptyFields @ d))
  fields (Snd cv dv) = zipRight (rvconcat (emptyFields @ a) (emptyFields @ b)) (rvconcat (fields cv) (fields dv))

  widths = zipWith max (widths @ a ++ widths @ b) (widths @ c ++ widths @ d)

  emptyChoices = Cons Empty (rnsConcat (rvconcat (emptyChoices @ a) (emptyChoices @ b)) (rvconcat (emptyChoices @ c) (emptyChoices @ d)))
  emptyFields = rnsConcat (rvconcat (emptyFields @ a) (emptyFields @ b)) (rvconcat (emptyFields @ c) (emptyFields @ d))

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

-- Instance for Units
instance
    ( MemRep x
    ) => GMemRep (SOP I '[ '[]]) where
  type GChoices (SOP I '[ '[]]) = '[]
  gchoices _ = Nil

  type GFields (SOP I '[ '[]]) = '[]
  gfields _ = Nil

  gemptyChoices = Nil
  gemptyFields = Nil


instance
    ( MemRep l
    , MemRep r
    ) => GMemRep (SOP I '[ '[l], '[r]]) where
  type GChoices (SOP I '[ '[l], '[r]]) =  Eval ('[Sum '[Finite 2]] ++ Eval (ZipWith' (<>) (Choices l) (Choices r)))
  gchoices (SOP (Z (I lv :* SOP.Nil)))     = Cons (Pick 0) (zipLeft (choices lv) (emptyChoices @ r))
  gchoices (SOP (S (Z (I rv :* SOP.Nil)))) = Cons (Pick 1) (zipRight (emptyChoices @ l) (choices rv))

  type GFields (SOP I '[ '[l], '[r]]) = Eval (ZipWith' (<>) (Fields l) (Fields r))
  gfields (SOP (Z (I lv :* SOP.Nil)))     = zipLeft  (fields lv)       (emptyFields @ r)
  gfields (SOP (S (Z (I rv :* SOP.Nil)))) = zipRight (emptyFields @ l) (fields rv)

  gemptyChoices = Cons Empty (rnsConcat (emptyChoices @ l) (emptyChoices @ r))
  gemptyFields = rnsConcat (emptyFields @ l) (emptyFields @ r)

-- Instance for Tuple-like types
instance (MemRep a, MemRep b) =>  GMemRep (SOP I '[ '[a, b]]) where
  type GChoices (SOP I '[ '[a, b]]) = Eval (Choices a ++ Choices b)
  -- Non-exhaustive pattern match? Nope, there are no inhabitants of SOP (S x)
  -- This issue arises for any GMemRep (SOP I xs) instance (afaik)
  gchoices (SOP (Z (I av :* I bv :* SOP.Nil))) = rvconcat (choices av) (choices bv)

  type GFields (SOP I '[ '[a, b]]) = Eval (Fields a ++ Fields b)
  gfields (SOP (Z (I av :* I bv :* SOP.Nil))) = rvconcat (fields av) (fields bv)

  gemptyChoices = rvconcat (emptyChoices @ a) (emptyChoices @ b)
  gemptyFields = rvconcat (emptyFields @ a) (emptyFields @ b)

-- either equivalent type:
data Try a b = Som a | Oth b
             deriving (GHC.Generic, Generic, MemRep)

data Tuple a b = T a b
               deriving (GHC.Generic, Generic, MemRep)
