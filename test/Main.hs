{-# LANGUAGE DataKinds #-}

module Main where

import Test.Tasty ( defaultMain, testGroup, TestTree )
import Test.Tasty.HUnit ( testCase, (@?=) )
import MemRep
    ( Finite,
      Elt(choices, fields),
      Remainder(Zero, Succ),
      Sum(Pick, Skip),
      Product(Nil, Cons) )

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Test Choices and Fields of basic data types"
  [ testGroup "Maybe"
    [ testCase "Nothing" $
        choices (Nothing :: Maybe Int) @?= Cons (Pick (0 :: Finite 2) Zero) Nil
    , testCase "Just" $
        choices (Just 14 :: Maybe Int) @?= Cons (Pick (1 :: Finite 2) Zero) Nil
    , testCase "Nested" $
        choices nestedMaybe @?= Cons (Pick (1 :: Finite 2) Zero) (Cons (Pick (1 :: Finite 2) Zero) Nil)
    , testCase "Fields" $
        fields nestedMaybe @?= Cons (Pick 1.4 Zero) Nil
    ]
  , testGroup "Either"
    [ testCase "Left" $
        choices (Left 1 :: Either Int Float) @?= Cons (Pick (0 :: Finite 2) Zero) Nil
    , testCase "Right" $
        choices (Right 14 :: Either Float Int) @?= Cons (Pick (1 :: Finite 2) Zero) Nil
    , testCase "Nested" $
        choices nestedEither @?= Cons (Pick (1 :: Finite 2) Zero) (Cons (Skip $ Pick (0 :: Finite 2) Zero) Nil)
    , testCase "Fields" $
      fields nestedEither @?= Cons (Skip $ Skip $ Pick 1.4 $ Succ Zero) Nil
    ]
  , testGroup "Tuple"
    [ testCase "choices" $
        choices (1 :: Int, 2.3 :: Float) @?= Nil
    , testCase "fields" $
        fields (1 :: Int, 2.3 :: Float) @?= Cons (Pick 1 Zero) (Cons (Pick 2.3 Zero) Nil)
    ]
  , testGroup "Mixed"
    [ testCase "fields (Either, Either)" $
        choices tupleOfEithers @?= Cons (Pick 0 Zero) (Cons (Pick 1 Zero) Nil)
    , testCase "choices (Either, Either)" $
        fields tupleOfEithers @?= Cons (Pick 1 $ Succ Zero) (Cons (Skip $ Pick 2.3 Zero) Nil)
    , testCase "fields Either (,) (,)" $
        choices eitherOfTuples @?= Cons (Pick 0 Zero) Nil
    , testCase "choices Either (,) (,)" $
        fields eitherOfTuples @?= Cons (Pick 1 $ Succ Zero) (Cons (Pick 3.4 $ Succ Zero) Nil)
    ]
  ]

nestedMaybe :: Maybe (Maybe Float)
nestedMaybe = Just (Just 1.4)

nestedEither :: Either (Either Int Float) (Either Float Int)
nestedEither = Right (Left 1.4)

tupleOfEithers :: (Either Int Float, Either Int Float)
tupleOfEithers = (Left 1, Right 2.3)

eitherOfTuples :: Either (Int, Float) (Float, Int)
eitherOfTuples = Left (1,3.4)
