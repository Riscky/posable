{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Test.Tasty ( defaultMain, testGroup, TestTree )
import Test.Tasty.HUnit ( testCase, (@?=) )
import Data.Type.MemRep.MemRep
import Data.Type.MemRep.Representation
import Data.Type.MemRep.Instances ()
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Test Choices and Fields of basic data types"
  [ testGroup "Maybe"
    [ testCase "Nothing" $
        choices (Nothing :: Maybe Int) @?= 0
    , testCase "Just" $
        choices (Just 14 :: Maybe Int) @?= 1
    , testCase "Nested" $
        choices nestedMaybe @?= 2
    , testCase "Fields" $
        fields nestedMaybe @?= Cons (Pick 1.4) Nil
    ]
  , testGroup "Either"
    [ testCase "Left" $
        choices (Left 1 :: Either Int Float) @?= 0
    , testCase "Right" $
        choices (Right 14 :: Either Float Int) @?= 1
    , testCase "Nested" $
        choices nestedEither @?= 2
    , testCase "Fields" $
      fields nestedEither @?= Cons (Skip $ Skip $ Pick 1.4) Nil
    ]
  , testGroup "Tuple"
    [ testCase "choices" $
        choices (1 :: Int, 2.3 :: Float) @?= 0
    , testCase "fields" $
        fields (1 :: Int, 2.3 :: Float) @?= Cons (Pick 1) (Cons (Pick 2.3) Nil)
    ]
  , testGroup "Mixed"
    [ testCase "fields (Either, Either)" $
        choices tupleOfEithers @?= 2
    , testCase "choices (Either, Either)" $
        fields tupleOfEithers @?= Cons (Pick 1) (Cons (Skip $ Pick 2.3) Nil)
    , testCase "fields Either (,) (,)" $
        choices eitherOfTuples @?= 0
    , testCase "choices Either (,) (,)" $
        fields eitherOfTuples @?= Cons (Pick 1) (Cons (Pick 3.4) Nil)
    ]
  , testGroup "QuickCheck"
    [ testProperty "Either Int Float" $
        propInjectivity @(Either Int Float)
    , testProperty "Either Either Tuple" $
        propInjectivity @(Either (Either Int Float) (Float, Int))
    , testProperty "Long tuple" $
        propInjectivity @(Int, Float, Word, Float, Char)
    , testProperty "Unit" $
        propInjectivity @()
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

propInjectivity :: (MemRep a, Arbitrary a, Eq a) => a -> Bool
propInjectivity x = fromMemRep (choices x) (fields x) == x
