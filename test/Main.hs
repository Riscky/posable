{-# LANGUAGE DataKinds #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import MemRep

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Test Choices of basic data types"
  [
    testGroup "Maybe" [
      testCase "Nothing :: Maybe Int" $
        choices (Nothing :: Maybe Int) @?= Cons (Pick (0 :: Finite 2) Zero) Nil
    ]
  ]
