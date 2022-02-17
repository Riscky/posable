{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=8 #-}

module Main where

import           Data.Type.POSable.Instances      ()
import           Data.Type.POSable.POSable        as POSable
import           Data.Type.POSable.Representation
import           GHC.Generics                     as GHC (Generic)
import           Test.Tasty                       (TestTree, defaultMain,
                                                   testGroup)
import           Test.Tasty.HUnit                 (testCase, (@?=))
import           Test.Tasty.QuickCheck
import Language.Haskell.TH
import Language.Haskell.TH.Lib

$(runQ $ do
  -- generate :: Int -> (Int -> a) -> [a]
  let generate n f = case n of
                          0 -> []
                          _ -> f n : generate (n - 1) f

  let baseTypes = [''Int, ''Float, ''Char, ''Bool]

  let buildValue n = (Bang NoSourceUnpackedness NoSourceStrictness, ConT (baseTypes !! (n-1)))

  let buildCons name n = NormalC (mkName name) (generate n buildValue)

  let arbitraryCon name n = case n of
                              0 -> AppE (VarE 'pure) (ConE name)
                              1 -> AppE (AppE (VarE '(<$>)) (ConE name)) (VarE 'arbitrary)
                              _ -> AppE (AppE (VarE '(<*>)) (arbitraryCon name (n-1))) (VarE 'arbitrary)

  let buildData name ncons nvals = DataD [] (mkName name) [] Nothing
                                    (generate ncons (\x -> buildCons (name ++ show x) nvals))
                                      [
                                          DerivClause Nothing [ConT ''Show, ConT ''Eq, ConT ''GHC.Generic, ConT ''POSable.Generic, ConT ''POSable]
                                      ]

  let buildInstance name ncons nvals = InstanceD Nothing [] (AppT (ConT ''Arbitrary) (ConT (mkName name)))
                                        [FunD 'arbitrary [
                                          Clause [] (NormalB (
                                            AppE (VarE 'oneof) (ListE (generate ncons (\x ->
                                              arbitraryCon (mkName (name ++ show x)) nvals
                                            )))
                                          )) []
                                        ]]

  let buildDataAndInstance ncons m | nvals <- m-1, name <- "TEST" ++ show ncons ++ show nvals =
                                                                                                          [
                                                                                                            buildData name ncons nvals,
                                                                                                            buildInstance name ncons nvals
                                                                                                          ]

  return (concat $ concat (generate 4 (generate 5 . buildDataAndInstance)))
  )

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
    , testProperty "Ordering" $
        propInjectivity @Ordering
    , testProperty "Large sum" $
        propInjectivity @LONGSUM
    , testProperty "Large product" $
        propInjectivity @LONGPRODUCT
    ]
  ]

data LONGSUM = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
    deriving (Show, Eq, GHC.Generic, POSable.Generic, POSable)

instance Arbitrary LONGSUM where
    arbitrary = elements [A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z]

data LONGPRODUCT = LONGPRODUCT Int Float Double Char Word Int Float Double Char Word Int Float Double Char Word Int Float Double Char Word
    deriving (Show, Eq, GHC.Generic, POSable.Generic, POSable)

instance Arbitrary LONGPRODUCT where
    arbitrary = LONGPRODUCT <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

nestedMaybe :: Maybe (Maybe Float)
nestedMaybe = Just (Just 1.4)

nestedEither :: Either (Either Int Float) (Either Float Int)
nestedEither = Right (Left 1.4)

tupleOfEithers :: (Either Int Float, Either Int Float)
tupleOfEithers = (Left 1, Right 2.3)

eitherOfTuples :: Either (Int, Float) (Float, Int)
eitherOfTuples = Left (1,3.4)

propInjectivity :: (POSable a, Arbitrary a, Eq a) => a -> Bool
propInjectivity x = fromPOSable (choices x) (fields x) == x
