{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}


{-# OPTIONS_GHC -ddump-splices #-}

module Data.Type.POSable.TH (mkPOSableGroundType) where

import Data.Type.POSable.Representation
import Data.Type.POSable.POSable
import Language.Haskell.TH

mkPOSableGroundType :: Name -> DecsQ
mkPOSableGroundType name = do
  mkDec (pure (ConT name))

mkDec :: Q Type -> DecsQ
mkDec name =
  [d| instance POSable $name where
        type Choices $name = 1
        choices _ = 0
      
        type Fields $name = '[ '[$name]]
        fields x = Cons (Pick x) Nil
      
        fromPOSable 0 (Cons (Pick x) Nil) = x
        fromPOSable _ _                   = error "index out of range"
      
        emptyFields = PTCons (STSucc (mkTypeRep @( $name)) STZero) PTNil
  |]
-- do


--   let x = mkName "x"
--   return [
--       InstanceD
--         Nothing
--         []
--         (AppT
--           (ConT ''POSable)
--           (ConT name)
--         )
--         [
--           TySynD
--             ''Choices
--             [
--               PlainTV name
--             ]
--             (LitT (NumTyLit 1))
--         ,
--         --   TySynD
--         --     ''Fields
--         --     [
--         --       PlainTV name
--         --     ]
--         --     (
--         --       AppT ( AppT
--         --             PromotedConsT ( AppT
--         --                 ( AppT PromotedConsT (ConT name)
--         --                 )
--         --                 PromotedNilT
--         --             )
--         --         )
--         --         PromotedNilT
--         --     )
--         -- ,
--           FunD 'choices [
--             Clause [WildP] (NormalB (LitE (IntegerL 0))) []
--           ]
--         , FunD 'fields [
--             Clause [VarP x] (NormalB (
--               AppE
--                 (AppE (ConE 'Cons) (
--                   AppE (ConE 'Pick) (VarE x)
--                 ))
--                 (ConE 'Nil)
--             )) []
--           ]
--         ]
--     ]

-- instance POSable Double where
--   type Choices Double = 1
--   choices _ = 0

--   type Fields Double = '[ '[Double]]
--   fields x = Cons (Pick x) Nil

--   fromPOSable 0 (Cons (Pick x) Nil) = x
--   fromPOSable _ _                   = error "index out of range"

--   emptyFields = PTCons (STSucc (mkTypeRep @Double) STZero) PTNil

