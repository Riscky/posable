{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}


{-# OPTIONS_GHC -ddump-splices #-}

module Data.Type.POSable.TH (mkPOSableGround) where

import           Data.Type.POSable.POSable
import           Data.Type.POSable.Representation
import           Language.Haskell.TH

mkPOSableGround :: Name -> DecsQ
mkPOSableGround name = mkDec (pure (ConT name))

mkDec :: Q Type -> DecsQ
mkDec name =
  [d| instance POSable $name where
        type Choices $name = 1
        choices _ = 0

        type OuterChoices $name = 1

        type Fields $name = '[ '[$name]]
        fields x = Cons (Pick x) Nil

        outerChoice _ = 0

        fromPOSable 0 (Cons (Pick x) Nil) = x
        fromPOSable _ _                   = error "index out of range"

        emptyFields = PTCons (STSucc (mkGround @($name)) STZero) PTNil
  |]
