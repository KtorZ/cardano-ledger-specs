{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Shelley.Spec.Ledger.Serialisation.Generators.Bootstrap
  ( genBootstrapAddress,
    genSignature,
  )
where

import qualified Cardano.Crypto.DSIGN as DSIGN
import Data.Maybe (fromJust)
import Shelley.Spec.Ledger.Address
  ( BootstrapAddress (..),
  )
import qualified Test.Cardano.Chain.Common.Gen as Byron
import Test.Cardano.Prelude (genBytes)
import Test.QuickCheck (Gen)
import Test.QuickCheck.Hedgehog (hedgehog)

genSignature :: forall a b. (DSIGN.DSIGNAlgorithm a) => Gen (DSIGN.SignedDSIGN a b)
genSignature =
  DSIGN.SignedDSIGN
    . fromJust
    . DSIGN.rawDeserialiseSigDSIGN
    <$> hedgehog (genBytes . fromIntegral $ DSIGN.sizeSigDSIGN ([] @a))

genBootstrapAddress :: Gen (BootstrapAddress era)
genBootstrapAddress = BootstrapAddress <$> hedgehog Byron.genAddress

