{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Cardano.Ledger.Mary () where -- export the EraGen instance for MaryEra

import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Mary.Value (Value (..))
import Cardano.Ledger.ShelleyMA.Timelocks (Timelock (..))
import Cardano.Ledger.ShelleyMA.TxBody (FamsTo, StrictMaybe, TxBody (..))
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.Slot (SlotNo)
import qualified Data.Map as Map
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Set as Set
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.MetaData (MetaDataHash)
import Shelley.Spec.Ledger.PParams (Update)
import Shelley.Spec.Ledger.Tx (TxIn, TxOut)
import Shelley.Spec.Ledger.TxBody (DCert, Wdrl)
import Test.Cardano.Ledger.Allegra
  ( genValidityInterval,
    quantifyTL,
    someLeaf,
    unQuantifyTL,
  )
import Test.Cardano.Ledger.EraBuffet (MaryEra)
import Test.QuickCheck (Gen)
import Test.Shelley.Spec.Ledger.Generator.Constants (Constants (..))
import Test.Shelley.Spec.Ledger.Generator.Core (GenEnv (..))
import Test.Shelley.Spec.Ledger.Generator.EraGen (EraGen (..))
import Test.Shelley.Spec.Ledger.Generator.ScriptClass
  ( ScriptClass (..),
    exponential,
  )
import Test.Shelley.Spec.Ledger.Utils (Split (..))

{------------------------------------------------------------------------------
 EraGen instance for MaryEra - This instance makes it possible to run the
 Shelley property tests for (MaryEra crypto)

 This instance is layered on top of the ShelleyMA instances
 in Cardano.Ledger.ShelleyMA.Scripts:

   `type instance Core.Script (MaryEra c) = Timelock (MaryEra c)`
   `type instance ValidateScript (ShelleyMAEra ma c) = ... `
------------------------------------------------------------------------------}

instance (CryptoClass.Crypto c) => ScriptClass (MaryEra c) where
  isKey _ (RequireSignature hk) = Just hk
  isKey _ _ = Nothing
  basescript _proxy = someLeaf
  quantify _ = quantifyTL
  unQuantify _ = unQuantifyTL

instance (CryptoClass.Crypto c) => EraGen (MaryEra c) where
  genGenesisValue (GenEnv _ Constants {minGenesisOutputVal, maxGenesisOutputVal}) =
    Val.inject . Coin <$> exponential minGenesisOutputVal maxGenesisOutputVal
  genEraTxBody = genTxBody
  genMetadata = error "TODO @uroboros - implement genMetaData for Mary"
  updateEraTxBody (TxBody _in _out cert wdrl _txfee vi upd meta forge) fee ins outs =
    TxBody ins outs cert wdrl fee vi upd meta forge

genTxBody ::
  forall era.
  ( FamsTo era,
    EraGen era
  ) =>
  GenEnv era ->
  SlotNo ->
  Set.Set (TxIn era) ->
  StrictSeq (TxOut era) ->
  StrictSeq (DCert era) ->
  Wdrl era ->
  Coin ->
  StrictMaybe (Update era) ->
  StrictMaybe (MetaDataHash era) ->
  Gen (TxBody era)
genTxBody _ge slot ins outs cert wdrl fee upd meta = do
  validityInterval <- genValidityInterval slot
  let mint = error "TODO @uroboros mint some Mary era tokens"
  pure $
    TxBody
      ins
      outs
      cert
      wdrl
      fee
      validityInterval
      upd
      meta
      mint

instance Split (Value era) where
  vsplit (Value n _) 0 = ([], Coin n)
  vsplit (Value n mp) m
    | m Prelude.<= 0 = error "must split coins into positive parts"
    | otherwise =
      ( take (fromIntegral m) ((Value (n `div` m) mp) : (repeat (Value (n `div` m) Map.empty))),
        Coin (n `rem` m)
      )
