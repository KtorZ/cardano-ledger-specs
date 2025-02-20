{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Definition of the shelley era, along with instances ot the @Core@ types
-- defined in @module Cardano.Ledger.Core@, and instances of the @API@ classes
-- exposed in @module Shelley.Spec.Ledger.API@.
module Cardano.Ledger.Shelley where

import Cardano.Binary (toCBOR)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Era (Era (Crypto))
import Cardano.Ledger.Shelley.Constraints (TxBodyConstraints)
import Shelley.Spec.Ledger.Coin (Coin)
import Shelley.Spec.Ledger.Keys (hashWithSerialiser)
import Shelley.Spec.Ledger.MetaData
  ( MetaData (MetaData),
    MetaDataHash (MetaDataHash),
    ValidateMetadata (hashMetadata, validateMetadata),
    validMetaDatum,
  )
import Shelley.Spec.Ledger.Scripts (MultiSig)
import Shelley.Spec.Ledger.Tx
  ( TxBody,
    ValidateScript (hashScript, validateScript),
    hashMultiSigScript,
    validateNativeMultiSigScript,
  )

data ShelleyEra c

instance CryptoClass.Crypto c => Era (ShelleyEra c) where
  type Crypto (ShelleyEra c) = c

--------------------------------------------------------------------------------
-- Core instances
--------------------------------------------------------------------------------

type instance Core.Value (ShelleyEra _c) = Coin

type instance Core.TxBody (ShelleyEra c) = TxBody (ShelleyEra c)

type instance Core.Script (ShelleyEra c) = MultiSig (ShelleyEra c)

type instance Core.Metadata (ShelleyEra c) = MetaData

--------------------------------------------------------------------------------
-- Ledger data instances
--------------------------------------------------------------------------------

instance
  (CryptoClass.Crypto c, TxBodyConstraints (ShelleyEra c)) =>
  ValidateScript (ShelleyEra c)
  where
  validateScript = validateNativeMultiSigScript
  hashScript = hashMultiSigScript

instance CryptoClass.Crypto c => ValidateMetadata (ShelleyEra c) where
  hashMetadata = MetaDataHash . hashWithSerialiser toCBOR
  validateMetadata (MetaData m) = all validMetaDatum m
