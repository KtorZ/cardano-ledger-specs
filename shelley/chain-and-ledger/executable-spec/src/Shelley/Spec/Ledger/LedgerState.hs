{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : LedgerState
-- Description : Operational Rules
--
-- This module implements the operation rules for treating UTxO transactions ('Tx')
-- as state transformations on a ledger state ('LedgerState'),
-- as specified in /A Simplified Formal Specification of a UTxO Ledger/.
module Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    DPState (..),
    DState (..),
    EpochState (..),
    FutureGenDeleg (..),
    InstantaneousRewards (..),
    Ix,
    KeyPairs,
    LedgerState (..),
    PPUPState (..),
    PState (..),
    RewardAccounts,
    RewardUpdate (..),
    UTxOState (..),
    depositPoolChange,
    emptyAccount,
    emptyDPState,
    emptyDState,
    emptyEpochState,
    emptyInstantaneousRewards,
    emptyLedgerState,
    emptyPPUPState,
    emptyPState,
    emptyRewardUpdate,
    emptyUTxOState,
    pvCanFollow,
    reapRewards,
    totalInstantaneousReservesRewards,
    updatePpup,

    -- * state transitions
    emptyDelegation,

    -- * Genesis State
    genesisState,

    -- * Validation
    WitHashes (..),
    nullWitHashes,
    diffWitHashes,
    minfee,
    minfeeBound,
    txsize,
    txsizeBound,
    produced,
    consumed,
    verifiedWits,
    witsVKeyNeeded,
    witsFromWitnessSet,

    -- * DelegationState
    keyRefunds,

    -- * Epoch boundary
    stakeDistr,
    applyRUpd,
    createRUpd,
    --
    NewEpochState (..),
    getGKeys,
    updateNES,
    circulation,

    -- * Decay
    decayFactor,

    -- * Remove Bootstrap Redeem Addresses
    returnRedeemAddrsToReserves,
  )
where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    encodeListLen,
  )
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Shelley.Constraints (ShelleyBased, TxBodyConstraints)
import Cardano.Ledger.Val ((<+>), (<->), (<×>))
import qualified Cardano.Ledger.Val as Val
import Control.DeepSeq (NFData)
import Control.Monad.Trans.Reader (asks)
import Control.SetAlgebra (Bimap, biMapEmpty, dom, eval, forwards, range, (∈), (∪+), (▷), (◁))
import qualified Data.ByteString.Lazy as BSL (length)
import Data.Coerce (coerce)
import Data.Foldable (fold, toList)
import Data.Group (invert)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (NoThunks (..))
import Quiet
import Shelley.Spec.Ledger.Address (Addr (..), bootstrapKeyHash, isBootstrapRedeemer)
import Shelley.Spec.Ledger.Address.Bootstrap
  ( BootstrapWitness (..),
    bootstrapWitKeyHash,
    verifyBootstrapWit,
  )
import Shelley.Spec.Ledger.BaseTypes
  ( Globals (..),
    ShelleyBase,
    StrictMaybe (..),
    activeSlotVal,
    intervalValue,
    unitIntervalToRational,
  )
import Shelley.Spec.Ledger.Coin
  ( Coin (..),
    DeltaCoin (..),
    addDeltaCoin,
    rationalToCoinViaFloor,
    toDeltaCoin,
  )
import Shelley.Spec.Ledger.Credential (Credential (..))
import Shelley.Spec.Ledger.Delegation.Certificates
  ( DCert (..),
    PoolDistr (..),
    delegCWitness,
    genesisCWitness,
    isDeRegKey,
    poolCWitness,
    requiresVKeyWitness,
  )
import Shelley.Spec.Ledger.EpochBoundary
  ( BlocksMade (..),
    SnapShot (..),
    SnapShots (..),
    Stake (..),
    aggregateUtxoCoinByCredential,
    emptySnapShots,
  )
import Shelley.Spec.Ledger.Hashing (hashAnnotated)
import Shelley.Spec.Ledger.Keys
  ( DSignable,
    GenDelegPair (..),
    GenDelegs (..),
    Hash,
    KeyHash (..),
    KeyPair,
    KeyRole (..),
    VKey,
    asWitness,
  )
import Shelley.Spec.Ledger.PParams
  ( PParams,
    PParams' (..),
    ProposedPPUpdates (..),
    ProtVer (..),
    Update (..),
    emptyPPPUpdates,
    emptyPParams,
  )
import Shelley.Spec.Ledger.Rewards
  ( Likelihood (..),
    NonMyopic (..),
    applyDecay,
    emptyNonMyopic,
    reward,
  )
import Shelley.Spec.Ledger.Serialization (decodeRecordNamed, mapFromCBOR, mapToCBOR)
import Shelley.Spec.Ledger.Slot
  ( EpochNo (..),
    EpochSize,
    SlotNo (..),
  )
import Shelley.Spec.Ledger.Tx
  ( Tx (..),
    WitnessSet,
    WitnessSetHKD (..),
    addrWits,
    extractKeyHashWitnessSet,
  )
import Shelley.Spec.Ledger.TxBody
  ( EraIndependentTxBody,
    Ix,
    PoolCert (..),
    PoolParams (..),
    Ptr (..),
    RewardAcnt (..),
    TxIn (..),
    TxOut (..),
    Wdrl (..),
    WitVKey (..),
    getRwdCred,
    witKeyHash,
  )
import Shelley.Spec.Ledger.UTxO
  ( UTxO (..),
    balance,
    totalDeposits,
    txinLookup,
    txins,
    txouts,
    txup,
    verifyWitVKey,
  )

-- | Representation of a list of pairs of key pairs, e.g., pay and stake keys
type KeyPairs era = [(KeyPair 'Payment era, KeyPair 'Staking era)]

type RewardAccounts era =
  Map (Credential 'Staking era) Coin

data FutureGenDeleg crypto = FutureGenDeleg
  { fGenDelegSlot :: !SlotNo,
    fGenDelegGenKeyHash :: !(KeyHash 'Genesis crypto)
  }
  deriving (Show, Eq, Ord, Generic)

instance NoThunks (FutureGenDeleg crypto)

instance NFData (FutureGenDeleg crypto)

instance CC.Crypto crypto => ToCBOR (FutureGenDeleg crypto) where
  toCBOR (FutureGenDeleg a b) =
    encodeListLen 2 <> toCBOR a <> toCBOR b

instance CC.Crypto crypto => FromCBOR (FutureGenDeleg crypto) where
  fromCBOR = do
    decodeRecordNamed "FutureGenDeleg" (const 2) $ do
      a <- fromCBOR
      b <- fromCBOR
      pure $ FutureGenDeleg a b

data InstantaneousRewards era = InstantaneousRewards
  { iRReserves :: !(Map (Credential 'Staking era) Coin),
    iRTreasury :: !(Map (Credential 'Staking era) Coin)
  }
  deriving (Show, Eq, Generic)

totalInstantaneousReservesRewards :: InstantaneousRewards era -> Coin
totalInstantaneousReservesRewards (InstantaneousRewards irR _) = fold irR

instance NoThunks (InstantaneousRewards era)

instance NFData (InstantaneousRewards era)

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  ToCBOR (InstantaneousRewards era)
  where
  toCBOR (InstantaneousRewards irR irT) =
    encodeListLen 2 <> mapToCBOR irR <> mapToCBOR irT

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  FromCBOR (InstantaneousRewards era)
  where
  fromCBOR = do
    decodeRecordNamed "InstantaneousRewards" (const 2) $ do
      irR <- mapFromCBOR
      irT <- mapFromCBOR
      pure $ InstantaneousRewards irR irT

-- | State of staking pool delegations and rewards
data DState era = DState
  { -- | The active reward accounts.
    _rewards :: !(RewardAccounts era),
    -- | The current delegations.
    _delegations :: !(Map (Credential 'Staking era) (KeyHash 'StakePool (Crypto era))),
    -- | The pointed to hash keys.
    _ptrs :: !(Bimap Ptr (Credential 'Staking era)),
    -- | future genesis key delegations
    _fGenDelegs :: !(Map (FutureGenDeleg (Crypto era)) (GenDelegPair (Crypto era))),
    -- | Genesis key delegations
    _genDelegs :: !(GenDelegs (Crypto era)),
    -- | Instantaneous Rewards
    _irwd :: !(InstantaneousRewards era)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (DState era)

instance NFData (DState era)

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  ToCBOR (DState era)
  where
  toCBOR (DState rw dlg p fgs gs ir) =
    encodeListLen 6
      <> toCBOR rw
      <> toCBOR dlg
      <> toCBOR p
      <> toCBOR fgs
      <> toCBOR gs
      <> toCBOR ir

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  FromCBOR (DState era)
  where
  fromCBOR = do
    decodeRecordNamed "DState" (const 6) $ do
      rw <- fromCBOR
      dlg <- fromCBOR
      p <- fromCBOR
      fgs <- fromCBOR
      gs <- fromCBOR
      ir <- fromCBOR
      pure $ DState rw dlg p fgs gs ir

-- | Current state of staking pools and their certificate counters.
data PState era = PState
  { -- | The pool parameters.
    _pParams :: !(Map (KeyHash 'StakePool (Crypto era)) (PoolParams era)),
    -- | The future pool parameters.
    _fPParams :: !(Map (KeyHash 'StakePool (Crypto era)) (PoolParams era)),
    -- | A map of retiring stake pools to the epoch when they retire.
    _retiring :: !(Map (KeyHash 'StakePool (Crypto era)) EpochNo)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (PState era)

instance NFData (PState era)

instance Era era => ToCBOR (PState era) where
  toCBOR (PState a b c) =
    encodeListLen 3 <> toCBOR a <> toCBOR b <> toCBOR c

instance Era era => FromCBOR (PState era) where
  fromCBOR = do
    decodeRecordNamed "PState" (const 3) $ do
      a <- fromCBOR
      b <- fromCBOR
      c <- fromCBOR
      pure $ PState a b c

-- | The state associated with the current stake delegation.
data DPState era = DPState
  { _dstate :: !(DState era),
    _pstate :: !(PState era)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (DPState era)

instance NFData (DPState era)

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  ToCBOR (DPState era)
  where
  toCBOR (DPState ds ps) =
    encodeListLen 2 <> toCBOR ds <> toCBOR ps

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  FromCBOR (DPState era)
  where
  fromCBOR = do
    decodeRecordNamed "DPState" (const 2) $ do
      ds <- fromCBOR
      ps <- fromCBOR
      pure $ DPState ds ps

data RewardUpdate era = RewardUpdate
  { deltaT :: !DeltaCoin,
    deltaR :: !DeltaCoin,
    rs :: !(Map (Credential 'Staking era) Coin),
    deltaF :: !DeltaCoin,
    nonMyopic :: !(NonMyopic era)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (RewardUpdate era)

instance NFData (RewardUpdate era)

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  ToCBOR (RewardUpdate era)
  where
  toCBOR (RewardUpdate dt dr rw df nm) =
    encodeListLen 5
      <> toCBOR dt
      <> toCBOR (invert dr) -- TODO change Coin serialization to use integers?
      <> toCBOR rw
      <> toCBOR (invert df) -- TODO change Coin serialization to use integers?
      <> toCBOR nm

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  FromCBOR (RewardUpdate era)
  where
  fromCBOR = do
    decodeRecordNamed "RewardUpdate" (const 5) $ do
      dt <- fromCBOR
      dr <- fromCBOR -- TODO change Coin serialization to use integers?
      rw <- fromCBOR
      df <- fromCBOR -- TODO change Coin serialization to use integers?
      nm <- fromCBOR
      pure $ RewardUpdate dt (invert dr) rw (invert df) nm

emptyRewardUpdate :: RewardUpdate era
emptyRewardUpdate = RewardUpdate (DeltaCoin 0) (DeltaCoin 0) Map.empty (DeltaCoin 0) emptyNonMyopic

data AccountState = AccountState
  { _treasury :: !Coin,
    _reserves :: !Coin
  }
  deriving (Show, Eq, Generic)

instance ToCBOR AccountState where
  toCBOR (AccountState t r) =
    encodeListLen 2 <> toCBOR t <> toCBOR r

instance FromCBOR AccountState where
  fromCBOR = do
    decodeRecordNamed "AccountState" (const 2) $ do
      t <- fromCBOR
      r <- fromCBOR
      pure $ AccountState t r

instance NoThunks AccountState

instance NFData AccountState

data EpochState era = EpochState
  { esAccountState :: !AccountState,
    esSnapshots :: !(SnapShots era),
    esLState :: !(LedgerState era),
    esPrevPp :: !(PParams era),
    esPp :: !(PParams era),
    -- | This field, esNonMyopic, does not appear in the formal spec
    -- and is not a part of the protocol. It is only used for providing
    -- data to the stake pool ranking calculation @getNonMyopicMemberRewards@.
    -- See https://hydra.iohk.io/job/Cardano/cardano-ledger-specs/specs.pool-ranking/latest/download-by-type/doc-pdf/pool-ranking
    esNonMyopic :: !(NonMyopic era)
  }
  deriving (Generic)

deriving stock instance
  ShelleyBased era =>
  Show (EpochState era)

deriving stock instance
  ShelleyBased era =>
  Eq (EpochState era)

instance NoThunks (EpochState era)

instance (Era era) => NFData (EpochState era)

instance
  ShelleyBased era =>
  ToCBOR (EpochState era)
  where
  toCBOR (EpochState a s l r p n) =
    encodeListLen 6 <> toCBOR a <> toCBOR s <> toCBOR l <> toCBOR r <> toCBOR p <> toCBOR n

instance
  ShelleyBased era =>
  FromCBOR (EpochState era)
  where
  fromCBOR = do
    decodeRecordNamed "EpochState" (const 6) $ do
      a <- fromCBOR
      s <- fromCBOR
      l <- fromCBOR
      r <- fromCBOR
      p <- fromCBOR
      n <- fromCBOR
      pure $ EpochState a s l r p n

emptyPPUPState :: PPUPState era
emptyPPUPState = PPUPState emptyPPPUpdates emptyPPPUpdates

emptyUTxOState :: UTxOState era
emptyUTxOState = UTxOState (UTxO Map.empty) (Coin 0) (Coin 0) emptyPPUPState

emptyEpochState :: EpochState era
emptyEpochState =
  EpochState emptyAccount emptySnapShots emptyLedgerState emptyPParams emptyPParams emptyNonMyopic

emptyLedgerState :: LedgerState era
emptyLedgerState =
  LedgerState
    emptyUTxOState
    emptyDelegation

emptyAccount :: AccountState
emptyAccount = AccountState (Coin 0) (Coin 0)

emptyDelegation :: DPState era
emptyDelegation =
  DPState emptyDState emptyPState

emptyInstantaneousRewards :: InstantaneousRewards era
emptyInstantaneousRewards = InstantaneousRewards Map.empty Map.empty

emptyDState :: DState era
emptyDState =
  DState
    Map.empty
    Map.empty
    biMapEmpty
    Map.empty
    (GenDelegs Map.empty)
    emptyInstantaneousRewards

emptyPState :: PState era
emptyPState =
  PState Map.empty Map.empty Map.empty

emptyDPState :: DPState era
emptyDPState = DPState emptyDState emptyPState

data PPUPState era = PPUPState
  { proposals :: !(ProposedPPUpdates era),
    futureProposals :: !(ProposedPPUpdates era)
  }
  deriving (Show, Eq, Generic, NFData, NoThunks)

instance Era era => ToCBOR (PPUPState era) where
  toCBOR (PPUPState ppup fppup) =
    encodeListLen 2 <> toCBOR ppup <> toCBOR fppup

instance Era era => FromCBOR (PPUPState era) where
  fromCBOR = do
    decodeRecordNamed "PPUPState" (const 2) $ do
      ppup <- fromCBOR
      fppup <- fromCBOR
      pure $ PPUPState ppup fppup

pvCanFollow :: ProtVer -> StrictMaybe ProtVer -> Bool
pvCanFollow _ SNothing = True
pvCanFollow (ProtVer m n) (SJust (ProtVer m' n')) =
  (m + 1, 0) == (m', n') || (m, n + 1) == (m', n')

-- | Update the protocol parameter updates by clearing out the proposals
-- and making the future proposals become the new proposals,
-- provided the new proposals can follow (otherwise reset them).
updatePpup :: UTxOState era -> PParams era -> UTxOState era
updatePpup utxoSt pp = utxoSt {_ppups = PPUPState ps emptyPPPUpdates}
  where
    (ProposedPPUpdates newProposals) = futureProposals . _ppups $ utxoSt
    goodPV = pvCanFollow (_protocolVersion pp) . _protocolVersion
    ps = if all goodPV newProposals then ProposedPPUpdates newProposals else emptyPPPUpdates

data UTxOState era = UTxOState
  { _utxo :: !(UTxO era),
    _deposited :: !Coin,
    _fees :: !Coin,
    _ppups :: !(PPUPState era)
  }
  deriving (Generic, NFData)

deriving stock instance
  ShelleyBased era =>
  Show (UTxOState era)

deriving stock instance
  ShelleyBased era =>
  Eq (UTxOState era)

instance NoThunks (UTxOState era)

instance
  ShelleyBased era =>
  ToCBOR (UTxOState era)
  where
  toCBOR (UTxOState ut dp fs us) =
    encodeListLen 4 <> toCBOR ut <> toCBOR dp <> toCBOR fs <> toCBOR us

instance
  ShelleyBased era =>
  FromCBOR (UTxOState era)
  where
  fromCBOR = do
    decodeRecordNamed "UTxOState" (const 4) $ do
      ut <- fromCBOR
      dp <- fromCBOR
      fs <- fromCBOR
      us <- fromCBOR
      pure $ UTxOState ut dp fs us

-- | New Epoch state and environment
data NewEpochState era = NewEpochState
  { -- | Last epoch
    nesEL :: !EpochNo,
    -- | Blocks made before current epoch
    nesBprev :: !(BlocksMade era),
    -- | Blocks made in current epoch
    nesBcur :: !(BlocksMade era),
    -- | Epoch state before current
    nesEs :: !(EpochState era),
    -- | Possible reward update
    nesRu :: !(StrictMaybe (RewardUpdate era)),
    -- | Stake distribution within the stake pool
    nesPd :: !(PoolDistr (Crypto era))
  }
  deriving (Generic)

deriving stock instance
  ShelleyBased era =>
  Show (NewEpochState era)

deriving stock instance
  ShelleyBased era =>
  Eq (NewEpochState era)

instance (Era era) => NFData (NewEpochState era)

instance NoThunks (NewEpochState era)

instance ShelleyBased era => ToCBOR (NewEpochState era) where
  toCBOR (NewEpochState e bp bc es ru pd) =
    encodeListLen 6 <> toCBOR e <> toCBOR bp <> toCBOR bc <> toCBOR es
      <> toCBOR ru
      <> toCBOR pd

instance
  ShelleyBased era =>
  FromCBOR (NewEpochState era)
  where
  fromCBOR = do
    decodeRecordNamed "NewEpochState" (const 6) $ do
      e <- fromCBOR
      bp <- fromCBOR
      bc <- fromCBOR
      es <- fromCBOR
      ru <- fromCBOR
      pd <- fromCBOR
      pure $ NewEpochState e bp bc es ru pd

getGKeys ::
  NewEpochState era ->
  Set (KeyHash 'Genesis (Crypto era))
getGKeys nes = Map.keysSet genDelegs
  where
    NewEpochState _ _ _ es _ _ = nes
    EpochState _ _ ls _ _ _ = es
    LedgerState _ (DPState (DState _ _ _ _ (GenDelegs genDelegs) _) _) = ls

-- | The state associated with a 'Ledger'.
data LedgerState era = LedgerState
  { -- | The current unspent transaction outputs.
    _utxoState :: !(UTxOState era),
    -- | The current delegation state
    _delegationState :: !(DPState era)
  }
  deriving (Generic)

deriving stock instance
  ShelleyBased era =>
  Show (LedgerState era)

deriving stock instance
  ShelleyBased era =>
  Eq (LedgerState era)

instance NoThunks (LedgerState era)

instance (Era era) => NFData (LedgerState era)

instance
  ShelleyBased era =>
  ToCBOR (LedgerState era)
  where
  toCBOR (LedgerState u dp) =
    encodeListLen 2 <> toCBOR u <> toCBOR dp

instance
  ShelleyBased era =>
  FromCBOR (LedgerState era)
  where
  fromCBOR = do
    decodeRecordNamed "LedgerState" (const 2) $ do
      u <- fromCBOR
      dp <- fromCBOR
      pure $ LedgerState u dp

-- | Creates the ledger state for an empty ledger which
--  contains the specified transaction outputs.
genesisState ::
  Map (KeyHash 'Genesis (Crypto era)) (GenDelegPair (Crypto era)) ->
  UTxO era ->
  LedgerState era
genesisState genDelegs0 utxo0 =
  LedgerState
    ( UTxOState
        utxo0
        (Coin 0)
        (Coin 0)
        emptyPPUPState
    )
    (DPState dState emptyPState)
  where
    dState = emptyDState {_genDelegs = GenDelegs genDelegs0}

-- | Implementation of abstract transaction size
txsize :: Tx era -> Integer
txsize = fromIntegral . BSL.length . txFullBytes

-- | Convenience Function to bound the txsize function.
-- | It can be helpful for coin selection.
txsizeBound ::
  forall era.
  ( ShelleyBased era,
    HasField "outputs" (Core.TxBody era) (StrictSeq (TxOut era)),
    HasField "inputs" (Core.TxBody era) (Set (TxIn era))
  ) =>
  Tx era ->
  Integer
txsizeBound tx = numInputs * inputSize + numOutputs * outputSize + rest
  where
    uint = 5
    smallArray = 1
    hashLen = 32
    hashObj = 2 + hashLen
    addrHashLen = 28
    addrHeader = 1
    address = 2 + addrHeader + 2 * addrHashLen
    txbody = _body tx
    numInputs = toInteger . length . getField @"inputs" $ txbody
    inputSize = smallArray + uint + hashObj
    numOutputs = toInteger . length . getField @"outputs" $ txbody
    outputSize = smallArray + uint + address
    rest = fromIntegral $ BSL.length (txFullBytes tx)

-- | Minimum fee calculation
minfee :: PParams era -> Tx era -> Coin
minfee pp tx =
  Coin $
    fromIntegral (_minfeeA pp)
      * txsize tx + fromIntegral (_minfeeB pp)

-- | Minimum fee bound using txsizeBound
minfeeBound ::
  forall era.
  ( ShelleyBased era,
    HasField "outputs" (Core.TxBody era) (StrictSeq (TxOut era)),
    HasField "inputs" (Core.TxBody era) (Set (TxIn era))
  ) =>
  PParams era ->
  Tx era ->
  Coin
minfeeBound pp tx =
  Coin $
    fromIntegral (_minfeeA pp)
      * txsizeBound tx + fromIntegral (_minfeeB pp)

-- | Compute the lovelace which are created by the transaction
produced ::
  ( ShelleyBased era,
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert era)),
    HasField "outputs" (Core.TxBody era) (StrictSeq (TxOut era)),
    HasField "txfee" (Core.TxBody era) Coin
  ) =>
  PParams era ->
  Map (KeyHash 'StakePool (Crypto era)) (PoolParams era) ->
  Core.TxBody era ->
  Core.Value era
produced pp stakePools tx =
  balance (txouts tx)
    <> ( Val.inject $
           getField @"txfee" tx
             <> totalDeposits pp stakePools (toList $ getField @"certs" tx)
       )

-- | Compute the key deregistration refunds in a transaction
keyRefunds ::
  ( HasField "certs" (Core.TxBody era) (StrictSeq (DCert era))
  ) =>
  PParams era ->
  Core.TxBody era ->
  Coin
keyRefunds pp tx = (length deregistrations) <×> (_keyDeposit pp)
  where
    deregistrations = filter isDeRegKey (toList $ getField @"certs" tx)

-- | Compute the lovelace which are destroyed by the transaction
consumed ::
  ( ShelleyBased era,
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert era)),
    HasField "inputs" (Core.TxBody era) (Set (TxIn era)),
    HasField "wdrls" (Core.TxBody era) (Wdrl era)
  ) =>
  PParams era ->
  UTxO (era) ->
  Core.TxBody era ->
  Core.Value era
consumed pp u tx =
  balance (eval (txins tx ◁ u)) <> (Val.inject $ refunds <> withdrawals)
  where
    -- balance (UTxO (Map.restrictKeys v (txins tx))) + refunds + withdrawals
    refunds = keyRefunds pp tx
    withdrawals = fold . unWdrl $ getField @"wdrls" tx

newtype WitHashes era = WitHashes
  {unWitHashes :: Set (KeyHash 'Witness (Crypto era))}
  deriving (Eq, Generic)
  deriving (Show) via Quiet (WitHashes era)

instance Era era => NoThunks (WitHashes era)

-- | Check if a set of witness hashes is empty.
nullWitHashes :: WitHashes era -> Bool
nullWitHashes (WitHashes a) = Set.null a

-- | Extract the difference between two sets of witness hashes.
diffWitHashes :: WitHashes era -> WitHashes era -> WitHashes era
diffWitHashes (WitHashes x) (WitHashes x') =
  WitHashes (x `Set.difference` x')

-- | Extract the witness hashes from the Witness set.
witsFromWitnessSet ::
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  WitnessSet era ->
  WitHashes era
witsFromWitnessSet (WitnessSet aWits _ bsWits) =
  WitHashes $
    Set.map witKeyHash aWits
      `Set.union` Set.map bootstrapWitKeyHash bsWits

-- | Collect the set of hashes of keys that needs to sign a
--  given transaction. This set consists of the txin owners,
--  certificate authors, and withdrawal reward accounts.
witsVKeyNeeded ::
  forall era.
  ( ShelleyBased era,
    HasField "wdrls" (Core.TxBody era) (Wdrl era),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert era)),
    HasField "inputs" (Core.TxBody era) (Set (TxIn era)),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era))
  ) =>
  UTxO era ->
  Tx era ->
  GenDelegs (Crypto era) ->
  WitHashes era
witsVKeyNeeded utxo' tx@(Tx txbody _ _) genDelegs =
  WitHashes $
    certAuthors
      `Set.union` inputAuthors
      `Set.union` owners
      `Set.union` wdrlAuthors
      `Set.union` updateKeys
  where
    inputAuthors :: Set (KeyHash 'Witness (Crypto era))
    inputAuthors = foldr accum Set.empty (getField @"inputs" txbody)
      where
        accum txin ans =
          case txinLookup txin utxo' of
            Just (TxOut (Addr _ (KeyHashObj pay) _) _) ->
              Set.insert (asWitness pay) ans
            Just (TxOut (AddrBootstrap bootAddr) _) ->
              Set.insert (asWitness (bootstrapKeyHash bootAddr)) ans
            _other -> ans
    wdrlAuthors :: Set (KeyHash 'Witness (Crypto era))
    wdrlAuthors = Map.foldrWithKey accum Set.empty (unWdrl (getField @"wdrls" txbody))
      where
        accum key _ ans = Set.union (extractKeyHashWitnessSet [getRwdCred key]) ans
    owners :: Set (KeyHash 'Witness (Crypto era))
    owners = foldr accum Set.empty (getField @"certs" txbody)
      where
        accum (DCertPool (RegPool pool)) ans =
          Set.union
            (Set.map asWitness (_poolOwners pool))
            ans
        accum _cert ans = ans
    cwitness (DCertDeleg dc) = extractKeyHashWitnessSet [delegCWitness dc]
    cwitness (DCertPool pc) = extractKeyHashWitnessSet [poolCWitness pc]
    cwitness (DCertGenesis gc) = Set.singleton (asWitness $ genesisCWitness gc)
    cwitness c = error $ show c ++ " does not have a witness"
    -- key reg requires no witness but this is already filtered outby requiresVKeyWitness
    -- before the call to `cwitness`, so this error should never be reached.

    certAuthors :: Set (KeyHash 'Witness (Crypto era))
    certAuthors = foldr accum Set.empty (getField @"certs" txbody)
      where
        accum cert ans | requiresVKeyWitness cert = Set.union (cwitness cert) ans
        accum _cert ans = ans
    updateKeys :: Set (KeyHash 'Witness (Crypto era))
    updateKeys = asWitness `Set.map` propWits (txup tx) genDelegs

-- | Given a ledger state, determine if the UTxO witnesses in a given
--  transaction are correct.
verifiedWits ::
  ( TxBodyConstraints era,
    Core.AnnotatedData (Core.Script era),
    ToCBOR (Core.Metadata era),
    DSignable (Crypto era) (Hash (Crypto era) EraIndependentTxBody)
  ) =>
  Tx era ->
  Either [VKey 'Witness (Crypto era)] ()
verifiedWits (Tx txbody wits _) =
  case (failed <> failedBootstrap) of
    [] -> Right ()
    nonEmpty -> Left nonEmpty
  where
    wvkKey (WitVKey k _) = k
    failed =
      wvkKey
        <$> filter
          (not . verifyWitVKey (coerce . hashAnnotated $ txbody))
          (Set.toList $ addrWits wits)
    failedBootstrap =
      bwKey
        <$> filter
          (not . verifyBootstrapWit (coerce . hashAnnotated $ txbody))
          (Set.toList $ bootWits wits)

-- | Calculate the set of hash keys of the required witnesses for update
-- proposals.
propWits ::
  Maybe (Update era) ->
  GenDelegs (Crypto era) ->
  Set (KeyHash 'Witness (Crypto era))
propWits Nothing _ = Set.empty
propWits (Just (Update (ProposedPPUpdates pup) _)) (GenDelegs genDelegs) =
  Set.map asWitness . Set.fromList $ Map.elems updateKeys
  where
    updateKeys' = eval (Map.keysSet pup ◁ genDelegs)
    updateKeys = Map.map genDelegKeyHash updateKeys'

-- Functions for stake delegation model

-- | Calculate the change to the deposit pool for a given transaction.
depositPoolChange ::
  ( HasField "certs" (Core.TxBody era) (StrictSeq (DCert era))
  ) =>
  LedgerState era ->
  PParams era ->
  Core.TxBody era ->
  Coin
depositPoolChange ls pp tx = (currentPool <+> txDeposits) <-> txRefunds
  where
    -- Note that while (currentPool + txDeposits) >= txRefunds,
    -- it could be that txDeposits < txRefunds. We keep the parenthesis above
    -- to emphasize this point.

    currentPool = (_deposited . _utxoState) ls
    txDeposits =
      totalDeposits pp ((_pParams . _pstate . _delegationState) ls) (toList $ getField @"certs" tx)
    txRefunds = keyRefunds pp tx

reapRewards ::
  RewardAccounts era ->
  RewardAccounts era ->
  RewardAccounts era
reapRewards dStateRewards withdrawals =
  Map.mapWithKey removeRewards dStateRewards
  where
    removeRewards k v = if k `Map.member` withdrawals then Coin 0 else v

---------------------------------
-- epoch boundary calculations --
---------------------------------

stakeDistr ::
  forall era.
  ShelleyBased era =>
  UTxO era ->
  DState era ->
  PState era ->
  SnapShot era
stakeDistr u ds ps =
  SnapShot
    (Stake $ eval (dom activeDelegs ◁ stakeRelation))
    delegs
    poolParams
  where
    DState rewards' delegs ptrs' _ _ _ = ds
    PState poolParams _ _ = ps
    stakeRelation :: Map (Credential 'Staking era) Coin
    stakeRelation = aggregateUtxoCoinByCredential (forwards ptrs') u rewards'
    activeDelegs :: Map (Credential 'Staking era) (KeyHash 'StakePool (Crypto era))
    activeDelegs = eval ((dom rewards' ◁ delegs) ▷ dom poolParams)

-- | Apply a reward update
applyRUpd ::
  RewardUpdate era ->
  EpochState era ->
  EpochState era
applyRUpd ru (EpochState as ss ls pr pp _nm) = EpochState as' ss ls' pr pp nm'
  where
    utxoState_ = _utxoState ls
    delegState = _delegationState ls
    dState = _dstate delegState
    (regRU, unregRU) =
      Map.partitionWithKey
        (\k _ -> eval (k ∈ dom (_rewards dState)))
        (rs ru)
    as' =
      as
        { _treasury = (addDeltaCoin (_treasury as) (deltaT ru)) <> fold (range unregRU),
          _reserves = addDeltaCoin (_reserves as) (deltaR ru)
        }
    ls' =
      ls
        { _utxoState =
            utxoState_ {_fees = _fees utxoState_ `addDeltaCoin` deltaF ru},
          _delegationState =
            delegState
              { _dstate =
                  dState
                    { _rewards = eval (_rewards dState ∪+ regRU)
                    }
              }
        }
    nm' = nonMyopic ru

decayFactor :: Float
decayFactor = 0.9

updateNonMypopic ::
  NonMyopic era ->
  Coin ->
  Map (KeyHash 'StakePool (Crypto era)) Likelihood ->
  NonMyopic era
updateNonMypopic nm rPot newLikelihoods =
  nm
    { likelihoodsNM = updatedLikelihoods,
      rewardPotNM = rPot
    }
  where
    history = likelihoodsNM nm
    performance kh newPerf =
      fromMaybe
        mempty
        (applyDecay decayFactor <$> Map.lookup kh history)
        <> newPerf
    updatedLikelihoods = Map.mapWithKey performance newLikelihoods

-- | Create a reward update
createRUpd ::
  EpochSize ->
  BlocksMade era ->
  EpochState era ->
  Coin ->
  ShelleyBase (RewardUpdate era)
createRUpd slotsPerEpoch b@(BlocksMade b') es@(EpochState acnt ss ls pr _ nm) maxSupply = do
  asc <- asks activeSlotCoeff
  let SnapShot stake' delegs' poolParams = _pstakeGo ss
      Coin reserves = _reserves acnt
      ds = _dstate $ _delegationState ls
      -- reserves and rewards change
      deltaR1 =
        ( rationalToCoinViaFloor $
            min 1 eta
              * unitIntervalToRational (_rho pr)
              * fromIntegral reserves
        )
      d = unitIntervalToRational (_d pr)
      expectedBlocks =
        floor $
          (1 - d) * unitIntervalToRational (activeSlotVal asc) * fromIntegral slotsPerEpoch
      -- TODO asc is a global constant, and slotsPerEpoch should not change often at all,
      -- it would be nice to not have to compute expectedBlocks every epoch
      eta
        | intervalValue (_d pr) >= 0.8 = 1
        | otherwise = blocksMade % expectedBlocks
      Coin rPot = _feeSS ss <> deltaR1
      deltaT1 = floor $ intervalValue (_tau pr) * fromIntegral rPot
      _R = Coin $ rPot - deltaT1
      totalStake = circulation es maxSupply
      (rs_, newLikelihoods) =
        reward
          pr
          b
          _R
          (Map.keysSet $ _rewards ds)
          poolParams
          stake'
          delegs'
          totalStake
          asc
          slotsPerEpoch
      deltaR2 = _R <-> (Map.foldr (<+>) mempty rs_)
      blocksMade = fromIntegral $ Map.foldr (+) 0 b' :: Integer
  pure $
    RewardUpdate
      { deltaT = (DeltaCoin deltaT1),
        deltaR = ((invert $ toDeltaCoin deltaR1) <> toDeltaCoin deltaR2),
        rs = rs_,
        deltaF = (invert (toDeltaCoin $ _feeSS ss)),
        nonMyopic = (updateNonMypopic nm _R newLikelihoods)
      }

-- | Calculate the current circulation
--
-- This is used in the rewards calculation, and for API endpoints for pool ranking.
circulation :: EpochState era -> Coin -> Coin
circulation (EpochState acnt _ _ _ _ _) supply =
  supply <-> (_reserves acnt)

-- | Update new epoch state
updateNES ::
  NewEpochState era ->
  BlocksMade era ->
  LedgerState era ->
  NewEpochState era
updateNES
  ( NewEpochState
      eL
      bprev
      _
      (EpochState acnt ss _ pr pp nm)
      ru
      pd
    )
  bcur
  ls =
    NewEpochState eL bprev bcur (EpochState acnt ss ls pr pp nm) ru pd

returnRedeemAddrsToReserves ::
  ShelleyBased era =>
  EpochState era ->
  EpochState era
returnRedeemAddrsToReserves es = es {esAccountState = acnt', esLState = ls'}
  where
    ls = esLState es
    us = _utxoState ls
    UTxO utxo = _utxo us
    (redeemers, nonredeemers) = Map.partition (\(TxOut a _) -> isBootstrapRedeemer a) utxo
    acnt = esAccountState es
    acnt' = acnt {_reserves = (_reserves acnt) <+> (Val.coin . balance $ UTxO redeemers)}
    us' = us {_utxo = UTxO nonredeemers}
    ls' = ls {_utxoState = us'}
