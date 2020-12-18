{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.Epoch
  ( EPOCH,
    EpochPredicateFailure (..),
    PredicateFailure,
  )
where

import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era (Crypto))
import Cardano.Ledger.Shelley.Constraints (UsesTxOut, UsesValue)
import Control.Monad.Trans.Reader (asks)
import Control.SetAlgebra (eval, (⨃))
import Control.State.Transition (Embed (..), InitialRule, STS (..), TRC (..), TransitionRule, judgmentContext, trans)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.BaseTypes (ShelleyBase)
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.EpochBoundary (emptySnapShots, obligation)
import Shelley.Spec.Ledger.LedgerState
  ( EpochState,
    LedgerState,
    PPUPState (..),
    PState (..),
    emptyAccount,
    emptyLedgerState,
    esAccountState,
    esLState,
    esNonMyopic,
    esPp,
    esPrevPp,
    esSnapshots,
    _delegationState,
    _deposited,
    _ppups,
    _reserves,
    _rewards,
    _utxoState,
    pattern DPState,
    pattern EpochState,
  )
import Shelley.Spec.Ledger.PParams
  ( emptyPParams,
  )
import Shelley.Spec.Ledger.Rewards (emptyNonMyopic)
import Shelley.Spec.Ledger.STS.PoolReap (POOLREAP, PoolreapState (..))
import Shelley.Spec.Ledger.STS.Snap (SNAP)
import Shelley.Spec.Ledger.STS.Upec (UPEC, UPECState (..))
import Shelley.Spec.Ledger.Slot (EpochNo)

data EPOCH era

data EpochPredicateFailure era
  = PoolReapFailure (PredicateFailure (Core.EraRule "POOLREAP" era)) -- Subtransition Failures
  | SnapFailure (PredicateFailure (Core.EraRule "SNAP" era)) -- Subtransition Failures
  | NewPpFailure (PredicateFailure (Core.EraRule "UPEC" era)) -- Subtransition Failures
  deriving (Generic)

deriving stock instance
  ( Eq (PredicateFailure (Core.EraRule "POOLREAP" era)),
    Eq (PredicateFailure (Core.EraRule "SNAP" era)),
    Eq (PredicateFailure (Core.EraRule "NEWPP" era))
  ) =>
  Eq (EpochPredicateFailure era)

deriving stock instance
  ( Show (PredicateFailure (Core.EraRule "POOLREAP" era)),
    Show (PredicateFailure (Core.EraRule "SNAP" era)),
    Show (PredicateFailure (Core.EraRule "NEWPP" era))
  ) =>
  Show (EpochPredicateFailure era)

instance
  ( UsesTxOut era,
    UsesValue era,
    Embed (Core.EraRule "SNAP" era) (EPOCH era),
    Environment (Core.EraRule "SNAP" era) ~ LedgerState era,
    State (Core.EraRule "SNAP" era) ~ SnapShots (Crypto era),
    Signal (Core.EraRule "SNAP" era) ~ (),
    Embed (Core.EraRule "POOLREAP" era) (EPOCH era),
    Environment (Core.EraRule "POOLREAP" era) ~ PParams era,
    State (Core.EraRule "POOLREAP" era) ~ PoolreapState era,
    Signal (Core.EraRule "POOLREAP" era) ~ EpochNo,
    Embed (Core.EraRule "NEWPP" era) (EPOCH era),
    Environment (Core.EraRule "NEWPP" era) ~ NewppEnv era,
    State (Core.EraRule "NEWPP" era) ~ NewppState era,
    Signal (Core.EraRule "NEWPP" era) ~ Maybe (PParams era)
  ) =>
  STS (EPOCH era)
  where
  type State (EPOCH era) = EpochState era
  type Signal (EPOCH era) = EpochNo
  type Environment (EPOCH era) = ()
  type BaseM (EPOCH era) = ShelleyBase
  type PredicateFailure (EPOCH era) = EpochPredicateFailure era
  initialRules = [initialEpoch]
  transitionRules = [epochTransition]

instance
  ( NoThunks (PredicateFailure (Core.EraRule "POOLREAP" era)),
    NoThunks (PredicateFailure (Core.EraRule "SNAP" era)),
    NoThunks (PredicateFailure (Core.EraRule "NEWPP" era))
  ) =>
  NoThunks (EpochPredicateFailure era)

initialEpoch :: InitialRule (EPOCH era)
initialEpoch =
  pure $
    EpochState
      emptyAccount
      emptySnapShots
      emptyLedgerState
      emptyPParams
      emptyPParams
      emptyNonMyopic

epochTransition ::
  forall era.
  ( UsesTxOut era,
    UsesValue era,
    Embed (Core.EraRule "SNAP" era) (EPOCH era),
    Environment (Core.EraRule "SNAP" era) ~ LedgerState era,
    State (Core.EraRule "SNAP" era) ~ SnapShots (Crypto era),
    Signal (Core.EraRule "SNAP" era) ~ (),
    Embed (Core.EraRule "POOLREAP" era) (EPOCH era),
    Environment (Core.EraRule "POOLREAP" era) ~ PParams era,
    State (Core.EraRule "POOLREAP" era) ~ PoolreapState era,
    Signal (Core.EraRule "POOLREAP" era) ~ EpochNo,
    Embed (Core.EraRule "NEWPP" era) (EPOCH era),
    Environment (Core.EraRule "NEWPP" era) ~ NewppEnv era,
    State (Core.EraRule "NEWPP" era) ~ NewppState era,
    Signal (Core.EraRule "NEWPP" era) ~ Maybe (PParams era)
  ) =>
  TransitionRule (EPOCH era)
epochTransition = do
  TRC
    ( _,
      EpochState
        { esAccountState = acnt,
          esSnapshots = ss,
          esLState = ls,
          esPrevPp = pr,
          esPp = pp,
          esNonMyopic = nm
        },
      e
      ) <-
    judgmentContext
  let utxoSt = _utxoState ls
  let DPState dstate pstate = _delegationState ls
  ss' <-
    trans @(Core.EraRule "SNAP" era) $ TRC (ls, ss, ())

  let PState pParams fPParams _ = pstate
      ppp = eval (pParams ⨃ fPParams)
      pstate' =
        pstate
          { _pParams = ppp,
            _fPParams = Map.empty
          }
  PoolreapState utxoSt' acnt' dstate' pstate'' <-
    trans @(Core.EraRule "POOLREAP" era) $ TRC (pp, PoolreapState utxoSt acnt dstate pstate', e)

  let epochState' =
        EpochState
          acnt'
          ss'
          (ls {_utxoState = utxoSt', _delegationState = DPState dstate' pstate''})
          pr
          pp
          nm

  UPECState pp' ppupSt' <-
    trans @(UPEC era) $ TRC (epochState', UPECState pp (_ppups utxoSt'), ())
  let utxoSt'' = utxoSt' {_ppups = ppupSt'}

  let Coin oblgCurr = obligation pp (_rewards dstate) (_pParams pstate)
      Coin oblgNew = obligation pp' (_rewards dstate) (_pParams pstate)
      Coin reserves = _reserves acnt
      utxoSt''' = utxoSt'' {_deposited = Coin oblgNew}
      acnt'' = acnt' {_reserves = Coin $ reserves + oblgCurr - oblgNew}
  pure $
    epochState'
      { esAccountState = acnt'',
        esLState = ls {_utxoState = utxoSt'''},
        esPrevPp = if pp' == pp then pr else pp,
        esPp = pp'
      }

instance
  ( UsesTxOut era,
    UsesValue era,
    PredicateFailure (Core.EraRule "SNAP" era) ~ SnapPredicateFailure era
  ) =>
  Embed (SNAP era) (EPOCH era)
  where
  wrapFailed = SnapFailure

instance
  ( Era era,
    PredicateFailure (Core.EraRule "POOLREAP" era) ~ PoolreapPredicateFailure era
  ) =>
  Embed (POOLREAP era) (EPOCH era)
  where
  wrapFailed = PoolReapFailure

instance
  ( Era era,
    PredicateFailure (Core.EraRule "UPEC" era) ~ UpecPredicateFailure era
  ) =>
  Embed (UPEC era) (EPOCH era)
  where
  wrapFailed = UpecFailure
