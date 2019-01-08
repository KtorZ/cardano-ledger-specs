{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Ledger.Delegation
  ( -- * Delegation scheduling
    SDELEG
  , SDELEGS
  , initialDSState
  , DSState(DSState)
  , _dSStateScheduledDelegations
  , _dSStateKeyEpochDelegations
  , DCert(DCert)
  , _dbody
  , _dwit
  , _dwho
  , _depoch
  , delegator
  , delegate
  , dbody
  , dwit
  , dwho
  , depoch
    -- * Delegation activation
  , ADELEG
  , ADELEGS
  , initialDState
  , DSEnv (DSEnv)
  , allowedDelegators
  , DState(DState)
  -- * Delegation interface
  , DELEG
  , DIEnv
  , DIState(DIState)
  , PredicateFailure(SDelegSFailure, SDelegFailure, IsAlreadyScheduled)
  , initialDIState
  -- * State lens fields
  , slot
  , liveness
  , delegationMap
  -- * State lens type classes
  , HasScheduledDelegations
  , scheduledDelegations
  )
where

import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Hedgehog (Gen)
import qualified Hedgehog.Gen as Gen
import Hedgehog.Range (constant, linear)
import Control.Lens
  ( Lens'
  , (%~)
  , (&)
  , (.~)
  , (<>~)
  , (^.)
  , _1
  , _2
  , lens
  , makeFields
  , makeLenses
  , to
  )

import Control.State.Transition
  ( Embed
  , Environment
  , PredicateFailure
  , STS
  , Signal
  , State
  , TRC(TRC)
  , (?!)
  , initialRules
  , judgmentContext
  , trans
  , transitionRules
  , wrapFailed
  )
import Control.State.Transition.Generator
  ( HasTrace
  , initEnvGen
  , sigGen
  )
import Ledger.Core
  ( Epoch(Epoch)
  , Sig(Sig)
  , Slot(Slot)
  , SlotCount(SlotCount)
  , VKey
  , VKeyGenesis
  , (⨃)
  , addSlot
  , minusSlot
  , owner
  , owner
  )
import Ledger.Core.Generator (vkGen, vkgenesisGen)

--------------------------------------------------------------------------------
-- Abstract types
--------------------------------------------------------------------------------

-- | A delegation certificate.
data DCert = DCert
  { -- | Body of the delegation certificate
    _dbody :: (VKey, Epoch)
    -- | Witness for the delegation cerfiticate
  , _dwit :: Sig VKeyGenesis
    -- | Who delegates to whom
  , _dwho :: (VKeyGenesis, VKey)
    -- | Certificate epoch
  , _depoch :: Epoch
  } deriving (Show, Eq)

makeLenses ''DCert

-- | Key that is delegating.
delegator :: DCert -> VKeyGenesis
delegator c = c ^. dwho . _1

-- | Key being delegated to.
delegate :: DCert -> VKey
delegate c = c ^. dwho . _2

--------------------------------------------------------------------------------
-- Derived types
--------------------------------------------------------------------------------

-- | Delegation scheduling environment
data DSEnv = DSEnv
  { _dSEnvAllowedDelegators :: Set VKeyGenesis
  , _dSEnvEpoch :: Epoch
  , _dSEnvSlot :: Slot
  , _dSEnvLiveness :: SlotCount
  } deriving (Show, Eq)

makeFields ''DSEnv

-- | Delegation scheduling state
data DSState = DSState
  { _dSStateScheduledDelegations :: [(Slot, (VKeyGenesis, VKey))]
  , _dSStateKeyEpochDelegations :: Set (Epoch, VKeyGenesis)
  } deriving (Show, Eq)

makeFields ''DSState

initialDSState :: DSState
initialDSState = DSState
  {  _dSStateScheduledDelegations = []
  , _dSStateKeyEpochDelegations = Set.empty
  }

-- | Delegation state
data DState = DState
  { _dStateDelegationMap :: Map VKeyGenesis VKey
    -- | When was the last time each genesis key delegated.
  , _dStateLastDelegation :: Map VKeyGenesis Slot
  } deriving (Eq, Show)

makeFields ''DState

-- | Initial delegation state:
initialDState :: DState
initialDState =
  DState {_dStateDelegationMap = Map.empty, _dStateLastDelegation = Map.empty}

-- | Interface environment is the same as scheduling environment.
type DIEnv = DSEnv

data DIState = DIState
  { _dIStateDelegationMap :: Map VKeyGenesis VKey
  , _dIStateLastDelegation :: Map VKeyGenesis Slot
  , _dIStateScheduledDelegations :: [(Slot, (VKeyGenesis, VKey))]
  , _dIStateKeyEpochDelegations :: Set (Epoch, VKeyGenesis)
  } deriving (Show, Eq)

makeFields ''DIState

initialDIState :: DIState
initialDIState = DIState
  { _dIStateDelegationMap = initialDState ^. delegationMap
  , _dIStateLastDelegation = initialDState ^. lastDelegation
  , _dIStateScheduledDelegations = initialDSState ^. scheduledDelegations
  , _dIStateKeyEpochDelegations = initialDSState ^. keyEpochDelegations
  }

dIStateDSState :: Lens' DIState DSState
dIStateDSState = lens
  (\dis -> DSState (dis ^. scheduledDelegations) (dis ^. keyEpochDelegations))
  (\dis dss ->
    dis
      &  scheduledDelegations
      .~ dss
      ^. scheduledDelegations
      &  keyEpochDelegations
      .~ dss
      ^. keyEpochDelegations
  )

dIStateDState :: Lens' DIState DState
dIStateDState = lens
  (\dis -> DState (dis ^. delegationMap) (dis ^. lastDelegation))
  (\dis dss ->
    dis
      &  delegationMap
      .~ dss
      ^. delegationMap
      &  lastDelegation
      .~ dss
      ^. lastDelegation
  )

--------------------------------------------------------------------------------
-- Transition systems
--------------------------------------------------------------------------------

-- | Delegation scheduling rules
data SDELEG

instance STS SDELEG where
  type State SDELEG = DSState
  type Signal SDELEG = DCert
  type Environment SDELEG = DSEnv

  data PredicateFailure SDELEG
    = IsNotGenesisKey
    | IsPastEpoch
    | HasAlreadyDelegated
    | IsAlreadyScheduled
    | DoesNotVerify
    deriving (Eq, Show)

  initialRules = []
  transitionRules =
    [ do
        TRC (env, st, cert) <- judgmentContext
        verify cert ?! DoesNotVerify
        notAlreadyDelegated st cert ?! HasAlreadyDelegated
        notAlreadyScheduled env st cert ?! IsAlreadyScheduled
        Set.member (cert ^. dwho . _1) (env ^. allowedDelegators) ?! IsNotGenesisKey
        env ^. epoch <= cert ^. depoch ?! IsPastEpoch
        return $ st
          & scheduledDelegations <>~ [((env ^. slot) `addSlot` (env ^. liveness)
                                      , cert ^. dwho
                                      )]
          & keyEpochDelegations %~ Set.insert (env ^. epoch, cert ^. dwho . _1)
    ]
    where
      verify :: DCert -> Bool
      verify = const True
      -- Check that this delegator hasn't already delegated this epoch
      notAlreadyDelegated :: DSState -> DCert -> Bool
      notAlreadyDelegated st cert =
        Set.notMember (cert ^. depoch, cert ^. dwho . _1) (st ^. keyEpochDelegations)
      -- Check whether there is a scheduled delegation from this key
      notAlreadyScheduled :: DSEnv -> DSState -> DCert -> Bool
      notAlreadyScheduled env st cert =
        List.notElem
          ((env ^. slot) `addSlot` (env ^. liveness), cert ^. dwho . _1)
          (st ^. scheduledDelegations . to (fmap $ fmap fst))

-- | Delegation rules
data ADELEG

instance STS ADELEG where
  type State ADELEG = DState
  type Signal ADELEG = (Slot, (VKeyGenesis, VKey))
  type Environment ADELEG = ()

  data PredicateFailure ADELEG
    = BeforeExistingDelegation
      -- | Not actually a failure; this should just trigger the other rule.
    | NoLastDelegation
      -- | Not a failure; this should just pass the other rule
    | AfterExistingDelegation
    deriving (Eq, Show)

  initialRules = []
  transitionRules =
    [ do
        TRC (_env, st, (slt, (vks, vkd))) <- judgmentContext
        case Map.lookup vks (st ^. lastDelegation) of
          Nothing -> True ?! BeforeExistingDelegation
          Just sp -> sp < slt ?! BeforeExistingDelegation
        return $ st
          & delegationMap %~ (\sdm -> sdm ⨃ Map.singleton vks vkd)
          & lastDelegation %~ (\ldm -> ldm ⨃ Map.singleton vks slt)
    , do
        (TRC (_env, st, (slt, (vks, _vkd)))) <- judgmentContext
        case Map.lookup vks (st ^. lastDelegation) of
          Just sp -> sp >= slt ?! AfterExistingDelegation
          Nothing -> False ?! NoLastDelegation
        return st
    ]

-- | Delegation scheduling sequencing
data SDELEGS

instance STS SDELEGS where
  type State SDELEGS = DSState
  type Signal SDELEGS = [DCert]
  type Environment SDELEGS = DSEnv

  data PredicateFailure SDELEGS
    = SDelegFailure (PredicateFailure SDELEG)
    deriving (Eq, Show)

  initialRules = []
  transitionRules =
    [ do
        TRC (env, st, sig) <- judgmentContext
        case sig of
          [] -> return st
          (x:xs) -> do
            dss' <- trans @SDELEGS $ TRC (env, st, xs)
            dss'' <- trans @SDELEG $ TRC (env, dss', x)
            return dss''
    ]

instance Embed SDELEG SDELEGS where
  wrapFailed = SDelegFailure

-- | Delegation rules sequencing
data ADELEGS

instance STS ADELEGS where
  type State ADELEGS = DState
  type Signal ADELEGS = [(Slot, (VKeyGenesis, VKey))]
  type Environment ADELEGS = ()

  data PredicateFailure ADELEGS
    = ADelegFailure (PredicateFailure ADELEG)
    deriving (Eq, Show)

  initialRules = []
  transitionRules =
    [ do
        TRC (env, st, sig) <- judgmentContext
        case sig of
          [] -> return st
          (x:xs) -> do
            ds' <- trans @ADELEGS $ TRC (env, st, xs)
            ds'' <- trans @ADELEG $ TRC (env, ds', x)
            return ds''
    ]

instance Embed ADELEG ADELEGS where
  wrapFailed = ADelegFailure

-- | Delegation interface
data DELEG

instance STS DELEG where
  type State DELEG = DIState
  type Signal DELEG = [DCert]
  type Environment DELEG = DIEnv

  data PredicateFailure DELEG
    = SDelegSFailure (PredicateFailure SDELEGS)
    | ADelegSFailure (PredicateFailure ADELEGS)
    deriving (Eq, Show)

  initialRules = [pure initialDIState]
  transitionRules =
    [ do
        TRC (env, st, sig) <- judgmentContext
        sds <- trans @SDELEGS $ TRC (env, st ^. dIStateDSState, sig)
        let slots = filter ((<= (env ^. slot)) . fst) $ sds ^. scheduledDelegations
        dms <- trans @ADELEGS $ TRC ((), st ^. dIStateDState, slots)
        return $ DIState
          (dms ^. delegationMap)
          (dms ^. lastDelegation)
          (filter (aboutSlot (env ^. slot) (env ^. liveness) . fst)
            $ sds ^. scheduledDelegations)
          (Set.filter ((<= (env ^. epoch)) . fst)
            $ sds ^. keyEpochDelegations)
    ]
    where
      aboutSlot :: Slot -> SlotCount -> (Slot -> Bool)
      aboutSlot a b c = c >= (a `minusSlot` b) && c <= (a `addSlot` b)

instance Embed SDELEGS DELEG where
  wrapFailed = SDelegSFailure

instance Embed ADELEGS DELEG where
  wrapFailed = ADelegSFailure

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | Generate delegation certificates, using the allowed delegators in the
-- environment passed as parameter.
dcertGen :: DSEnv -> Gen DCert
dcertGen env = do
  -- The generated delegator must be one of the genesis keys in the
  -- environment.
  vkS <- Gen.element $ Set.toList (env ^. allowedDelegators)
  vkD <- vkGen
  let Epoch n = env ^. epoch
  m   <- Gen.integral (linear 0 100)
  let epo = Epoch (n + m)
  return DCert { _dbody = (vkD, epo)
               , _dwit = Sig vkS (owner vkS)
               , _dwho = (vkS, vkD)
               , _depoch = epo
               }

-- | Generate a list of delegation certificates.
--
-- At the moment the size of the generated list is severely constrained since
-- the longer the list the higher the probability that it will contain
-- conflicting delegation certificates (that will be rejected by the
-- transition-system-rules).
dcertsGen :: DSEnv -> Gen [DCert]
-- NOTE: at the moment we cannot use a linear range that depends on the
-- generator size: the problem is that the more delegation certificates in the
-- resulting list, the higher the probability that this list will be rejected
-- and the generator will have to retry.
--
dcertsGen env = Gen.list (constant 0 n) (dcertGen env)
  where n = env ^. allowedDelegators . to length

instance HasTrace DELEG where

  initEnvGen
    = DSEnv
    -- We need at least one delegator in the environment to be able to generate
    -- delegation certificates.
    --
    -- The use of a linear generator and its bound is rather arbitrary. The
    -- sizes passed to the `Gen` monad would be around 100~300, so we rather
    -- arbitrarily decided that this size times 100 is a reasonable upper
    -- bounds for epochs.
    --
    -- A similar remark applies to the ranges chosen for slot and slot count
    -- generators.
    <$> Gen.set (linear 1 7) vkgenesisGen
    <*> (Epoch <$> Gen.integral (linear 0 100))
    <*> (Slot <$> Gen.integral (linear 0 10000))
    <*> (SlotCount <$> Gen.integral (linear 0 10))

  sigGen e _st = dcertsGen e
