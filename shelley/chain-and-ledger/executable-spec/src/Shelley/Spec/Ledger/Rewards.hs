{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Shelley.Spec.Ledger.Rewards
  ( desirability,
    PerformanceEstimate (..),
    NonMyopic (..),
    emptyNonMyopic,
    getTopRankedPools,
    StakeShare (..),
    mkApparentPerformance,
    reward,
    nonMyopicStake,
    nonMyopicMemberRew,
    percentile',
    Histogram (..),
    LogWeight (..),
    likelihood,
    applyDecay,
    Likelihood (..),
    leaderProbability,
    leaderRew,
    memberRew,
  )
where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    decodeDouble,
    encodeDouble,
    encodeListLen,
  )
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Val ((<->))
import Cardano.Slotting.Slot (EpochSize)
import Control.DeepSeq (NFData)
import Control.Iterate.SetAlgebra (eval, (◁))
import Data.Foldable (find, fold)
import Data.Function (on)
import Data.List (sortBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Ratio ((%))
import qualified Data.Sequence as Seq
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..))
import Numeric.Natural (Natural)
import Quiet
import Shelley.Spec.Ledger.BaseTypes
  ( ActiveSlotCoeff,
    UnitInterval,
    activeSlotVal,
    unitIntervalToRational,
  )
import Shelley.Spec.Ledger.Coin
  ( Coin (..),
    coinToRational,
    rationalToCoinViaFloor,
  )
import Shelley.Spec.Ledger.Credential (Credential (..))
import Shelley.Spec.Ledger.Delegation.PoolParams (poolSpec)
import Shelley.Spec.Ledger.EpochBoundary
  ( BlocksMade (..),
    Stake (..),
    maxPool,
    poolStake,
  )
import qualified Shelley.Spec.Ledger.HardForks as HardForks
import Shelley.Spec.Ledger.Keys (KeyHash, KeyRole (..))
import Shelley.Spec.Ledger.PParams (PParams, _a0, _d, _nOpt)
import Shelley.Spec.Ledger.Serialization
  ( decodeRecordNamed,
    decodeSeq,
    encodeFoldable,
  )
import Shelley.Spec.Ledger.TxBody (PoolParams (..), getRwdCred)

newtype LogWeight = LogWeight {unLogWeight :: Float}
  deriving (Eq, Generic, Ord, Num, NFData, NoThunks, ToCBOR, FromCBOR)
  deriving (Show) via Quiet LogWeight

toLogWeight :: Double -> LogWeight
toLogWeight d = LogWeight (realToFrac $ log d)

fromLogWeight :: LogWeight -> Double
fromLogWeight (LogWeight l) = exp (realToFrac l)

newtype Histogram = Histogram {unHistogram :: StrictSeq LogWeight}
  deriving (Eq, Show, Generic)

newtype Likelihood = Likelihood {unLikelihood :: StrictSeq LogWeight}
  -- TODO: replace with small data structure
  deriving (Show, Generic, NFData)

instance NoThunks Likelihood

instance Eq Likelihood where
  (==) = (==) `on` unLikelihood . normalizeLikelihood

instance Semigroup Likelihood where
  (Likelihood x) <> (Likelihood y) =
    normalizeLikelihood $ Likelihood (strictSeqZipWith (+) x y)

instance Monoid Likelihood where
  mempty = Likelihood $ StrictSeq.toStrict $ Seq.replicate (length samplePositions) (LogWeight 0)

-- TODO should be defined in @Data.Sequence.Strict@
strictSeqZipWith :: (a -> b -> c) -> StrictSeq a -> StrictSeq b -> StrictSeq c
strictSeqZipWith f x y =
  StrictSeq.toStrict (Seq.zipWith f (StrictSeq.getSeq x) (StrictSeq.getSeq y))

normalizeLikelihood :: Likelihood -> Likelihood
normalizeLikelihood (Likelihood xs) = Likelihood $ (\x -> x - m) <$> xs
  where
    m = minimum xs

instance ToCBOR Likelihood where
  toCBOR (Likelihood logweights) = encodeFoldable logweights

instance FromCBOR Likelihood where
  fromCBOR = Likelihood . StrictSeq.toStrict <$> decodeSeq fromCBOR

leaderProbability :: ActiveSlotCoeff -> Rational -> UnitInterval -> Double
leaderProbability activeSlotCoeff relativeStake decentralizationParameter =
  (1 - (1 - asc) ** s) * (1 - d')
  where
    d' = realToFrac . unitIntervalToRational $ decentralizationParameter
    asc = realToFrac . unitIntervalToRational . activeSlotVal $ activeSlotCoeff
    s = realToFrac relativeStake

samplePositions :: StrictSeq Double
samplePositions = (\x -> (x + 0.5) / 100.0) <$> StrictSeq.fromList [0.0 .. 99.0]

likelihood ::
  Natural -> -- number of blocks produced this epoch
  Double -> -- chance we're allowed to produce a block in this slot
  EpochSize ->
  Likelihood
likelihood blocks t slotsPerEpoch =
  Likelihood $
    sample <$> samplePositions
  where
    -- The likelihood function L(x) is the probability of observing the data we got
    -- under the assumption that the underlying pool performance is equal to x.
    -- L(x) = C(n,m) * (tx)^n * (1-tx)^m
    -- where
    -- t is the chance we're allowed to produce a block
    -- n is the number of slots in which a block was produced
    -- m is the number of slots in which a block was not produced
    --      (slots per epoch minus n)
    -- C(n,m) is a coefficient that will be irrelevant
    -- Since the likelihood function only matters up to a scalar multiple, we will
    -- will divide out C(n,m) t^n and use the following instead:
    -- L(x) = x^n * (1-tx)^m
    -- We represent this function using 100 sample points, but to avoid very
    -- large exponents, we store the log of the value instead of the value itself.
    -- log(L(x)) = log [ x^n * (1-tx)^m ]
    --           = n * log(x) + m * log(1 - tx)
    -- TODO: worry more about loss of floating point precision
    --
    -- example:
    -- a pool has relative stake of 1 / 1,000,000 (~ 30k ada of 35b ada)
    -- f = active slot coefficient = 1/20
    -- t = 1 - (1-f)^(1/1,000,000)
    n = fromIntegral blocks
    m = fromIntegral $ slotsPerEpoch - fromIntegral blocks
    l :: Double -> Double
    l x = n * log x + m * log (1 - t * x)
    sample position = LogWeight (realToFrac $ l position)

-- | Decay previous likelihood
applyDecay :: Float -> Likelihood -> Likelihood
applyDecay decay (Likelihood logWeights) = Likelihood $ mul decay <$> logWeights
  where
    mul x (LogWeight f) = LogWeight (x * f)

posteriorDistribution :: Histogram -> Likelihood -> Histogram
posteriorDistribution (Histogram points) (Likelihood likelihoods) =
  normalize $
    Histogram $ strictSeqZipWith (+) points likelihoods

-- | Normalize the histogram so that the total area is 1
normalize :: Histogram -> Histogram
normalize (Histogram values) = Histogram $ (\x -> x - logArea) <$> values'
  where
    m = maximum values
    values' = (\x -> x - m) <$> values
    logArea = toLogWeight area
    area = reimannSum 0.01 (fromLogWeight <$> values')

-- | Calculate the k percentile for this distribution.
-- k is a value between 0 and 1. The 0 percentile is 0 and the 1 percentile is 1
percentile :: Double -> Histogram -> Likelihood -> PerformanceEstimate
percentile p prior likelihoods =
  PerformanceEstimate . fst $
    fromMaybe (1, 1) $
      find (\(_x, fx) -> fx > p) cdf
  where
    (Histogram values) = posteriorDistribution prior likelihoods
    cdf =
      Seq.zip
        (StrictSeq.getSeq samplePositions)
        (StrictSeq.getSeq (StrictSeq.scanl (+) 0 (fromLogWeight <$> values)))

percentile' :: Likelihood -> PerformanceEstimate
percentile' = percentile 0.5 h
  where
    h = normalize . Histogram $ logBeta 40 1 <$> samplePositions
    -- Beta(n,m)(x) = C * x^(n-1)*(1-x)^(m-1)
    -- log( Beta(n,m)(x) ) = (n-1) * log x + (m-1) * log (1-x)
    logBeta n m x = LogWeight . realToFrac $ (n -1) * log x + (m -1) * log (1 - x)

reimannSum :: (Functor f, Foldable f) => Double -> f Double -> Double
reimannSum width heights = sum $ fmap (width *) heights

-- | This is a estimate of the proportion of allowed blocks a pool will
-- make in the future. It is used for ranking pools in delegation.
newtype PerformanceEstimate = PerformanceEstimate {unPerformanceEstimate :: Double}
  deriving (Show, Eq, Generic, NoThunks)

instance ToCBOR PerformanceEstimate where
  toCBOR = encodeDouble . unPerformanceEstimate

instance FromCBOR PerformanceEstimate where
  fromCBOR = PerformanceEstimate <$> decodeDouble

data NonMyopic era = NonMyopic
  { likelihoodsNM :: !(Map (KeyHash 'StakePool (Crypto era)) Likelihood),
    rewardPotNM :: !Coin
  }
  deriving (Show, Eq, Generic)

emptyNonMyopic :: NonMyopic era
emptyNonMyopic = NonMyopic Map.empty (Coin 0)

instance NoThunks (NonMyopic era)

instance NFData (NonMyopic era)

instance Era era => ToCBOR (NonMyopic era) where
  toCBOR
    NonMyopic
      { likelihoodsNM = aps,
        rewardPotNM = rp
      } =
      encodeListLen 3
        <> toCBOR aps
        <> toCBOR rp

instance Era era => FromCBOR (NonMyopic era) where
  fromCBOR = do
    decodeRecordNamed "NonMyopic" (const 3) $ do
      aps <- fromCBOR
      rp <- fromCBOR
      pure $
        NonMyopic
          { likelihoodsNM = aps,
            rewardPotNM = rp
          }

-- | Desirability calculation for non-myopic utily,
-- corresponding to f^~ in section 5.6.1 of
-- "Design Specification for Delegation and Incentives in Cardano"
desirability ::
  PParams era ->
  Coin ->
  PoolParams era ->
  PerformanceEstimate ->
  Coin ->
  Double
desirability pp r pool (PerformanceEstimate p) (Coin totalStake) =
  if fTilde <= cost
    then 0
    else (fTilde - cost) * (1 - margin)
  where
    fTilde = fTildeNumer / fTildeDenom
    fTildeNumer = p * fromRational (coinToRational r * (z0 + min s z0 * a0))
    fTildeDenom = fromRational $ 1 + a0
    cost = (fromRational . coinToRational . _poolCost) pool
    margin = (fromRational . unitIntervalToRational . _poolMargin) pool
    tot = max 1 (fromIntegral totalStake)
    Coin pledge = _poolPledge pool
    s = fromIntegral pledge % tot
    a0 = _a0 pp
    z0 = 1 % max 1 (fromIntegral (_nOpt pp))

-- | Computes the top ranked stake pools
-- corresponding to section 5.6.1 of
-- "Design Specification for Delegation and Incentives in Cardano"
getTopRankedPools ::
  Coin ->
  Coin ->
  PParams era ->
  Map (KeyHash 'StakePool (Crypto era)) (PoolParams era) ->
  Map (KeyHash 'StakePool (Crypto era)) PerformanceEstimate ->
  Set (KeyHash 'StakePool (Crypto era))
getTopRankedPools rPot totalStake pp poolParams aps =
  Set.fromList $
    fmap fst $
      take (fromIntegral $ _nOpt pp) (sortBy (flip compare `on` snd) rankings)
  where
    pdata = Map.toList $ Map.intersectionWith (,) poolParams aps
    rankings =
      [ ( hk,
          desirability pp rPot pool ap totalStake
        )
        | (hk, (pool, ap)) <- pdata
      ]

-- | StakeShare type
newtype StakeShare = StakeShare {unStakeShare :: Rational}
  deriving (Generic, Ord, Eq, NoThunks)
  deriving (Show) via Quiet StakeShare

-- | Calculate pool reward
mkApparentPerformance ::
  UnitInterval ->
  Rational ->
  Natural ->
  Natural ->
  Rational
mkApparentPerformance d_ sigma blocksN blocksTotal
  | sigma == 0 = 0
  | unitIntervalToRational d_ < 0.8 = beta / sigma
  | otherwise = 1
  where
    beta = fromIntegral blocksN / fromIntegral (max 1 blocksTotal)

-- | Calculate pool leader reward
leaderRew ::
  Coin ->
  PoolParams era ->
  StakeShare ->
  StakeShare ->
  Coin
leaderRew f pool (StakeShare s) (StakeShare sigma)
  | f <= c = f
  | otherwise =
    c
      <> rationalToCoinViaFloor
        (coinToRational (f <-> c) * (m' + (1 - m') * s / sigma))
  where
    (c, m, _) = poolSpec pool
    m' = unitIntervalToRational m

-- | Calculate pool member reward
memberRew ::
  Coin ->
  PoolParams era ->
  StakeShare ->
  StakeShare ->
  Coin
memberRew (Coin f') pool (StakeShare t) (StakeShare sigma)
  | f' <= c = mempty
  | otherwise =
    rationalToCoinViaFloor $
      fromIntegral (f' - c) * (1 - m') * t / sigma
  where
    (Coin c, m, _) = poolSpec pool
    m' = unitIntervalToRational m

-- | Reward one pool
rewardOnePool ::
  PParams era ->
  Coin ->
  Natural ->
  Natural ->
  PoolParams era ->
  Stake era ->
  Rational ->
  Rational ->
  Coin ->
  Set (Credential 'Staking era) ->
  Map (Credential 'Staking era) Coin
rewardOnePool
  pp
  r
  blocksN
  blocksTotal
  pool
  (Stake stake)
  sigma
  sigmaA
  (Coin totalStake)
  addrsRew =
    rewards'
    where
      Coin ostake =
        Set.foldl'
          (\c o -> c <> (fromMaybe mempty $ Map.lookup (KeyHashObj o) stake))
          mempty
          (_poolOwners pool)
      Coin pledge = _poolPledge pool
      pr = fromIntegral pledge % fromIntegral totalStake
      (Coin maxP) =
        if pledge <= ostake
          then maxPool pp r sigma pr
          else mempty
      appPerf = mkApparentPerformance (_d pp) sigmaA blocksN blocksTotal
      poolR = rationalToCoinViaFloor (appPerf * fromIntegral maxP)
      tot = fromIntegral totalStake
      mRewards =
        Map.fromList
          [ ( hk,
              memberRew
                poolR
                pool
                (StakeShare (fromIntegral c % tot))
                (StakeShare sigma)
            )
            | (hk, Coin c) <- Map.toList stake,
              notPoolOwner hk
          ]
      notPoolOwner (KeyHashObj hk) = hk `Set.notMember` _poolOwners pool
      notPoolOwner (ScriptHashObj _) = False
      lReward =
        leaderRew
          poolR
          pool
          (StakeShare $ fromIntegral ostake % tot)
          (StakeShare sigma)
      f =
        if HardForks.aggregatedRewards pp
          then Map.insertWith (<>)
          else Map.insert
      potentialRewards =
        f (getRwdCred $ _poolRAcnt pool) lReward mRewards
      rewards' = Map.filter (/= Coin 0) $ eval (addrsRew ◁ potentialRewards)

reward ::
  PParams era ->
  BlocksMade era ->
  Coin ->
  Set (Credential 'Staking era) ->
  Map (KeyHash 'StakePool (Crypto era)) (PoolParams era) ->
  Stake era ->
  Map (Credential 'Staking era) (KeyHash 'StakePool (Crypto era)) ->
  Coin ->
  ActiveSlotCoeff ->
  EpochSize ->
  ( Map
      (Credential 'Staking era)
      Coin,
    Map (KeyHash 'StakePool (Crypto era)) Likelihood
  )
reward
  pp
  (BlocksMade b)
  r
  addrsRew
  poolParams
  stake
  delegs
  (Coin totalStake)
  asc
  slotsPerEpoch = (rewards', hs)
    where
      totalBlocks = sum b
      Coin activeStake = fold . unStake $ stake
      results = do
        (hk, pparams) <- Map.toList poolParams
        let sigma = if totalStake == 0 then 0 else fromIntegral pstake % fromIntegral totalStake
            sigmaA = if activeStake == 0 then 0 else fromIntegral pstake % fromIntegral activeStake
            blocksProduced = Map.lookup hk b
            actgr@(Stake s) = poolStake hk delegs stake
            Coin pstake = fold s
            rewardMap = case blocksProduced of
              Nothing -> Nothing -- This is equivalent to calling rewarOnePool with n = 0
              Just n ->
                Just $
                  rewardOnePool
                    pp
                    r
                    n
                    totalBlocks
                    pparams
                    actgr
                    sigma
                    sigmaA
                    (Coin totalStake)
                    addrsRew
            ls =
              likelihood
                (fromMaybe 0 blocksProduced)
                (leaderProbability asc sigma (_d pp))
                slotsPerEpoch
        pure (hk, rewardMap, ls)
      f =
        if HardForks.aggregatedRewards pp
          then Map.unionsWith (<>)
          else Map.unions
      rewards' = f . catMaybes $ fmap (\(_, x, _) -> x) results
      hs = Map.fromList $ fmap (\(hk, _, l) -> (hk, l)) results

-- | Compute the Non-Myopic Pool Stake
--
--   This function implements non-myopic stake calculation in section 5.6.2
--   of "Design Specification for Delegation and Incentives in Cardano".
--   Note that the protocol parameters are implicit in the design document.
--   Additionally, instead of passing a rank r to compare with k,
--   we pass the top k desirable pools and check for membership.
nonMyopicStake ::
  PParams era ->
  StakeShare ->
  StakeShare ->
  StakeShare ->
  KeyHash 'StakePool (Crypto era) ->
  Set (KeyHash 'StakePool (Crypto era)) ->
  StakeShare
nonMyopicStake pp (StakeShare s) (StakeShare sigma) (StakeShare t) kh topPools =
  let z0 = 1 % max 1 (fromIntegral (_nOpt pp))
   in if kh `Set.member` topPools
        then StakeShare (max (sigma + t) z0)
        else StakeShare (s + t)

-- | Compute the Non-Myopic Pool Member Reward
--
--   This function implements equation (3) in section 5.6.4
--   of "Design Specification for Delegation and Incentives in Cardano".
--   Note that the protocol parameters and the reward pot are implicit
--   in the design document. Additionally, instead of passing a rank
--   r to compare with k, we pass the top k desirable pools and
--   check for membership.
nonMyopicMemberRew ::
  PParams era ->
  Coin ->
  PoolParams era ->
  StakeShare ->
  StakeShare ->
  StakeShare ->
  Set (KeyHash 'StakePool (Crypto era)) ->
  PerformanceEstimate ->
  Coin
nonMyopicMemberRew
  pp
  rPot
  pool
  s
  sigma
  t
  topPools
  (PerformanceEstimate p) =
    let nm = nonMyopicStake pp s sigma t (_poolId pool) topPools
        f = maxPool pp rPot (unStakeShare nm) (unStakeShare s)
        fHat = floor (p * (fromRational . coinToRational) f)
     in memberRew (Coin fHat) pool t nm
