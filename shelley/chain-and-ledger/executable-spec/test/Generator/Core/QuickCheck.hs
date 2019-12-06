{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generator.Core.QuickCheck
  ( findPayKeyPair
  , genBool
  , genCoin
  , genCoinList
  , genInteger
  , genNatural
  , genTxOut
  , genUtxo0
  , increasingProbabilityAt
  , mkGenesisLedgerState
  , coreKeyPairs
  , traceCoreKeyPairs
  , traceKeyPairs
  , traceVRFKeyPairs
  , someKeyPairs
  , pickStakeKey
  , toAddr
  , toCred)
  where

import           Cardano.Crypto.VRF (deriveVerKeyVRF, genKeyVRF)
import           Control.Monad (replicateM)
import           Crypto.Random (drgNewTest, withDRG)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (fromList)
import           Data.Tuple (swap)
import           Data.Word (Word64)

import           Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

import           Address (toAddr, toCred)
import           Coin (Coin (..))
import           Control.State.Transition (IRC)
import           Keys (pattern KeyPair, hashKey, sKey, vKey)
import           LedgerState (pattern LedgerState, genesisCoins, genesisState)
import           MockTypes (Addr, CoreKeyPair, DPState, GenKeyHash, KeyHash, KeyPair, KeyPairs,
                     LEDGER, SignKeyVRF, TxOut, UTxO, UTxOState, VKey, VerKeyVRF)
import           Numeric.Natural (Natural)
import           Test.Utils (mkGenKey, mkKeyPair)
import           Tx (pattern TxOut)
import           TxData (pattern AddrBase, pattern KeyHashObj)

genBool :: Gen Bool
genBool = QC.arbitraryBoundedRandom

genInteger :: Integer -> Integer -> Gen Integer
genInteger lower upper = QC.choose (lower, upper)

-- | Generator for a natural number between 'lower' and 'upper'
genNatural :: Natural -> Natural -> Gen Natural
genNatural lower upper = fromInteger <$> QC.choose (lower', upper')
 where
  lower' = fromIntegral lower
  upper' = fromIntegral upper

mkKeyPairs :: Word64 -> (KeyPair, KeyPair)
mkKeyPairs n
  = (mkKeyPair_ (2*n), mkKeyPair_ (2*n+1))
  where
    mkKeyPair_ n_ = (uncurry KeyPair . swap) (mkKeyPair (n_,n_,n_,n_,n_))

-- | Constant list of KeyPairs intended to be used in the generators.
traceKeyPairs :: KeyPairs
traceKeyPairs = mkKeyPairs <$> [1 .. 150]

numCoreNodes :: Word64
numCoreNodes = 7

-- Pairs of (genesis key, node cold key)
--
-- NOTE: we use a seed range in the [1000...] range
-- to create keys that don't overlap with any of the other generated keys
coreNodes :: [(CoreKeyPair, KeyPair)]
coreNodes = [ ( (toKeyPair . mkGenKey) (x, 0, 0, 0, 0)
              , (toKeyPair . mkKeyPair) (x, 0, 0, 0, 1))
            | x <- [1001..1000+numCoreNodes]]
          where
            toKeyPair (sk,vk) = KeyPair {sKey = sk, vKey = vk}

coreKeyPairs :: [CoreKeyPair]
coreKeyPairs = fst . unzip $ coreNodes

-- | Select between _lower_ and _upper_ keys from 'traceKeyPairs'
someKeyPairs :: Int -> Int -> Gen KeyPairs
someKeyPairs lower upper =
  take
    <$> QC.choose (lower, upper)
    <*> QC.shuffle traceKeyPairs

-- | Find first matching key pair for address. Returns the matching key pair
-- where the first element of the pair matched the hash in 'addr'.
findPayKeyPair :: Addr -> KeyPairs -> KeyPair
findPayKeyPair (AddrBase (KeyHashObj addr) _) keyList =
    case matches of
      []    -> error "findPayKeyPair: could not find a match for the given address"
      (x:_) -> fst x
    where
      matches = filter (\(pay, _) -> addr == hashKey (vKey pay)) keyList
findPayKeyPair _ _ = error "findPayKeyPair: expects only AddrBase addresses"

-- | Select one random verification staking key from list of pairs of KeyPair.
pickStakeKey :: KeyPairs -> Gen VKey
pickStakeKey keys = vKey . snd <$> QC.elements keys

-- | Generates a list of coins for the given 'Addr' and produced a 'TxOut' for each 'Addr'
--
-- Note: we need to keep the initial utxo coin sizes large enough so that
-- when we simulate sequences of transactions, we have enough funds available
-- to include certificates that require deposits.
genTxOut :: [Addr] -> Gen [TxOut]
genTxOut addrs = do
  ys <- genCoinList 1000 10000 (length addrs) (length addrs)
  return (uncurry TxOut <$> zip addrs ys)

-- | Generates a list of 'Coin' values of length between 'lower' and 'upper'
-- and with values between 'minCoin' and 'maxCoin'.
genCoinList :: Integer -> Integer -> Int -> Int -> Gen [Coin]
genCoinList minCoin maxCoin lower upper = do
  len <- QC.choose (lower, upper)
  replicateM len $ genCoin minCoin maxCoin

-- TODO this should be an exponential distribution, not constant
genCoin :: Integer -> Integer -> Gen Coin
genCoin minCoin maxCoin = Coin <$> QC.choose (minCoin, maxCoin)

genUtxo0 :: Int -> Int -> Gen UTxO
genUtxo0 lower upper = do
  genesisKeys <- someKeyPairs lower upper
  outs <- genTxOut (fmap toAddr genesisKeys)
  return (genesisCoins outs)

genesisDelegs0 :: Map GenKeyHash KeyHash
genesisDelegs0
  = Map.fromList
      [ (hashVKey gkey, hashVKey pkey)
      | (gkey, pkey) <- coreNodes]
  where
    hashVKey = hashKey . vKey

-- | Generate initial state for the LEDGER STS using the STS environment.
--
-- Note: this function must be usable in place of 'applySTS' and needs to align
-- with the signature 'RuleContext sts -> Gen (Either [[PredicateFailure sts]] (State sts))'.
-- To achieve this we (1) use 'IRC LEDGER' (the "initial rule context") instead of simply 'LedgerEnv'
-- and (2) always return Right (since this function does not raise predicate failures).
mkGenesisLedgerState
  :: IRC LEDGER
  -> Gen (Either a (UTxOState, DPState))
mkGenesisLedgerState _ = do
  utxo0 <- genUtxo0 5 10
  let (LedgerState utxoSt dpSt _) = genesisState genesisDelegs0 utxo0
  pure $ Right (utxoSt, dpSt)

-- | Generate values the given distribution in 90% of the cases, and values at
-- the bounds of the range in 10% of the cases.
--
-- This can be used to generate enough extreme values. The exponential and
-- linear distributions provided by @hedgehog@ will generate a small percentage
-- of these (0-1%).
increasingProbabilityAt
  :: Gen a
  -> (a, a)
  -> Gen a
increasingProbabilityAt gen (lower, upper)
  = QC.frequency [ (5, pure lower)
                 , (90, gen)
                 , (5, pure upper)
                 ]

-- | A pre-populated space of VRF keys for use in the generators.
traceVRFKeyPairs :: [(SignKeyVRF, VerKeyVRF)]
traceVRFKeyPairs = [body (0,0,0,0,i) | i <- [1 .. 50]]
 where
  body seed = fst . withDRG (drgNewTest seed) $ do
    sk <- genKeyVRF
    return (sk, deriveVerKeyVRF sk)

-- | A pre-populated space of core node keys
traceCoreKeyPairs :: [CoreKeyPair]
traceCoreKeyPairs = mkGenKeys <$> [1..7]

mkGenKeys :: Word64 -> CoreKeyPair
mkGenKeys n = (uncurry KeyPair . swap) (mkGenKey (n, n , n, n, n))