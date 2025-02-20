{-# LANGUAGE DataKinds #-}

-- |
-- Module      : Test.Cardano.Ledger.Mary.Examples.Cast
-- Description : Cast of characters for Mary ledger examples
--
-- The cast of Characters for Mary Ledger Examples
module Test.Cardano.Ledger.Mary.Examples.Cast
  ( alicePay,
    aliceStake,
    aliceAddr,
    bobPay,
    bobStake,
    bobAddr,
    carlPay,
    carlStake,
    carlAddr,
    dariaPay,
    dariaStake,
    dariaAddr,
  )
where

import Cardano.Ledger.Mary (MaryEra)
import Shelley.Spec.Ledger.Address (Addr (..))
import Shelley.Spec.Ledger.Keys
  ( KeyPair (..),
    KeyRole (..),
  )
import Test.Cardano.Ledger.EraBuffet (TestCrypto)
import Test.Shelley.Spec.Ledger.Utils (mkAddr, mkKeyPair)

type MaryTest = MaryEra TestCrypto

-- | Alice's payment key pair
alicePay :: KeyPair 'Payment TestCrypto
alicePay = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (0, 0, 0, 0, 0)

-- | Alice's stake key pair
aliceStake :: KeyPair 'Staking TestCrypto
aliceStake = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (1, 1, 1, 1, 1)

-- | Alice's base address
aliceAddr :: Addr MaryTest
aliceAddr = mkAddr (alicePay, aliceStake)

-- | Bob's payment key pair
bobPay :: KeyPair 'Payment TestCrypto
bobPay = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (2, 2, 2, 2, 2)

-- | Bob's stake key pair
bobStake :: KeyPair 'Staking TestCrypto
bobStake = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (3, 3, 3, 3, 3)

-- | Bob's address
bobAddr :: Addr MaryTest
bobAddr = mkAddr (bobPay, bobStake)

-- Carl's payment key pair
carlPay :: KeyPair 'Payment TestCrypto
carlPay = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (4, 4, 4, 4, 4)

-- | Carl's stake key pair
carlStake :: KeyPair 'Staking TestCrypto
carlStake = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (5, 5, 5, 5, 5)

-- | Carl's address
carlAddr :: Addr MaryTest
carlAddr = mkAddr (carlPay, carlStake)

-- | Daria's payment key pair
dariaPay :: KeyPair 'Payment TestCrypto
dariaPay = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (6, 6, 6, 6, 6)

-- | Daria's stake key pair
dariaStake :: KeyPair 'Staking TestCrypto
dariaStake = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (7, 7, 7, 7, 7)

-- | Daria's address
dariaAddr :: Addr MaryTest
dariaAddr = mkAddr (dariaPay, dariaStake)
