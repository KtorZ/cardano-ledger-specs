{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Test.Shelley.Spec.Ledger.Generator.ScriptClass
  ( ScriptClass (..),
    Quantifier (..),
    exponential,
    anyOf,
    allOf,
    mOf,
    keyPairs,
    mkPayScriptHashMap,
    mkStakeScriptHashMap,
    mkScriptsFromKeyPair,
    mkKeyPairs,
    mkScripts,
    mkScriptCombinations,
    combinedScripts,
    someScripts,
    scriptKeyCombinations,
    scriptKeyCombination,
  )
where

import Cardano.Crypto.DSIGN.Class (DSIGNAlgorithm (..))
import Cardano.Ledger.Core (Script)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Crypto (DSIGN)
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Era (..))
import Data.List (permutations)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Proxy
import Data.Tuple (swap)
import Data.Word (Word64)
import Shelley.Spec.Ledger.Keys (KeyHash, KeyPair (..), KeyRole (..), asWitness, hashKey, vKey)
import Shelley.Spec.Ledger.LedgerState (KeyPairs)
import Shelley.Spec.Ledger.Scripts (ScriptHash)
import Shelley.Spec.Ledger.Tx (ValidateScript (..))
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC
import Test.Shelley.Spec.Ledger.Generator.Constants
  ( Constants (..),
  )
import Test.Shelley.Spec.Ledger.Utils (mkKeyPair)

{------------------------------------------------------------------------------
  ScriptClass defines the operations that enable an Era's scripts to
  be adapated to property tests. This is a key component of the EraGen class.
------------------------------------------------------------------------------}

class
  ( Eq (Script era),
    ValidateScript era,
    CC.Crypto (Crypto era),
    Era era
  ) =>
  ScriptClass era
  where
  basescript :: Proxy era -> KeyHash 'Witness (Crypto era) -> Script era
  isKey :: Proxy era -> Script era -> Maybe (KeyHash 'Witness (Crypto era))
  quantify :: Proxy era -> Script era -> Quantifier (Script era)
  unQuantify :: Proxy era -> Quantifier (Script era) -> Script era

{------------------------------------------------------------------------------
  Abstracts the quantifier structure of (Script era)
  used in the 'quantify' and 'unQuantify' methods of ScriptClass.
 -----------------------------------------------------------------------------}

data Quantifier t = AllOf [t] | AnyOf [t] | MOf Int [t] | Leaf t

anyOf :: forall era. ScriptClass era => Proxy era -> [Script era] -> Script era
anyOf prox xs = unQuantify prox $ AnyOf xs

allOf :: forall era. ScriptClass era => Proxy era -> [Script era] -> Script era
allOf prox xs = unQuantify prox $ AllOf xs

mOf :: forall era. ScriptClass era => Proxy era -> Int -> [Script era] -> Script era
mOf prox m xs = unQuantify prox $ MOf m xs

{------------------------------------------------------------------------------
  Compute lists of keyHashes
------------------------------------------------------------------------------}

-- | return the first sublist that meets the predicate p.
getFirst :: ([a] -> Bool) -> [[a]] -> [a]
getFirst _p [] = []
getFirst p (xs : xss) = if p xs then xs else getFirst p xss

-- | Return some valid list of KeyHashes that appear in a Script
--   Try not to return the empty list if there is at least on
--   Leaf that requires a key hash.
scriptKeyCombination ::
  forall era.
  ScriptClass era =>
  Proxy era ->
  Script era ->
  [KeyHash 'Witness (Crypto era)]
scriptKeyCombination prox script = case quantify prox script of
  AllOf xs -> concatMap (scriptKeyCombination prox) xs
  AnyOf xs -> getFirst (not . null) (map (scriptKeyCombination prox) xs)
  MOf m xs -> concatMap (scriptKeyCombination prox) (take m xs)
  Leaf t -> case isKey prox t of
    Just hk -> [hk]
    Nothing -> []

-- | Return all valid lists of KeyHashes that appear in a Script
--   used in testing.
scriptKeyCombinations ::
  forall era.
  ScriptClass era =>
  Proxy era ->
  Script era ->
  [[KeyHash 'Witness (Crypto era)]]
scriptKeyCombinations prox script = case quantify prox script of
  AllOf xs -> [concat $ concatMap (scriptKeyCombinations prox) xs]
  AnyOf xs -> concatMap (scriptKeyCombinations prox) xs
  MOf m xs ->
    let perms = map (take m) $ permutations xs
     in map (concat . concatMap (scriptKeyCombinations prox)) perms
  Leaf t -> case isKey prox t of
    Just hk -> [[hk]]
    Nothing -> [[]]

mkScriptFromKey :: forall era. (ScriptClass era) => KeyPair 'Witness (Crypto era) -> Core.Script era
mkScriptFromKey = (basescript (Proxy :: Proxy era) . hashKey . vKey)

mkScriptsFromKeyPair ::
  forall era.
  (ScriptClass era) =>
  (KeyPair 'Payment (Crypto era), KeyPair 'Staking (Crypto era)) ->
  (Core.Script era, Core.Script era)
mkScriptsFromKeyPair (k0, k1) =
  (mkScriptFromKey @era $ asWitness k0, mkScriptFromKey @era $ asWitness k1)

-- | make Scripts based on the given key pairs
mkScripts ::
  forall era.
  (ScriptClass era) =>
  KeyPairs (Crypto era) ->
  [(Core.Script era, Core.Script era)]
mkScripts = map (mkScriptsFromKeyPair @era)

mkPayScriptHashMap ::
  (ScriptClass era) =>
  [(Core.Script era, Core.Script era)] ->
  Map.Map (ScriptHash era) (Core.Script era, Core.Script era)
mkPayScriptHashMap scripts =
  Map.fromList (f <$> scripts)
  where
    f script@(pay, _stake) = (hashScript pay, script)

-- | Generate a mapping from stake script hash to script pair.
mkStakeScriptHashMap ::
  (ScriptClass era) =>
  [(Core.Script era, Core.Script era)] ->
  Map.Map (ScriptHash era) (Core.Script era, Core.Script era)
mkStakeScriptHashMap scripts =
  Map.fromList (f <$> scripts)
  where
    f script@(_pay, stake) = (hashScript stake, script)

-- | Combine a list of script pairs into hierarchically structured multi-sig
-- scripts, list must have at least length 3. Be careful not to call with too
-- many pairs in order not to create too many of the possible combinations.
mkScriptCombinations ::
  forall era.
  (ScriptClass era) =>
  [(Core.Script era, Core.Script era)] ->
  [(Core.Script era, Core.Script era)]
mkScriptCombinations msigs =
  if length msigs < 3
    then error "length of input msigs must be at least 3"
    else
      ( List.foldl' (++) [] $
          do
            (k1, k2) <- msigs
            (k3, k4) <- msigs List.\\ [(k1, k2)]
            (k5, k6) <- msigs List.\\ [(k1, k2), (k3, k4)]

            pure
              [ (pay, stake)
                | pay <-
                    [ anyOf (Proxy @era) [k1, k3, k5],
                      allOf (Proxy @era) [k1, k3, k5],
                      mOf (Proxy @era) 1 [k1, k3, k5],
                      mOf (Proxy @era) 2 [k1, k3, k5],
                      mOf (Proxy @era) 3 [k1, k3, k5]
                    ],
                  stake <-
                    [ anyOf (Proxy @era) [k2, k4, k6],
                      allOf (Proxy @era) [k2, k4, k6],
                      mOf (Proxy @era) 1 [k2, k4, k6],
                      mOf (Proxy @era) 2 [k2, k4, k6],
                      mOf (Proxy @era) 3 [k2, k4, k6]
                    ]
              ]
      ) ::
        [(Core.Script era, Core.Script era)]

baseScripts ::
  forall era.
  ScriptClass era =>
  Constants ->
  [(Core.Script era, Core.Script era)]
baseScripts c = mkScripts @era (keyPairs c)

combinedScripts ::
  forall era.
  ScriptClass era =>
  Constants ->
  [(Core.Script era, Core.Script era)]
combinedScripts c@(Constants {numBaseScripts}) =
  mkScriptCombinations @era . take numBaseScripts $ baseScripts @era c

-- | Select between _lower_ and _upper_ scripts from the possible combinations
-- of the first `numBaseScripts` multi-sig scripts of `mSigScripts`.
someScripts ::
  forall era.
  ScriptClass era =>
  Constants ->
  Int ->
  Int ->
  Gen [(Core.Script era, Core.Script era)]
someScripts c lower upper =
  take
    <$> QC.choose (lower, upper)
    <*> QC.shuffle (combinedScripts @era c)

-- | Constant list of KeyPairs intended to be used in the generators.
keyPairs :: CC.Crypto crypto => Constants -> KeyPairs crypto
keyPairs Constants {maxNumKeyPairs} = mkKeyPairs <$> [1 .. maxNumKeyPairs]

mkKeyPairs ::
  (DSIGNAlgorithm (DSIGN crypto)) =>
  Word64 ->
  (KeyPair kr crypto, KeyPair kr' crypto)
mkKeyPairs n =
  (mkKeyPair_ (2 * n), mkKeyPair_ (2 * n + 1))
  where
    mkKeyPair_ n_ =
      (uncurry KeyPair . swap)
        (mkKeyPair (n_, n_, n_, n_, n_))

{------------------------------------------------------------------------------
  How to be a Generic Value
------------------------------------------------------------------------------}

exponential :: Integer -> Integer -> Gen Integer
exponential minc maxc = QC.frequency spread
  where
    width = (maxc - minc) `div` n
    deltas = [QC.choose (minc + (i -1) * width, minc + i * width) | i <- [1 .. n]]
    scales = [1, 2, 4, 6, 4, 2, 1]
    n = fromIntegral (length scales)
    spread = zip scales deltas
