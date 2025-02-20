{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.Mary.Value
  ( PolicyID (..),
    AssetName (..),
    Value (..),
    insert,
    lookup,
    policies,
    prune,
    showValue,
  )
where

import Cardano.Binary
  ( Decoder,
    Encoding,
    FromCBOR,
    ToCBOR,
    TokenType (..),
    decodeInt64,
    decodeWord64,
    fromCBOR,
    peekTokenType,
    toCBOR,
  )
import qualified Cardano.Crypto.Hash.Class as Hash
import Cardano.Ledger.Compactible (Compactible (..))
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era
import Cardano.Ledger.Torsor (Torsor (..))
import Cardano.Ledger.Val
  ( DecodeMint (..),
    DecodeNonNegative (..),
    EncodeMint (..),
    Val (..),
  )
import Control.DeepSeq (NFData (..))
import Control.Monad (guard)
import Data.Array (Array)
import Data.Array.IArray (array)
import Data.ByteString (ByteString)
import Data.CannonicalMaps
  ( cannonicalMap,
    cannonicalMapUnion,
    pointWise,
  )
import Data.Coders
  ( Decode (..),
    Encode (..),
    decode,
    encode,
    (!>),
    (<!),
  )
import Data.Group (Abelian, Group (..))
import Data.Map.Internal
  ( Map (..),
    link,
    link2,
    splitLookup,
  )
import Data.Map.Strict (assocs)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import Data.Word (Word64)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.Coin (Coin (..), integerToWord64)
import Shelley.Spec.Ledger.Scripts (ScriptHash (..))
import Shelley.Spec.Ledger.Serialization (decodeMap, encodeMap)
import Prelude hiding (lookup)

-- | Asset Name
newtype AssetName = AssetName {assetName :: ByteString}
  deriving newtype
    ( Show,
      Eq,
      ToCBOR,
      FromCBOR,
      Ord,
      NoThunks,
      NFData
    )

-- | Policy ID
newtype PolicyID era = PolicyID {policyID :: ScriptHash era}
  deriving (Show, Eq, ToCBOR, FromCBOR, Ord, NoThunks, NFData)

-- | The Value representing MultiAssets
data Value era = Value !Integer !(Map (PolicyID era) (Map AssetName Integer))
  deriving (Show, Generic)

instance Era era => Eq (Value era) where
  x == y = pointwise (==) x y

-- TODO make these specific
instance NFData (Value era)

instance NoThunks (Value era)

instance Semigroup (Value era) where
  Value c m <> Value c1 m1 =
    Value (c + c1) (cannonicalMapUnion (cannonicalMapUnion (+)) m m1)

instance Monoid (Value era) where
  mempty = Value 0 mempty

instance Group (Value era) where
  invert (Value c m) =
    Value
      (- c)
      (cannonicalMap (cannonicalMap ((-1 :: Integer) *)) m)

instance Abelian (Value era)

-- ===================================================
-- Make the Val instance of Value

instance Era era => Val (Value era) where
  s <×> (Value c v) =
    Value
      (fromIntegral s * c)
      (cannonicalMap (cannonicalMap ((fromIntegral s) *)) v)
  isZero (Value c v) = c == 0 && Map.null v
  coin (Value c _) = Coin c
  inject (Coin c) = Value c mempty
  modifyCoin f (Value c m) = Value n m where (Coin n) = f (Coin c)
  pointwise p (Value c x) (Value d y) = (p c d) && (pointWise (pointWise p) x y)

  size (Value _ v) =
    -- add uint for the Coin portion in this size calculation
    foldr accum uint v
    where
      -- add addrHashLen for each Policy ID
      accum u ans = foldr accumIns (ans + policyIdLen) u
        where
          -- add assetNameLen and uint for each asset of that Policy ID
          accumIns _ ans1 = ans1 + assetNameLen + uint
      -- TODO move these constants somewhere (they are also specified in CDDL)
      uint :: Integer
      uint = 9

      assetNameLen :: Integer
      assetNameLen = 32

      -- TODO dig up these constraints from Era
      -- address hash length is always same as Policy ID length
      policyIdLen :: Integer
      policyIdLen = 28

-- ==============================================================
-- CBOR

-- TODO filter out 0s at deserialization
-- TODO Probably the actual serialization will be of the formal Coin OR Value type
-- Maybe better to make this distinction in the TxOut de/serialization

decodeInteger :: Decoder s Integer
decodeInteger = fromIntegral <$> decodeInt64

decodeValue ::
  ( Typeable (Core.Script era),
    Era era
  ) =>
  Decoder s (Value era)
decodeValue = do
  tt <- peekTokenType
  case tt of
    TypeUInt -> inject . Coin <$> decodeInteger
    TypeNInt -> inject . Coin <$> decodeInteger
    TypeListLen -> decodeValuePair decodeInteger
    TypeListLen64 -> decodeValuePair decodeInteger
    TypeListLenIndef -> decodeValuePair decodeInteger
    _ -> fail $ "Value: expected array or int"

decodeValuePair ::
  ( Typeable (Core.Script era),
    Era era
  ) =>
  (forall t. Decoder t Integer) ->
  Decoder s (Value era)
decodeValuePair decodeAmount =
  decode $
    RecD Value
      <! D decodeAmount
      <! D (decodeMultiAssetMaps decodeAmount)

encodeMultiAssetMaps ::
  ( Typeable (Core.Script era),
    Era era
  ) =>
  Map (PolicyID era) (Map AssetName Integer) ->
  Encoding
encodeMultiAssetMaps = encodeMap toCBOR (encodeMap toCBOR toCBOR)

decodeMultiAssetMaps ::
  ( Typeable (Core.Script era),
    Era era
  ) =>
  Decoder s Integer ->
  Decoder s (Map (PolicyID era) (Map AssetName Integer))
decodeMultiAssetMaps decodeAmount =
  prune <$> decodeMap fromCBOR (decodeMap fromCBOR decodeAmount)

decodeNonNegativeInteger :: Decoder s Integer
decodeNonNegativeInteger = fromIntegral <$> decodeWord64

decodeNonNegativeValue ::
  ( Typeable (Core.Script era),
    Era era
  ) =>
  Decoder s (Value era)
decodeNonNegativeValue = do
  tt <- peekTokenType
  case tt of
    TypeUInt -> inject . Coin <$> decodeNonNegativeInteger
    TypeListLen -> decodeValuePair decodeNonNegativeInteger
    TypeListLen64 -> decodeValuePair decodeNonNegativeInteger
    TypeListLenIndef -> decodeValuePair decodeNonNegativeInteger
    _ -> fail $ "Value: expected array or int"

instance
  (Era era, Typeable (Core.Script era)) =>
  ToCBOR (Value era)
  where
  toCBOR (Value c v) =
    if Map.null v
      then toCBOR c
      else
        encode $
          Rec Value
            !> To c
            !> E encodeMultiAssetMaps v

instance
  (Era era, Typeable (Core.Script era)) =>
  FromCBOR (Value era)
  where
  fromCBOR = decodeValue

instance
  (Era era, Typeable (Core.Script era)) =>
  DecodeNonNegative (Value era)
  where
  decodeNonNegative = decodeNonNegativeValue

instance
  (Era era, Typeable (Core.Script era)) =>
  DecodeMint (Value era)
  where
  decodeMint = Value 0 <$> decodeMultiAssetMaps decodeInteger

instance
  (Era era, Typeable (Core.Script era)) =>
  EncodeMint (Value era)
  where
  encodeMint (Value _ multiasset) = encodeMultiAssetMaps multiasset

-- ========================================================================
-- Compactible
-- This is used in the TxOut which stores the (CompactForm Value).

instance Era era => Compactible (Value era) where
  newtype CompactForm (Value era) = CompactValue (CV era)
    deriving (Eq, Typeable, Show, ToCBOR, FromCBOR)
  toCompact x = CompactValue <$> toCV x
  fromCompact (CompactValue x) = fromCV x

instance (Typeable (Core.Script era), Era era) => ToCBOR (CV era) where
  toCBOR = toCBOR . fromCV

instance (Typeable (Core.Script era), Era era) => FromCBOR (CV era) where
  fromCBOR = do
    v <- decodeNonNegativeValue
    case toCV v of
      Nothing ->
        fail
          "impossible failure: decoded nonnegative value that cannot be compacted"
      Just x -> pure x

data CV era
  = CV
      {-# UNPACK #-} !Word64
      {-# UNPACK #-} !(Array Int (CVPart era))
  deriving (Eq, Show, Typeable)

data CVPart era
  = CVPart
      !(PolicyID era)
      {-# UNPACK #-} !AssetName
      {-# UNPACK #-} !Word64
  deriving (Eq, Show, Typeable)

toCV :: Value era -> Maybe (CV era)
toCV v = do
  let (c, triples) = gettriples v
      policyIDs = Set.fromList $ (\(x, _, _) -> x) <$> triples
      n = length triples - 1
  cvParts <- traverse (toCVPart policyIDs) triples
  let arr = array (0, n) (zip [0 .. n] cvParts)
  c' <- integerToWord64 c
  pure $ CV c' arr
  where
    deduplicate xs x = fromMaybe x $ do
      r <- Set.lookupLE x xs
      guard (x == r)
      pure r
    toCVPart policyIdSet (policyId, aname, amount) =
      CVPart (deduplicate policyIdSet policyId) aname
        <$> integerToWord64 amount

fromCV :: Era era => CV era -> Value era
fromCV (CV w vs) = foldr f (inject . Coin . fromIntegral $ w) vs
  where
    f (CVPart policyId aname amount) acc =
      insert (+) policyId aname (fromIntegral amount) acc

instance (Era era) => Torsor (Value era) where
  -- TODO a proper torsor form
  type Delta (Value era) = (Value era)
  addDelta = (<+>)
  toDelta = id

-- ========================================================================
-- Operations on Values

-- | Extract the set of policies in the Value.
--
--   This function is equivalent to computing the support of the value in the
--   spec.
policies :: Value era -> Set (PolicyID era)
policies (Value _ m) = Map.keysSet m

lookup :: PolicyID era -> AssetName -> Value era -> Integer
lookup pid aid (Value _ m) =
  case Map.lookup pid m of
    Nothing -> 0
    Just m2 -> Map.findWithDefault 0 aid m2

-- | insert comb policy asset n v,
--   if comb = \ old new -> old, the integer in the Value is prefered over n
--   if comb = \ old new -> new, then n is prefered over the integer in the Value
--   if (comb old new) == 0, then that value should not be stored in the Map part of the Value.
insert ::
  (Integer -> Integer -> Integer) ->
  PolicyID era ->
  AssetName ->
  Integer ->
  Value era ->
  Value era
insert combine pid aid new (Value cn m1) =
  case splitLookup pid m1 of
    (l1, Just m2, l2) ->
      case splitLookup aid m2 of
        (v1, Just old, v2) ->
          if n == 0
            then
              let m3 = (link2 v1 v2)
               in if Map.null m3
                    then Value cn (link2 l1 l2)
                    else Value cn (link pid m3 l1 l2)
            else Value cn (link pid (link aid n v1 v2) l1 l2)
          where
            n = combine old new
        (_, Nothing, _) ->
          Value
            cn
            ( link
                pid
                ( if new == 0
                    then m2
                    else (Map.insert aid new m2)
                )
                l1
                l2
            )
    (l1, Nothing, l2) ->
      Value
        cn
        ( if new == 0
            then link2 l1 l2
            else link pid (Map.singleton aid new) l1 l2
        )

-- ========================================================

-- | Remove 0 assets from a map
prune ::
  Map (PolicyID era) (Map AssetName Integer) ->
  Map (PolicyID era) (Map AssetName Integer)
prune assets =
  Map.filter (not . null) $ Map.filter (/= 0) <$> assets

-- | Display a Value as a String, one token per line
showValue :: Value era -> String
showValue v = show c ++ "\n" ++ unlines (map trans ts)
  where
    (c, ts) = gettriples v
    trans (PolicyID x, hash, cnt) =
      show x
        ++ ",  "
        ++ show hash
        ++ ",  "
        ++ show cnt

gettriples :: Value era -> (Integer, [(PolicyID era, AssetName, Integer)])
gettriples (Value c m1) = (c, triples)
  where
    triples =
      [ (policyId, aname, amount)
        | (policyId, m2) <- assocs m1,
          (aname, amount) <- assocs m2
      ]
