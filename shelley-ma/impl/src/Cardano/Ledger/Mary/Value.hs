{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
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
    valueFromList,
  )
where

import Cardano.Binary
  ( Decoder,
    DecoderError (..),
    Encoding,
    FromCBOR,
    ToCBOR,
    TokenType (..),
    decodeInteger,
    decodeWord64,
    fromCBOR,
    peekTokenType,
    toCBOR,
  )
import qualified Cardano.Crypto.Hash.Class as Hash
import Cardano.Ledger.Compactible (Compactible (..))
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Torsor (Torsor (..))
import Cardano.Ledger.Val
  ( DecodeMint (..),
    DecodeNonNegative (..),
    EncodeMint (..),
    Val (..),
  )
import Cardano.Prelude (cborError)
import Control.DeepSeq (NFData (..))
import Control.Monad (forM_)
import Control.Monad.ST (runST)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Short as SBS
import Data.ByteString.Short.Internal (ShortByteString (SBS))
import Data.CanonicalMaps
  ( canonicalMap,
    canonicalMapUnion,
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
import Data.List (nub, sort, sortBy)
import Data.Map.Internal
  ( Map (..),
    link,
    link2,
    splitLookup,
  )
import Data.Map.Strict (assocs)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import qualified Data.Primitive.ByteArray as BA
import Data.Set (Set)
import Data.Text.Encoding (decodeUtf8)
import Data.Typeable (Typeable)
import Data.Word (Word16, Word64)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..), OnlyCheckWhnfNamed (..))
import Shelley.Spec.Ledger.Coin (Coin (..), integerToWord64)
import Shelley.Spec.Ledger.Scripts (ScriptHash (..))
import Shelley.Spec.Ledger.Serialization (decodeMap, encodeMap)
import Prelude hiding (lookup)

-- | Asset Name
newtype AssetName = AssetName {assetName :: BS.ByteString}
  deriving newtype
    ( Show,
      Eq,
      ToCBOR,
      Ord,
      NoThunks,
      NFData
    )

instance FromCBOR AssetName where
  fromCBOR = do
    an <- fromCBOR
    if BS.length an > 32
      then cborError $ DecoderErrorCustom "asset name exceeds 32 bytes:" (decodeUtf8 an)
      else pure . AssetName $ an

-- | Policy ID
newtype PolicyID crypto = PolicyID {policyID :: ScriptHash crypto}
  deriving (Show, Eq, ToCBOR, FromCBOR, Ord, NoThunks, NFData)

-- | The Value representing MultiAssets
data Value crypto = Value !Integer !(Map (PolicyID crypto) (Map AssetName Integer))
  deriving (Show, Generic)

instance CC.Crypto crypto => Eq (Value crypto) where
  x == y = pointwise (==) x y

-- TODO make these specific
instance NFData (Value crypto)

instance NoThunks (Value crypto)

instance Semigroup (Value crypto) where
  Value c m <> Value c1 m1 =
    Value (c + c1) (canonicalMapUnion (canonicalMapUnion (+)) m m1)

instance Monoid (Value crypto) where
  mempty = Value 0 mempty

instance Group (Value crypto) where
  invert (Value c m) =
    Value
      (- c)
      (canonicalMap (canonicalMap ((-1 :: Integer) *)) m)

instance Abelian (Value crypto)

-- ===================================================
-- Make the Val instance of Value

instance CC.Crypto crypto => Val (Value crypto) where
  s <×> (Value c v) =
    Value
      (fromIntegral s * c)
      (canonicalMap (canonicalMap ((fromIntegral s) *)) v)
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

decodeValue ::
  CC.Crypto crypto =>
  Decoder s (Value crypto)
decodeValue = do
  tt <- peekTokenType
  case tt of
    TypeUInt -> inject . Coin <$> decodeInteger
    TypeUInt64 -> inject . Coin <$> decodeInteger
    TypeNInt -> inject . Coin <$> decodeInteger
    TypeNInt64 -> inject . Coin <$> decodeInteger
    TypeListLen -> decodeValuePair decodeInteger
    TypeListLen64 -> decodeValuePair decodeInteger
    TypeListLenIndef -> decodeValuePair decodeInteger
    _ -> fail $ "Value: expected array or int, got " ++ show tt

decodeValuePair ::
  CC.Crypto crypto =>
  (forall t. Decoder t Integer) ->
  Decoder s (Value crypto)
decodeValuePair decodeAmount =
  decode $
    RecD Value
      <! D decodeAmount
      <! D (decodeMultiAssetMaps decodeAmount)

encodeMultiAssetMaps ::
  CC.Crypto crypto =>
  Map (PolicyID crypto) (Map AssetName Integer) ->
  Encoding
encodeMultiAssetMaps = encodeMap toCBOR (encodeMap toCBOR toCBOR)

decodeMultiAssetMaps ::
  CC.Crypto crypto =>
  Decoder s Integer ->
  Decoder s (Map (PolicyID crypto) (Map AssetName Integer))
decodeMultiAssetMaps decodeAmount =
  prune <$> decodeMap fromCBOR (decodeMap fromCBOR decodeAmount)

decodeNonNegativeInteger :: Decoder s Integer
decodeNonNegativeInteger = fromIntegral <$> decodeWord64

decodeNonNegativeValue ::
  CC.Crypto crypto =>
  Decoder s (Value crypto)
decodeNonNegativeValue = do
  tt <- peekTokenType
  case tt of
    TypeUInt -> inject . Coin <$> decodeNonNegativeInteger
    TypeUInt64 -> inject . Coin <$> decodeNonNegativeInteger
    TypeListLen -> decodeValuePair decodeNonNegativeInteger
    TypeListLen64 -> decodeValuePair decodeNonNegativeInteger
    TypeListLenIndef -> decodeValuePair decodeNonNegativeInteger
    _ -> fail $ "Value: expected array or int, got " ++ show tt

instance
  CC.Crypto crypto =>
  ToCBOR (Value crypto)
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
  CC.Crypto crypto =>
  FromCBOR (Value crypto)
  where
  fromCBOR = decodeValue

instance
  CC.Crypto crypto =>
  DecodeNonNegative (Value crypto)
  where
  decodeNonNegative = decodeNonNegativeValue

instance
  CC.Crypto crypto =>
  DecodeMint (Value crypto)
  where
  decodeMint = Value 0 <$> decodeMultiAssetMaps decodeInteger

instance
  CC.Crypto crypto =>
  EncodeMint (Value crypto)
  where
  encodeMint (Value _ multiasset) = encodeMultiAssetMaps multiasset

-- ========================================================================
-- Compactible
-- This is used in the TxOut which stores the (CompactForm Value).

instance CC.Crypto crypto => Compactible (Value crypto) where
  newtype CompactForm (Value crypto) = CompactValue (CompactValue crypto)
    deriving (Eq, Typeable, Show, NoThunks, ToCBOR, FromCBOR)
  toCompact x = CompactValue <$> to x
  fromCompact (CompactValue x) = from x

instance CC.Crypto crypto => ToCBOR (CompactValue crypto) where
  toCBOR = toCBOR . from

instance CC.Crypto crypto => FromCBOR (CompactValue crypto) where
  fromCBOR = do
    v <- decodeNonNegativeValue
    case to v of
      Nothing ->
        fail
          "impossible failure: decoded nonnegative value that cannot be compacted"
      Just x -> pure x

data CompactValue crypto
  = CompactValueAdaOnly {-# UNPACK #-} !Word64
  | CompactValueMultiAsset
      {-# UNPACK #-} !Word64 -- ada
      {-# UNPACK #-} !Word -- number of ma's
      {-# UNPACK #-} !ShortByteString -- rep
      {-
       The rep consists of five parts
         A) a sequence of Word64s representing quantities
         B) a sequence of Word16s representing policyId indices
         C) Word16s representing asset name indices
         D) a blob of policyIDs
         E) a blob of asset names
       -}
  deriving (Eq, Show, Typeable)

deriving via
  OnlyCheckWhnfNamed "CompactValue" (CompactValue crypto)
  instance
    NoThunks (CompactValue crypto)

from :: forall crypto. (CC.Crypto crypto) => CompactValue crypto -> Value crypto
from (CompactValueAdaOnly c) = Value (fromIntegral c) mempty
from (CompactValueMultiAsset c numAssets rep) =
  valueFromList (fromIntegral c) triples
  where
    n = fromIntegral numAssets
    ba = sbsToByteArray rep
    getTripleForIndex :: Int -> (Word16, Word16, Word64)
    getTripleForIndex i =
      let q = BA.indexByteArray ba i
          pidix = BA.indexByteArray ba (4 * n + i)
          anameix = BA.indexByteArray ba (5 * n + i)
       in (pidix, anameix, q)
    rawTriples :: [(Word16, Word16, Word64)]
    rawTriples = map getTripleForIndex [0 .. (fromIntegral $ numAssets -1)]
    triples :: [(PolicyID crypto, AssetName, Integer)]
    triples = map convertTriple rawTriples
    assetLens =
      let ixs = nub $ map (\(_, x, _) -> x) rawTriples
          ixPairs = zip ixs (drop 1 ixs ++ [fromIntegral $ SBS.length rep])
       in Map.fromList $ (\(a, b) -> (a, fromIntegral $ b - a)) <$> ixPairs
    assetLen :: Word16 -> Int
    assetLen ix = fromJust (Map.lookup ix assetLens)
    convertTriple ::
      (Word16, Word16, Word64) ->
      (PolicyID crypto, AssetName, Integer)
    convertTriple (p, a, i) =
      ( PolicyID $
          ScriptHash $
            Hash.UnsafeHash $
              readShortByteString
                rep
                (fromIntegral p)
                (fromIntegral $ Hash.sizeHash ([] :: [CC.ADDRHASH crypto])),
        AssetName $
          SBS.fromShort $ readShortByteString rep (fromIntegral a) (assetLen a),
        fromIntegral i
      )

to ::
  forall crypto.
  (CC.Crypto crypto) =>
  Value crypto ->
  Maybe (CompactValue crypto)
to v = do
  c <- integerToWord64 ada
  preparedTriples <-
    zip [0 ..]
      . sortBy (comparing (\(_, x, _) -> x))
      <$> traverse prepare triples
  pure $ case triples of
    [] -> CompactValueAdaOnly c
    _ -> CompactValueMultiAsset c (fromIntegral numTriples) $
      runST $ do
        byteArray <- BA.newByteArray repSize
        forM_ preparedTriples $ \(i, (pidoff, anoff, q)) ->
          do
            BA.writeByteArray byteArray i q
            BA.writeByteArray byteArray (4 * numTriples + i) pidoff
            BA.writeByteArray byteArray (5 * numTriples + i) anoff
        forM_ (Map.toList pidOffsetMap) $
          \(pid, offset) ->
            let PolicyID (ScriptHash (Hash.UnsafeHash pidBytes)) = pid
             in BA.copyByteArray
                  byteArray
                  offset
                  (sbsToByteArray pidBytes)
                  0
                  pidSize
        forM_ (Map.toList assetNameOffsetMap) $ \(AssetName anameBS, offset) ->
          let anameBytes = SBS.toShort anameBS
              anameLen = BS.length anameBS
           in BA.copyByteArray
                byteArray
                offset
                (sbsToByteArray anameBytes)
                0
                anameLen
        byteArrayToSbs <$> BA.unsafeFreezeByteArray byteArray
  where
    (ada, triples) = gettriples v
    numTriples = length triples
    initialBlockSize = numTriples * 12

    pidSize = fromIntegral (Hash.sizeHash ([] :: [CC.ADDRHASH crypto]))
    pids = nub $ sort $ (\(pid, _, _) -> pid) <$> triples
    pidOffsetMap =
      let offsets = enumFromThen initialBlockSize (initialBlockSize + pidSize)
       in Map.fromList (zip pids offsets)
    pidOffset pid = fromJust (Map.lookup pid pidOffsetMap)
    pidBlockSize = length pids * pidSize

    assetNames = nub $ sort $ (\(_, an, _) -> an) <$> triples
    assetNameLengths = BS.length . assetName <$> assetNames
    assetNameOffsetMap =
      let offsets = scanl (+) (initialBlockSize + pidBlockSize) assetNameLengths
       in Map.fromList (zip assetNames offsets)
    assetNameOffset aname = fromJust (Map.lookup aname assetNameOffsetMap)
    anameBlockSize = sum assetNameLengths

    repSize = initialBlockSize + pidBlockSize + anameBlockSize

    prepare (pid, aname, q) = do
      q' <- integerToWord64 q
      pure (pidOffset pid, assetNameOffset aname, q')

sbsToByteArray :: ShortByteString -> BA.ByteArray
sbsToByteArray (SBS bah) = BA.ByteArray bah

byteArrayToSbs :: BA.ByteArray -> ShortByteString
byteArrayToSbs (BA.ByteArray bah) = SBS bah

readShortByteString :: ShortByteString -> Int -> Int -> ShortByteString
readShortByteString sbs start len =
  byteArrayToSbs $ BA.cloneByteArray (sbsToByteArray sbs) start len

instance CC.Crypto crypto => Torsor (Value crypto) where
  -- TODO a proper torsor form
  type Delta (Value crypto) = (Value crypto)
  addDelta = (<+>)
  toDelta = id

-- ========================================================================
-- Operations on Values

-- | Extract the set of policies in the Value.
--
--   This function is equivalent to computing the support of the value in the
--   spec.
policies :: Value crypto -> Set (PolicyID crypto)
policies (Value _ m) = Map.keysSet m

lookup :: PolicyID crypto -> AssetName -> Value crypto -> Integer
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
  PolicyID crypto ->
  AssetName ->
  Integer ->
  Value crypto ->
  Value crypto
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
  Map (PolicyID crypto) (Map AssetName Integer) ->
  Map (PolicyID crypto) (Map AssetName Integer)
prune assets =
  Map.filter (not . null) $ Map.filter (/= 0) <$> assets

-- | Rather than using prune to remove 0 assets, when can avoid adding them in the
--   first place by using valueFromList to construct a Value.
valueFromList :: Integer -> [(PolicyID era, AssetName, Integer)] -> Value era
valueFromList ada =
  foldr
    (\(p, n, i) ans -> insert (+) p n i ans)
    (Value ada Map.empty)

-- | Display a Value as a String, one token per line
showValue :: Value crypto -> String
showValue v = show c ++ "\n" ++ unlines (map trans ts)
  where
    (c, ts) = gettriples v
    trans (PolicyID x, hash, cnt) =
      show x
        ++ ",  "
        ++ show hash
        ++ ",  "
        ++ show cnt

gettriples :: Value crypto -> (Integer, [(PolicyID crypto, AssetName, Integer)])
gettriples (Value c m1) = (c, triples)
  where
    triples =
      [ (policyId, aname, amount)
        | (policyId, m2) <- assocs m1,
          (aname, amount) <- assocs m2
      ]
