{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Cardano.Ledger.ShelleyMA.TxBody
  ( TxBody (TxBody, TxBodyConstr),
    TxBodyRaw (..),
    FamsFrom,
    FamsTo,
    txSparse,
    bodyFields,
    StrictMaybe (..),
    isSNothing,
    fromSJust,
    ValidityInterval (..),
    initial,
  )
where

import Cardano.Binary (Annotator, FromCBOR (..), ToCBOR (..))
import Cardano.Ledger.Compactible (CompactForm (..), Compactible (..))
import Cardano.Ledger.Core (Script, Value)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import Cardano.Ledger.Val
  ( DecodeMint (..),
    DecodeNonNegative,
    EncodeMint (..),
    Val (..),
  )
import Control.DeepSeq (NFData (..))
import Data.Coders
  ( Decode (..),
    Density (..),
    Encode (..),
    Field,
    Wrapped (..),
    decode,
    decodeSet,
    decodeStrictSeq,
    field,
    (!>),
  )
import qualified Data.Map as Map
import Data.MemoBytes (Mem, MemoBytes (..), memoBytes)
import Data.Sequence.Strict (StrictSeq, fromList)
import Data.Set (Set, empty)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.BaseTypes (StrictMaybe (SJust, SNothing))
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Hashing (EraIndependentTxBody, HashAnnotated (..))
import Shelley.Spec.Ledger.MetaData (MetaDataHash)
import Shelley.Spec.Ledger.PParams (Update)
import Shelley.Spec.Ledger.Serialization (encodeFoldable)
import Shelley.Spec.Ledger.TxBody
  ( DCert (..),
    TxIn (..),
    TxOut (..),
    Wdrl (..),
  )

-- =====================================================
-- TxBody has two Era dependent type families
-- (Value era) and (Script era) (hidden in DCert) in
-- order to make CBOR instances of things we are going to
-- have to assume some properties about these.

type FamsFrom era =
  ( Era era,
    Typeable era,
    Typeable (Script era),
    Typeable (Core.Metadata era),
    Show (Value era),
    Compactible (Value era),
    DecodeNonNegative (Value era),
    DecodeMint (Value era),
    FromCBOR (CompactForm (Value era)), -- Arises because TxOut uses Compact form
    FromCBOR (Value era),
    FromCBOR (Annotator (Script era)) -- Arises becaause DCert memoizes its bytes
  )

type FamsTo era =
  ( Era era,
    ToCBOR (Value era),
    Compactible (Value era),
    EncodeMint (Value era),
    ToCBOR (CompactForm (Value era)), -- Arises because TxOut uses Compact form
    ToCBOR (Script era),
    Typeable (Core.Metadata era)
  )

-- =======================================================

data TxBodyRaw era = TxBodyRaw
  { inputs :: !(Set (TxIn era)),
    outputs :: !(StrictSeq (TxOut era)),
    certs :: !(StrictSeq (DCert era)),
    wdrls :: !(Wdrl era),
    txfee :: !Coin,
    vldt :: !ValidityInterval, -- imported from Timelocks
    update :: !(StrictMaybe (Update era)),
    mdHash :: !(StrictMaybe (MetaDataHash era)),
    mint :: !(Value era)
  }
  deriving (Typeable)

-- For each instance we try and use the weakest constraint possible
-- The surprising (Compactible (Value era))) constraint comes from the fact that TxOut
-- stores a (Value era) in a compactible form.

deriving instance (NFData (Value era), Era era) => NFData (TxBodyRaw era)

deriving instance
  ( Compactible (Value era),
    Eq (Value era),
    Eq (CompactForm (Value era))
  ) =>
  Eq (TxBodyRaw era)

deriving instance
  (Era era, Compactible (Value era), Show (Value era)) =>
  Show (TxBodyRaw era)

deriving instance Generic (TxBodyRaw era)

deriving instance NoThunks (Value era) => NoThunks (TxBodyRaw era)

instance (Val (Value era), FamsFrom era) => FromCBOR (TxBodyRaw era) where
  fromCBOR =
    decode
      ( SparseKeyed
          "TxBodyRaw"
          initial
          bodyFields
          [(0, "inputs"), (1, "outputs"), (2, "txfee")]
      )

instance
  (Val (Value era), FamsFrom era) =>
  FromCBOR (Annotator (TxBodyRaw era))
  where
  fromCBOR = pure <$> fromCBOR

isSNothing :: StrictMaybe a -> Bool
isSNothing SNothing = True
isSNothing _ = False

fromSJust :: StrictMaybe a -> a
fromSJust (SJust x) = x
fromSJust SNothing = error "SNothing in fromSJust"

encodeKeyedStrictMaybe ::
  ToCBOR a =>
  Word ->
  StrictMaybe a ->
  Encode ( 'Closed 'Sparse) (StrictMaybe a)
encodeKeyedStrictMaybe key x = Omit isSNothing (Key key (E (toCBOR . fromSJust) x))

-- Sparse encodings of TxBodyRaw, the key values are fixed by backwarad compatibility
-- concerns as we want the Shelley era TxBody to deserialise as a Shelley-ma TxBody.
-- txXparse and bodyFields should be Duals, visual inspection helps ensure this.

txSparse ::
  (Val (Value era), FamsTo era) =>
  TxBodyRaw era ->
  Encode ( 'Closed 'Sparse) (TxBodyRaw era)
txSparse (TxBodyRaw inp out cert wdrl fee (ValidityInterval bot top) up hash frge) =
  Keyed (\i o f topx c w u h botx forg -> TxBodyRaw i o c w f (ValidityInterval botx topx) u h forg)
    !> Key 0 (E encodeFoldable inp) -- We don't have to send these in TxBodyX order
    !> Key 1 (E encodeFoldable out) -- Just hack up a fake constructor with the lambda.
    !> Key 2 (To fee)
    !> encodeKeyedStrictMaybe 3 top
    !> Omit null (Key 4 (E encodeFoldable cert))
    !> Omit (null . unWdrl) (Key 5 (To wdrl))
    !> encodeKeyedStrictMaybe 6 up
    !> encodeKeyedStrictMaybe 7 hash
    !> encodeKeyedStrictMaybe 8 bot
    !> Omit isZero (Key 9 (E encodeMint frge))

bodyFields :: FamsFrom era => Word -> Field (TxBodyRaw era)
bodyFields 0 = field (\x tx -> tx {inputs = x}) (D (decodeSet fromCBOR))
bodyFields 1 = field (\x tx -> tx {outputs = x}) (D (decodeStrictSeq fromCBOR))
bodyFields 2 = field (\x tx -> tx {txfee = x}) From
bodyFields 3 = field (\x tx -> tx {vldt = (vldt tx) {validTo = x}}) (D (SJust <$> fromCBOR))
bodyFields 4 = field (\x tx -> tx {certs = x}) (D (decodeStrictSeq fromCBOR))
bodyFields 5 = field (\x tx -> tx {wdrls = x}) From
bodyFields 6 = field (\x tx -> tx {update = x}) (D (SJust <$> fromCBOR))
bodyFields 7 = field (\x tx -> tx {mdHash = x}) (D (SJust <$> fromCBOR))
bodyFields 8 = field (\x tx -> tx {vldt = (vldt tx) {validFrom = x}}) (D (SJust <$> fromCBOR))
bodyFields 9 = field (\x tx -> tx {mint = x}) (D decodeMint)
bodyFields n = field (\_ t -> t) (Invalid n)

initial :: (Val (Value era)) => TxBodyRaw era
initial =
  TxBodyRaw
    empty
    (fromList [])
    (fromList [])
    (Wdrl Map.empty)
    (Coin 0)
    (ValidityInterval SNothing SNothing)
    SNothing
    SNothing
    zero

-- ===========================================================================
-- Wrap it all up in a newtype, hiding the insides with a pattern construtor.

newtype TxBody e = TxBodyConstr (MemoBytes (TxBodyRaw e))
  deriving (Typeable)

deriving instance
  (Compactible (Value era), Eq (Value era), Eq (CompactForm (Value era))) =>
  Eq (TxBody era)

deriving instance
  (Era era, Compactible (Value era), Show (Value era)) =>
  Show (TxBody era)

deriving instance Generic (TxBody era)

deriving newtype instance (Typeable era, NoThunks (Value era)) => NoThunks (TxBody era)

deriving newtype instance (NFData (Value era), Era era) => NFData (TxBody era)

deriving newtype instance (Typeable era) => ToCBOR (TxBody era)

deriving via
  (Mem (TxBodyRaw era))
  instance
    (Val (Value era), FamsFrom era) =>
    FromCBOR (Annotator (TxBody era))

instance Era era => HashAnnotated (TxBody era) era where
  type HashIndex (TxBody era) = EraIndependentTxBody

-- Make a Pattern so the newtype and the MemoBytes are hidden

pattern TxBody ::
  (Val (Value era), FamsTo era) =>
  (Set (TxIn era)) ->
  (StrictSeq (TxOut era)) ->
  (StrictSeq (DCert era)) ->
  (Wdrl era) ->
  Coin ->
  ValidityInterval ->
  (StrictMaybe (Update era)) ->
  (StrictMaybe (MetaDataHash era)) ->
  (Value era) ->
  TxBody era
pattern TxBody i o d w fee vi u m mint <-
  TxBodyConstr (Memo (TxBodyRaw i o d w fee vi u m mint) _)
  where
    TxBody i o d w fee vi u m mint =
      TxBodyConstr $
        memoBytes $ txSparse (TxBodyRaw i o d w fee vi u m mint)

{-# COMPLETE TxBody #-}

-- ==================================================================
-- Promote the fields of TxBodyRaw to be fields of TxBody. Either
-- automatically or by hand. Both methods have drawbacks.

{-
instance HasField tag (TxBodyRaw e) c => HasField (tag::Symbol) (TxBody e) c where
   getField (TxBodyConstr (Memo x _)) = getField @tag x

-- The method above autmatically lifts the Hasfield instances from TxBodyRaw to TxBody
-- the problem is, if some other file imports this file, it needs to import both
-- the hidden type TxBodyRaw and its constructors like this
-- import Cardano.Ledger.ShelleyMA.TxBody(TxBodyRaw(..))     OR
-- import qualified Cardano.Ledger.ShelleyMA.TxBody as XXX
-- Both are very ugly, but at least in the second way, one doesn't need to know the name of TxBodyRaw
-- So instead we tediously write by hand explicit HasField instances for TxBody
-}

instance HasField "inputs" (TxBody e) (Set (TxIn e)) where
  getField (TxBodyConstr (Memo m _)) = getField @"inputs" m

instance HasField "outputs" (TxBody e) (StrictSeq (TxOut e)) where
  getField (TxBodyConstr (Memo m _)) = getField @"outputs" m

instance HasField "certs" (TxBody e) (StrictSeq (DCert e)) where
  getField (TxBodyConstr (Memo m _)) = getField @"certs" m

instance HasField "wdrls" (TxBody e) (Wdrl e) where
  getField (TxBodyConstr (Memo m _)) = getField @"wdrls" m

instance HasField "txfee" (TxBody e) Coin where
  getField (TxBodyConstr (Memo m _)) = getField @"txfee" m

instance HasField "vldt" (TxBody e) ValidityInterval where
  getField (TxBodyConstr (Memo m _)) = getField @"vldt" m

instance HasField "update" (TxBody e) (StrictMaybe (Update e)) where
  getField (TxBodyConstr (Memo m _)) = getField @"update" m

instance HasField "mdHash" (TxBody e) (StrictMaybe (MetaDataHash e)) where
  getField (TxBodyConstr (Memo m _)) = getField @"mdHash" m

instance (Value e ~ vv) => HasField "mint" (TxBody e) vv where
  getField (TxBodyConstr (Memo m _)) = getField @"mint" m
