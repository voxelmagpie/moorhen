-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Show where

import Data.HashSet qualified as HS
import Data.Text qualified as T
import Front.Tc.PType
import MhPrelude
import Names

pTypeToText :: PType -> Text
pTypeToText = \case
  TUnknown -> "(unknown)"
  TFuncP ps r e ->
    T.concat
      [ if length ps > 1 then "\\ " else "\\",
        T.intercalate ", " $ pTypeToText <$> toList ps,
        " -> ",
        pTypeToText r,
        " ",
        case e of TEffectP {} -> ""; _ -> "@",
        pTypeToText e
      ]
  TTupleP ts -> "(" <> T.intercalate ", " (pTypeToText <$> toList ts) <> ")"
  TNamedP fqn [] -> shortenFqn $ un fqn
  TNamedP fqn args -> shortenFqn (un fqn) <> "[" <> T.intercalate ", " (pTypeToText <$> args) <> "]"
  TEffectP es | HS.size es == 1 -> "@" <> T.concat (pTypeToText <$> toList es)
  TEffectP es -> "@(" <> T.intercalate "," (pTypeToText <$> toList es) <> ")"
  TLifetimeP x -> "'" <> tShow x
