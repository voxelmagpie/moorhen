-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.TypeKind where

import MhPrelude

data TypeKind = MonoType | EffectType | AbstractType
  deriving (Show, Generic, Eq, Hashable)
