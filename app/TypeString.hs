-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module TypeString where

import MhPrelude

-- E.g. "#pkg/ns:MyType[Int]"
-- This is used for exception handling in the generated JS code
newtype TypeString = TypeString Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)
