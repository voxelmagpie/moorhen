-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Inputs where

import Front.Ast qualified as A
import MhPrelude
import Names

type ImportsList = [(PkgName, Namespace, Maybe TName, ImportNames)]

data Inputs = Inputs
  { pkgName :: PkgName,
    allAsts :: HashMap Namespace (A.Ast, ImportsList)
  }
