-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Expr where

import Data.HashSet (HashSet)
import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.Tc.Context
import Front.Tc.PType
import Front.Tc.State

visitExpr :: (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
