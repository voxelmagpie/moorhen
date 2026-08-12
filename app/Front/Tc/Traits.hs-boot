-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Traits where

import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.Tc.Context
import Front.Tc.Inputs
import Front.Tc.State
import MhPrelude
import Names
import SrcLoc (SrcRange)

lookupTrait :: (MonadTc m) => Ctx -> [TFqn] -> A.TypeExpr -> m (List1 H.TraitRef, HashSet VName)
getTrait :: (MonadTc m) => Inputs -> TFqn -> m H.Trait
visitBlockDecl :: (MonadTc m) => Ctx -> A.TDef -> m BlockCached
findTraitImpls :: (MonadTc m) => Ctx -> [(TFqn, H.Type)] -> H.WhereClauses -> SrcRange -> m H.WhereClauseTraitsList
findTraitImpls' :: (MonadTc m) => Ctx -> [(H.Type, List1 H.TraitRef)] -> SrcRange -> m H.WhereClauseTraitsList
lookupMembVNameInCtxWhere :: (MonadTc m) => Ctx -> H.Type -> Either VName OpName -> m [(H.WhereTraitLoc, H.Trait, H.TraitVDef)]
visitTrait :: (MonadTc m) => Ctx -> A.TDef -> [A.VDef] -> HashMap OpName (List1 A.VDef) -> m H.Trait
