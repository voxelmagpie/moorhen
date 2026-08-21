-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.State where

import Data.Kind qualified as K
import Front.Hir qualified as H
import Front.Tc.Context (Ctx)
import Front.Tc.Error (MonadTcError (..))
import Front.Tc.Inputs
import MhPrelude
import Names
import Vars

-- For traits the type is Self
-- This holds all the type information for a module or trait
data BlockCached = BlockCached
  { genParams :: [H.GenParam],
    selfType :: H.Type,
    blkFqn :: TFqn,
    blkCtx :: Ctx,
    traits :: H.TraitsList,
    recursiveNames :: HashSet VName, -- All names from all trait deps
    wh :: H.WhereClauses
  }

-- Subset of state-manipulating functions available during import preprocessing
class (MonadVars m, MonadTcError m) => MonadTcImports m where
  type Pkg m :: K.Type
  depPkgExists :: PkgName -> m Bool
  getDepPkg :: PkgName -> m (Pkg m)
  namespaceExistsInPkg :: Pkg m -> Namespace -> m Bool
  namesFoundInPkg :: Pkg m -> Namespace -> [Name] -> m [Bool]
  lookupTNameInPkg :: Pkg m -> Namespace -> TName -> m (Maybe H.TNameExport)
  lookupVNameInPkg :: Pkg m -> Namespace -> VName -> m (Maybe VFqn)
  getAllModulesInNs :: Pkg m -> Namespace -> m [H.Module]

class (MonadTcImports m) => MonadTc m where
  getThisPkg :: m (PkgName, Pkg m)
  getDepOrThisPkg :: PkgName -> m (Pkg m)
  getTDefMaybe :: Pkg m -> TFqn -> m (Maybe H.TDef)
  getDataTypeDefMaybe :: Pkg m -> TFqn -> m (Maybe H.DataTypeDef)
  getVDefMaybe :: Pkg m -> VFqn -> m (Maybe H.VDef)
  inputs :: m Inputs
  addTDef :: TFqn -> H.TDef -> m ()
  addDataTypeDef :: TFqn -> H.DataTypeDef -> m ()
  addVDef :: VFqn -> H.VDef -> m ()
  addVDefExpr :: VFqn -> H.Expr -> Int -> m ()
  addExportedDefs :: Namespace -> [(VName, VFqn)] -> [(TName, H.TNameExport)] -> [H.Module] -> m ()
  mkLocalVarUid :: m H.LocalVarUid
  getNextLocalVarUid :: m Int
  resetLocalVarUids :: m ()
  getBlockDeclMaybe :: Namespace -> TName -> m (Maybe BlockCached)
  addBlockDeclCache :: Namespace -> TName -> BlockCached -> m ()
