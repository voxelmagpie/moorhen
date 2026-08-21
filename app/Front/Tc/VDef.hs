-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.VDef where

import Control.Monad (forM, forM_, unless, when)
import Data.HashMap.Strict qualified as HM
import Data.Maybe (catMaybes, isJust, isNothing)
import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.HirFns (addTraitToWhereClauses)
import Front.Tc.Context
import Front.Tc.Error (MonadTcError (throw))
import {-# SOURCE #-} Front.Tc.Expr
import Front.Tc.Generics
import Front.Tc.Names
import Front.Tc.PType
import Front.Tc.State
import {-# SOURCE #-} Front.Tc.Traits
import Front.Tc.Types
import MhPrelude
import Names
import SrcLoc (SrcRange)
import Vars

-- Visits a value definition (function or constant value)
-- This does not include visiting the expression, that is done in typeCheckPackage
visitVDef :: (MonadTc m) => Ctx -> A.VDef -> H.WhereClauses -> m (VFqn, H.VDef)
visitVDef outerCtx astVDef implsWheres = do
  let name = fst astVDef.name
  let fqn =
        VFqn
          (un outerCtx.namespace <> ":" <> (case outerCtx.block of Just (n, _) -> un n <> "."; _ -> "") <> un name)
  (_, thisPkg) <- getThisPkg
  getVDefMaybe thisPkg fqn >>= \case
    Just x ->
      pure (fqn, x)
    _ -> do
      when (isNothing astVDef.typeExpr && isNothing outerCtx.block)
        $ throw astVDef.name "Missing type specifier"

      traitInfoMaybe <- do
        case outerCtx.block of
          Just (blkName, forType) -> do
            BlockCached {traits} <- getBlockDeclMaybe outerCtx.namespace blkName <&> must
            xs <- forM (toList traits) $ \(traitFqn, traitGenArgs) -> do
              trait <- getTrait outerCtx.tcIn traitFqn
              case find ((.vDef.name) >>> fst >>> (== name)) trait.vDefs of
                Just vDef -> pure $ Just (trait, traitGenArgs, vDef)
                Nothing -> pure Nothing
            case catMaybes xs of
              [] -> pure Nothing
              [x] -> pure $ Just (x, forType)
              _ -> throw astVDef.name $ "Multiple traits define the definition '" <> un (fst astVDef.name) <> "'"
          _ -> pure Nothing

      case traitInfoMaybe of
        Nothing -> do
          forM_ astVDef.genParams $ \(_, (n, sr)) ->
            when (HM.member n outerCtx.tNameToGp)
              $ throw sr "Duplicate generic parameter name"

          newGp <- mkGenParams (Fqn $ un fqn) astVDef.genParams

          let gp = outerCtx.genParams <> newGp
          let ctx =
                outerCtx
                  { fqn = Just $ Left fqn,
                    genParams = gp,
                    tNameToGp = HM.union outerCtx.tNameToGp $ HM.fromList $ zip ((snd >>> fst) <$> astVDef.genParams) newGp,
                    thisDefType = Nothing
                  }

          t <- case astVDef.typeExpr of
            Just e -> visitTypeExpr ctx e
            _ -> throw astVDef.name "No trait defines this function, may be missing trait or type"
          wh <- visitWhereClauses ctx astVDef.whereClauses

          let d = H.VDef astVDef.name astVDef.op fqn gp implsWheres wh t
          addVDef fqn d
          pure (fqn, d)
        Just ((trait, concreteTypes, vDef), forType) -> do
          when (isJust astVDef.typeExpr || notNull astVDef.genParams || notNull astVDef.whereClauses)
            $ throw astVDef.name
            $ "Implementations of trait definitions may not specify generic parameters or types\n"
            <> "These are already in the trait definition"

          newGp <- mkGenParams (Fqn $ un fqn) $ vDef.genParams <&> \gp -> (gp.kind, (tFqnToName gp.fqn, gp.sr))

          let selfFqn = case trait.selfType.type' of H.TNamed x _ -> x; _ -> undefined
          let gpMap =
                (selfFqn, forType)
                  : zip (trait.genParams <&> (.fqn)) concreteTypes
                    <> zip (vDef.genParams <&> (.fqn)) (newGp <&> (.type'))
          let sub = substituteGenerics gpMap
          let t = sub vDef.vDef.type'
          let gp = outerCtx.genParams <> newGp

          let wh =
                toList vDef.vDef.whereClauses <&> \(whType, traitRefs) ->
                  let whType' = sub whType
                      traitRefs' = traitRefs <&> second (sub <$>)
                   in (whType', traitRefs')

          unless ((fst <$> astVDef.op) == (fst <$> vDef.vDef.op)) $ case astVDef.op of
            Just (_, sr) -> throw sr "Operator does not match trait definition"
            _ -> throw astVDef.name "Missing operator (TODO: Get this from trait def)"

          let d = H.VDef astVDef.name astVDef.op fqn gp implsWheres (H.WhereClauses wh) t
          addVDef fqn d
          pure (fqn, d)

visitWhereClauses :: (MonadTc m) => Ctx -> [(A.TypeExpr, A.TypeExpr)] -> m H.WhereClauses
visitWhereClauses ctx astWhereClauses = do
  whVar <- newVar (def :: H.WhereClauses)
  forM_ astWhereClauses $ \(typeExpr, traitExpr) -> do
    t' <- visitTypeExpr ctx typeExpr
    (traits, _) <- lookupTrait ctx [] traitExpr
    forM_ traits $ \tr ->
      modVar whVar $ addTraitToWhereClauses t' tr
  getVar whVar

-- Type checks the expression in a value definition
-- Validates that global expressions are valid constant values
visitVDefExpr :: (MonadTc m) => Ctx -> H.Type -> A.Expr -> m ()
visitVDefExpr ctx ex expr@(_, sr) = do
  let fqn = ctx.fqn & must & getLeft & must
  let defType = must ctx.thisDefType
  resetLocalVarUids
  (e', ef) <- visitExpr ctx (typeToPType defType) expr
  unless (null ef) $ throw sr "Global variables may not have effects"
  e'' <- implicitCast ctx e' ex
  nextUid <- getNextLocalVarUid
  addVDefExpr fqn e'' nextUid

-- Looks up a global value definition by name (may be in current file or imported)
lookupGlobalVDef :: (MonadTc m) => Ctx -> VName -> SrcRange -> m (VFqn, H.VDef)
lookupGlobalVDef ctx name sr = do
  lookupVName ctx (name, sr) >>= \case
    NlAstValDef outerCtx astVDef ->
      -- TODO Will need to pass in where clauses once directly accessing impl block vdefs is added
      visitVDef outerCtx astVDef def <&> \(a, b) -> (a, b)
    NlValDef pkgName _ fqn -> do
      pkg <- getDepPkg pkgName
      vDef <- getVDefMaybe pkg fqn <&> must
      pure (fqn, vDef)
