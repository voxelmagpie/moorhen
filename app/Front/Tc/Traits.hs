-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Traits (lookupTrait, visitBlockDecl, findTraitImpls, findTraitImpls', getTraitMaybe, getTrait, lookupMembVNameInCtxWhere, visitTrait) where

import Control.Monad (forM, forM_, unless, when)
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.List (elemIndex)
import Data.Maybe (isJust, listToMaybe, mapMaybe)
import Data.Text qualified as T
import Front.Ast qualified as A
import Front.Hir (ChosenTrait (FromModule, FromWhereClause))
import Front.Hir qualified as H
import Front.HirFns (getTypeKind, traitRefToText, traitsListFromList, typeToText)
import Front.Tc.Context
import Front.Tc.Error (MonadTcError (throw))
import Front.Tc.Generics
import Front.Tc.Inputs
import Front.Tc.Names
import Front.Tc.PType
import Front.Tc.State
import Front.Tc.Types
import Front.Tc.VDef (visitVDef, visitWhereClauses)
import Front.TypeKind (TypeKind (MonoType))
import MhPrelude
import Names
import SrcLoc (SrcRange)
import Vars (MonadVars (..))

lookupTraits :: (MonadTc m) => Ctx -> [TFqn] -> [A.TypeExpr] -> m ([H.TraitRef], HashMap TName TFqn, HashSet VName)
lookupTraits ctx visited' ts = do
  namesVar <- newVar def
  assocsVar <- newVar def
  traitsVar <- newVar def
  visitedVar <- newVar visited'

  forM_ ts $ \tr -> do
    lookupTrait' ctx visitedVar traitsVar assocsVar namesVar tr

  names' <- getVar namesVar
  assocTypes' <- getVar assocsVar
  traits <- getVar traitsVar
  pure (traits, assocTypes', names')

lookupTrait' :: (MonadTc m) => Ctx -> Var m [TFqn] -> Var m [H.TraitRef] -> Var m (HashMap TName TFqn) -> Var m (HashSet VName) -> A.TypeExpr -> m ()
lookupTrait' ctx visitedVar traitsVar assocsVar namesVar typeExpr = do
  let addToVars depTraits associatedTypesRecursive fqn genArgs' namesRecursive sr = do
        modVar visitedVar $ (fqn :)

        modVar traitsVar (<> depTraits)
        modVar traitsVar ((fqn, genArgs') :)

        assocs <- getVar assocsVar
        forM_ (HM.keys $ HM.intersection associatedTypesRecursive assocs) $ \n' ->
          throw sr $ "Multiple traits define the associated type " <> un n'
        setVar assocsVar (assocs <> associatedTypesRecursive)

        names <- getVar namesVar
        forM_ (HS.intersection namesRecursive names) $ \n' -> throw sr $ "Multiple traits define the name " <> un n'
        setVar namesVar (names <> namesRecursive)

  case typeExpr of
    (A.TNamed qualMaybe name genArgs, sr) -> do
      genArgs' <- forM genArgs $ visitTypeExpr ctx
      lookupTypeName ctx (combineQualMaybeAndTName qualMaybe name) >>= \case
        (NlGenericType _, _) ->
          throw sr "Expected trait, got generic type"
        (_, _ : _) -> throw sr "Expected trait, got data constructor accessor"
        (NlAstTypeDef traitCtx astTDef, []) -> do
          let fqn = TFqn $ un traitCtx.namespace <> ":" <> un (fst name)
          visited <- getVar visitedVar
          unless (fqn `elem` visited) $ do
            unless (length genArgs == length astTDef.genParams) $ throw sr "Wrong number of generic args"
            case astTDef.tDef of
              A.Trait vDefs ts _ thisTraitAssocTypes -> do
                forM_ (toList thisTraitAssocTypes) $ \n'@(n, _) -> do
                  let fqn' = TFqn $ un fqn <> "." <> un n
                  let tDef =
                        H.TDef
                          { name = n',
                            fqn = fqn',
                            genParams = [],
                            selfType = H.TNamed fqn' [],
                            typeKind = MonoType,
                            tDefType = H.IsGenParam
                          }
                  addTDef fqn' tDef
                forM_ ts $ \tr ->
                  lookupTrait' ctx visitedVar traitsVar assocsVar namesVar tr
                addToVars
                  def
                  ((flip HM.mapWithKey thisTraitAssocTypes $ \n _ -> TFqn $ un fqn <> "." <> un n))
                  fqn
                  genArgs'
                  (HM.keysSet vDefs.nameMap)
                  sr
              _ -> throw sr "Expected trait"
        (NlTypeDef _ (H.TNameExport {fqn, typ}), []) -> do
          case typ of
            H.IsTrait (H.Trait {genParams, traits, namesRecursive, associatedTypesRecursive}) -> do
              visited <- getVar visitedVar
              unless (fqn `elem` visited) $ do
                unless (length genArgs == length genParams) $ throw sr "Wrong number of generic args"
                let associatedTypesRecursive' = associatedTypesRecursive <&> \case H.TNamed f _ -> f; _ -> undefined
                addToVars (toList traits) associatedTypesRecursive' fqn genArgs' namesRecursive sr
            _ -> throw sr "Expected trait"
    (_, sr) -> throw sr "Expected trait"

-- TODO Make return type into a record TraitHeader and cache it?
lookupTrait :: (MonadTc m) => Ctx -> A.TypeExpr -> m (List1 H.TraitRef, HashMap TName TFqn, HashSet VName)
lookupTrait ctx typeExpr = do
  traitsVar <- newVar def
  namesVar <- newVar def
  assocsVar <- newVar def
  visitedVar <- newVar def

  lookupTrait' ctx visitedVar traitsVar assocsVar namesVar typeExpr

  traits <- getVar traitsVar
  names <- getVar namesVar
  assocs <- getVar assocsVar

  pure (must $ listToList1 traits, assocs, names)

getTraitMaybe :: (MonadTc m) => Inputs -> TFqn -> m (Maybe H.Trait)
getTraitMaybe tcIn traitFqn = do
  (thisPkgName, thisPkg) <- getThisPkg
  let pkg = tFqnToPkg traitFqn
  if (pkg == thisPkgName)
    then do
      let ns = tFqnToNamespace traitFqn
      let tName = tFqnToName traitFqn
      let ast'@(ast, _) = must $ HM.lookup ns tcIn.allAsts
      let tDefMaybe = HM.lookup tName ast.tDefs -- Could be a generic parameter
      let ctx = mkFileCtx ns ast' tcIn
      case tDefMaybe of
        Just tDef ->
          case tDef.tDef of
            A.Trait x _ _ _ -> Just <$> visitTrait ctx tDef x.vDefsOrdered x.opMap
            _ -> pure Nothing
        _ -> pure Nothing
    else do
      pkg' <- if pkg == thisPkgName then pure thisPkg else getDepPkg pkg
      let traitNs = tFqnToNamespace traitFqn
      let traitName = tFqnToName traitFqn
      exportMaybe <- lookupTNameInPkg pkg' traitNs traitName
      case exportMaybe of
        Just export ->
          case export.typ of
            H.IsTrait x -> pure $ Just x
            _ -> pure Nothing
        _ -> pure Nothing

-- Looks up a trait by its fully qualified name, returning the H.Trait
getTrait :: (MonadTc m) => Inputs -> TFqn -> m H.Trait
getTrait tcIn traitFqn = getTraitMaybe tcIn traitFqn <&> must

-- Visits a module or trait
-- Caches results to avoid reprocessing, resolves generic parameters and 'for'/Self type
visitBlockDecl :: (MonadTc m) => Ctx -> A.TDef -> m BlockCached
visitBlockDecl outerCtx blkTDef = do
  let name = fst blkTDef.name
  cachedMaybe <- getBlockDeclMaybe outerCtx.namespace name
  case cachedMaybe of
    Just x -> pure x
    _ -> do
      let blkFqn = TFqn $ un outerCtx.namespace <> ":" <> un name
      genParams <- mkGenParams (Fqn $ un blkFqn) blkTDef.genParams

      let ctxWithGenParams =
            outerCtx
              { fqn = Just $ Right blkFqn,
                genParams,
                tNameToGp = HM.fromList $ zip ((snd >>> fst) <$> blkTDef.genParams) genParams
              }

      (selfType, traits, wh) <- case blkTDef.tDef of
        A.Module t _ ts astWh _ -> do
          t' <- visitTypeExpr ctxWithGenParams t
          let k = getTypeKind t'
          unless (k == MonoType) $ throw t $ "Type must be a monotype, not " <> T.toLower (tShow k)
          wh <- visitWhereClauses ctxWithGenParams astWh
          pure (t', ts, wh)
        A.Trait _ ts astWh _ -> do
          let fqn = TFqn $ un blkFqn <> "$Self"
          let selfType = H.TNamed fqn []
          let tDef =
                H.TDef
                  { name = (TName "Self", snd blkTDef.name),
                    fqn,
                    genParams = [],
                    selfType,
                    typeKind = MonoType,
                    tDefType = H.IsGenParam
                  }
          addTDef fqn tDef
          wh <- visitWhereClauses ctxWithGenParams astWh
          pure (selfType, ts, wh)
        _ -> error "Not a trait"

      (traits', assocTypesFromTraitDeps, namesFromTraitDeps) <-
        lookupTraits ctxWithGenParams [blkFqn] traits

      let traitMap = HM.fromListWith (<>) $ traits' <&> \(fqn, ts) -> (fqn, [ts])
      forM_ (HM.toList traitMap) $ \(fqn, tss) ->
        case tss of
          [] -> pure ()
          (t0 : ts) ->
            unless (all (== t0) ts)
              $ throw blkTDef.name ("The trait " <> un (tFqnToName fqn) <> " is included multiple times")

      (associatedTypesRecursive, associatedTypes) <- case blkTDef.tDef of
        A.Module _ _ _ _ assocTypes -> do
          forM_ (toList assocTypes) $ \(n, (sr, _)) -> do
            unless (HM.member n assocTypesFromTraitDeps)
              $ throw sr
              $ "Associated type "
              <> un n
              <> " not found in any required trait"

          let blkCtx = ctxWithGenParams {modOrTrait = Nothing, blockWhereClauses = wh}
          associatedTypes' <- forM assocTypes $ \(_, e) -> visitTypeExpr blkCtx e

          withFqn <- flip HM.traverseWithKey associatedTypes' $ \n t -> do
            fqn <- case HM.lookup n assocTypesFromTraitDeps of
              Just fqn -> do
                pure fqn
              _ -> throw blkTDef.name $ "Missing associated type: " <> un n
            pure (fqn, t)

          pure (associatedTypes', withFqn)
        A.Trait _ _ _ assocTypes -> do
          forM_ (HM.keys assocTypes) $ \n ->
            when (HM.member n assocTypesFromTraitDeps) $ throw blkTDef.name $ "Duplicate associated type " <> un n
          let assocTypesFromTraitDeps' = assocTypesFromTraitDeps <&> \f -> (f, H.TNamed f [])
          -- TDefs created in lookupTrait
          let assocTypesFromThisTrait = flip HM.mapWithKey assocTypes $ \n _ ->
                let f = TFqn $ un blkFqn <> "." <> un n
                 in (f, H.TNamed f [])
          let assocTypesAll = assocTypesFromTraitDeps' <> assocTypesFromThisTrait
          let withoutFqn = assocTypesAll <&> snd
          pure (withoutFqn, assocTypesAll)
        _ -> undefined

      namesRecursive <- case blkTDef.tDef of
        A.Module {} -> pure namesFromTraitDeps -- Names could be new or implementation of a trait def
        A.Trait (A.BlockInner {nameMap}) _ _ _ -> do
          forM_ (HM.keys nameMap) $ \n ->
            when (HS.member n namesFromTraitDeps) $ throw blkTDef.name $ "Duplicate name " <> un n
          pure $ namesFromTraitDeps <> HM.keysSet nameMap
        _ -> undefined

      let ctxModTrait = CtxModOrTrait {name, selfType, associatedTypes}
      let blkCtx = ctxWithGenParams {modOrTrait = Just ctxModTrait, blockWhereClauses = wh}

      let x =
            BlockCached
              { genParams,
                selfType,
                blkFqn,
                blkCtx,
                traits = traitsListFromList traits',
                namesRecursive,
                wh,
                associatedTypesRecursive
              }
      addBlockDeclCache outerCtx.namespace name x

      -- When a generic trait is initialised in a trait/module trait dep list, the dep trait/mod's own
      -- where clauses must be satisfiable with the provided generic args
      -- I.e. mod SomeModule [A] : SomeTrait[A] -- A might not support Eq!!
      -- trait SomeTrait [A] where A : Eq
      forM_ (HS.toList $ HS.fromList traits') $ \(traitFqn, genArgs) -> do
        trait <- getTrait blkCtx.tcIn traitFqn
        let gpMap = zip (trait.genParams <&> (.fqn)) genArgs
        findTraitImpls blkCtx gpMap trait.whereClauses (snd blkTDef.name)

      pure x

-- !! The where clause types are from the caller's perspective, i.e. generic args are substituted
-- There may be duplicates if 2 generic args map to the same type. That is fine.
findTraitImpls' :: forall m. (MonadTc m) => Ctx -> [(H.Type, List1 H.TraitRef)] -> SrcRange -> m H.WhereClauseTraitsList
findTraitImpls' ctx whs sr = do
  -- TODO Cache this
  allMods <- findAllModules ctx
  allMods' <- forM allMods $ \case
    FoundAstModule outerCtx blkTDef -> do
      BlockCached {genParams, selfType, blkFqn, traits, wh} <- visitBlockDecl outerCtx blkTDef
      pure (blkFqn, genParams, selfType, traits, wh)
    FoundModule _pkgName blk -> do
      pure (blk.fqn, blk.genParams, blk.forType, blk.traits, blk.whereClauses)

  forM whs $ \(t, requiredTraits) -> do
    allMods'' <- flip mapMaybeM allMods' $ \(fqn, gps, forType, ts, wh) -> do
      genArgsMaybe <- tryInferGenericArgs [] gps (typeToPType t) forType def
      case genArgsMaybe of
        Left _ -> pure Nothing
        Right xs -> pure $ Just (fqn, xs, ts, gps, wh)
    forM requiredTraits $ \tr@(traitFqn, _) -> do
      trait <- getTrait ctx.tcIn traitFqn
      let fromImpls = flip filter allMods'' $ \(_, _, ts, _, _) -> tr `elem` toList ts

      let fromWheres' :: H.FromWhereClauseSource -> Maybe H.WhereTraitLoc
          fromWheres' src =
            let ws = toList $ case src of
                  H.FromBlockWheres -> ctx.blockWhereClauses
                  H.FromVDefWheres -> ctx.vDefWhereClauses
                whereClausesTotal = length ws
             in listToMaybe $ flip mapMaybe (zip [0 :: Int ..] ws) $ \(i, (wt, traits')) ->
                  let whereClauseTraitsTotal = length traits'
                   in case elemIndex tr $ toList traits' of
                        Just j
                          | wt == t ->
                              Just
                                $ H.WhereTraitLoc
                                  { src,
                                    whereClauseIdx = i,
                                    whereClausesTotal,
                                    whereClauseTraitIdx = j,
                                    whereClauseTraitsTotal,
                                    traitDefsTotal = length trait.vDefs
                                  }
                        _ -> Nothing

      let fromWheres = case (fromWheres' H.FromBlockWheres, fromWheres' H.FromVDefWheres) of
            (Nothing, Nothing) -> Nothing
            (Just x, Nothing) -> Just x
            (Nothing, Just x) -> Just x
            (Just _, Just _) -> undefined -- TODO Check for ambiguity when processing module vdefs
      let typeTraitStr = typeToText t <> " : " <> traitRefToText tr
      case (fromImpls, fromWheres) of
        ([], Nothing) -> throw sr $ "No implementation found for " <> typeTraitStr
        ([], Just loc) -> pure (tr, FromWhereClause loc)
        ([(fqn, xs, _, gps, modWh)], Nothing) -> do
          let gpMap = zip (gps <&> (.fqn)) xs
          wh <- findTraitImpls ctx gpMap modWh sr
          pure (tr, FromModule fqn xs wh)
        _ -> throw sr $ "Ambiguous implementations of " <> typeTraitStr

-- -- Where clauses unmodified
findTraitImpls ::
  (MonadTc m) => Ctx -> [(TFqn, H.Type)] -> H.WhereClauses -> SrcRange -> m H.WhereClauseTraitsList
findTraitImpls ctx gpMap whs = findTraitImpls' ctx (toList whs <&> first (substituteGenerics gpMap))

lookupMembVNameInCtxWhere ::
  (MonadTc m) => Ctx -> H.Type -> Either VName OpName -> m [(H.WhereTraitLoc, H.Trait, H.TraitVDef)]
lookupMembVNameInCtxWhere ctx t name = do
  let ss = [(H.FromBlockWheres, ctx.blockWhereClauses), (H.FromVDefWheres, ctx.vDefWhereClauses)]
  xs <- forM ss $ \(src, whs) -> forM (zip [0 :: Int ..] $ toList whs) $ \(i, (t', traits)) -> do
    if t == t'
      then do
        traitIdx <- forM (zip [0 :: Int ..] $ toList traits) $ \(idx, (tr, _)) -> do
          trait <- getTrait ctx.tcIn tr
          let lookupName n = case HM.lookup n trait.names of
                Just vDef ->
                  [ ( H.WhereTraitLoc
                        { src,
                          whereClauseIdx = i,
                          whereClausesTotal = length $ un whs,
                          whereClauseTraitIdx = idx,
                          whereClauseTraitsTotal = length traits,
                          traitDefsTotal = length trait.vDefs
                        },
                      trait,
                      vDef
                    )
                  ]
                _ -> []
          pure $ case name of
            Left n -> lookupName n
            Right o -> case HM.lookup o trait.ops of
              Just names -> concat $ toList $ names <&> lookupName
              _ -> []
        pure $ concat traitIdx
      else
        pure []
  pure $ concat $ concat xs

visitTrait :: (MonadTc m) => Ctx -> A.TDef -> [A.VDef] -> HashMap OpName (List1 A.VDef) -> m H.Trait
visitTrait outerCtx tDef vDefs opMap = do
  assertM $ case tDef.tDef of A.Trait {} -> True; _ -> False

  BlockCached {genParams, selfType, blkFqn, blkCtx, traits, namesRecursive, wh, associatedTypesRecursive} <-
    visitBlockDecl outerCtx tDef

  vDefs' <- forM vDefs $ \astVDef -> do
    (_, vDef) <- visitVDef blkCtx astVDef wh
    when (isJust astVDef.expr) $ error "TODO: Default functions?"
    case vDef.type' of
      H.TFunc ps _ _ -> case ps of
        p : _ | p == selfType -> pure ()
        _ -> throw vDef.name "Trait functions must take a self parameter"
      _ -> throw vDef.name "Trait members must be functions"
    pure
      $ H.TraitVDef
        { genParams = drop (length genParams) vDef.genParams,
          idx = astVDef.idx,
          vDef
        }

  -- Fqn of the implicit Self type which is present for all traits
  let selfFqn = case selfType of H.TNamed f _ -> f; _ -> undefined

  let selfTypeGp =
        H.GenParam
          { fqn = selfFqn,
            sr = snd tDef.name,
            type' = selfType,
            kind = getTypeKind selfType
          }

  let blk =
        H.Trait
          { genParams,
            name = fst tDef.name,
            fqn = blkFqn,
            selfType = selfTypeGp,
            vDefs = vDefs',
            names = HM.fromList $ vDefs' <&> \v -> (fst v.vDef.name, v),
            ops = opMap <&> (<&> ((.name) >>> fst)),
            traits,
            whereClauses = wh,
            namesRecursive,
            associatedTypesRecursive
          }
  -- TODO Cache
  pure blk
