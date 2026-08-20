-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Names where

import Control.Monad (foldM, forM, forM_, unless, when)
import Data.HashMap.Strict qualified as HM
import Data.List (init)
import Data.Maybe (catMaybes, isNothing, mapMaybe)
import Data.Text qualified as T
import Error (ErrorSeverity (SevError, SevWarning))
import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.Tc.Context
import Front.Tc.Error
import Front.Tc.Inputs
import Front.Tc.State
import MhPrelude
import Names
import SrcLoc (SrcRange)
import Vars (MonadVars (getVar, newVar, setVar))

mkVFqn :: Namespace -> VName -> VFqn
mkVFqn (Namespace n) (VName n') = VFqn $ n <> ":" <> n'

mkTFqn :: Namespace -> TName -> TFqn
mkTFqn (Namespace n) (TName n') = TFqn $ n <> ":" <> n'

-- Resolves all imports in the source file with the given namespace and AST
-- Handles both absolute (#package/path) and relative (./path, ../path) imports
-- Validates import paths and checks each name is valid
getImports ::
  (MonadTcImports m) =>
  PkgName ->
  HashMap Namespace A.Ast ->
  Namespace ->
  A.Ast ->
  m ImportsList
getImports thisPkgName allAsts ns ast = do
  -- Extract #package_name and file path within the current package
  let allNsParts = T.split (== '/') (un ns)
  let nsParts = tail allNsParts
  assertM $ notNull nsParts

  xs <- forM ast.imports $ \(A.Import i sr qual names) -> do
    when (isNothing qual && names == NoNames) $ addError SevWarning sr "Import does nothing"
    (importPkg, importNs) <-
      if "#" `T.isPrefixOf` i
        then do
          let pkgName = PkgName $ must $ head $ T.split (== '/') i
          -- Absolute path
          exists <-
            if pkgName == thisPkgName
              then do
                pure $ HM.member (Namespace i) allAsts
              else do
                exists <- depPkgExists pkgName
                unless exists $ throw sr $ "No such package: " <> un pkgName
                pkg <- getDepPkg pkgName
                namespaceExistsInPkg pkg (Namespace i)
          unless exists $ throw sr "Invalid import path"
          pure (pkgName, Namespace i)
        else do
          -- Relative path
          let astImportParts = T.split (== '/') i
          importParts <-
            foldM
              ( \importParts iPart ->
                  if iPart == ".."
                    then do
                      -- Go up a directory by removing the last element in the list
                      when (null importParts) $ throw sr "Import path may not escape the package"
                      pure $ init importParts
                    else
                      pure $ importParts <> [iPart]
              )
              (init nsParts) -- Start by going up to the directory containing the current file
              astImportParts

          let importNs = Namespace $ T.intercalate "/" $ un thisPkgName : importParts
          unless (HM.member importNs allAsts) $ throw sr $ "Invalid relative import path: '" <> un importNs <> "'"
          pure (thisPkgName, importNs)

    let (namesList, nameNotFoundErrType) = case names of
          VisibleNames n -> (n, SevError)
          HiddenNames n -> (n, SevWarning)
          _ -> ([], SevWarning)

    foundList <-
      if importPkg == thisPkgName
        then
          pure
            $ let ast' = must $ HM.lookup importNs allAsts
               in namesList <&> \(n, _) -> case nameToVNameOrTName n of
                    Left n' -> HM.member n' ast'.vDefs
                    Right n' -> HM.member n' ast'.tDefs
        else do
          pkg <- getDepPkg importPkg
          namesFoundInPkg pkg importNs $ fst <$> namesList

    isErr <- newVar False

    forM_ (zip namesList foundList) $ \((n, sr'), f) -> unless f $ do
      when (nameNotFoundErrType == SevError) $ setVar isErr True
      addError nameNotFoundErrType sr' $ "Name not found: " <> un n

    getVar isErr >>= \x -> when x throwTcException

    pure (importPkg, importNs, fst <$> qual, names)

  let defaultImports =
        [(PkgName "#builtins", Namespace "#builtins/", Nothing, AllNames)]

  pure $ filter (\(_, ns', _, _) -> ns /= ns') (defaultImports <> xs)

-- Result of looking up a type name in the current namespace
data TNameLookupResult
  = NlGenericType H.Type -- Generic type parameter
  | NlAstTypeDef Ctx A.TDef -- Type definition in current package
  | NlAstNamespace Namespace A.Ast ImportsList -- Qualified namespace import
  | NlTypeDef PkgName H.TNameExport -- Type or block
  | NlNamespace PkgName Namespace -- Qualified namespace import

-- Looks up a type name in the current context and imports
-- First checks generic parameters, then local definitions, then imports
-- Returns appropriate Nl* result type or throws error if name not found
-- Throws if name lookup is ambiguous
lookupTypeName :: (MonadTc m) => Ctx -> TNameL -> m TNameLookupResult
lookupTypeName ctx (name, sr) = do
  -- Check generic arguments of current definition
  case HM.lookup name ctx.tNameToGp of
    Just gp ->
      pure $ NlGenericType gp.type'
    _ -> do
      -- Search definitions in the current file
      case HM.lookup name ctx.thisAst.tDefs of
        Just tsDef ->
          pure $ NlAstTypeDef (mkFileCtx' ctx) tsDef
        _ -> do
          -- Search imports
          found <- forM ctx.thisAstImports $ \(importPkgName, importNs, qualNameMaybe, names) -> do
            let doCheck = isImported names (forgetNameType name)
            inp <- inputs
            if importPkgName == inp.pkgName
              then do
                let (ast, astImports) = must $ HM.lookup importNs ctx.tcIn.allAsts
                    qualResult = [(importNs, NlAstNamespace importNs ast astImports) | qualNameMaybe == Just name]
                    ctx' = mkFileCtx importNs (ast, astImports) ctx.tcIn
                if not doCheck
                  then
                    -- The name was not in the names list or was in the hidden names list,
                    -- no need to search the AST
                    pure qualResult
                  else case HM.lookup name ast.tDefs of
                    Nothing ->
                      pure qualResult
                    Just tsDef -> do
                      pure $ (importNs, NlAstTypeDef ctx' tsDef) : qualResult
              else do
                let qualResult = [(importNs, NlNamespace importPkgName importNs) | qualNameMaybe == Just name]
                importPkg <- getDepPkg importPkgName
                if not doCheck
                  then
                    pure qualResult
                  else do
                    fqnMaybe <- lookupTNameInPkg importPkg importNs name
                    case fqnMaybe of
                      Nothing -> pure qualResult
                      Just ex -> pure $ (importNs, NlTypeDef importPkgName ex) : qualResult

          case concat found of
            [] -> throw sr $ "Name not found: " <> un name
            ((ns, x) : xs) -> do
              -- The name may have been imported multiple times from the same namespace
              -- This is valid but need to check the name isn't both an imported name and a qualified ('as') name
              let isSame = \case
                    (NlAstTypeDef {}, NlAstTypeDef {}) -> True
                    (NlAstNamespace {}, NlAstNamespace {}) -> True
                    _ -> False
              unless (all (\(ns', y) -> ns == ns' && isSame (x, y)) xs)
                $ throw sr
                $ "Ambiguous name: "
                <> un name
              pure x

-- Result of looking up a value name in the current namespace
data VNameLookupResult
  = NlAstValDef Ctx A.VDef -- Value definition in current package
  | NlValDef PkgName Namespace VFqn -- Imported value definition

-- Looks up a value name in the current context and imports
-- First checks local definitions, then imports
-- Returns appropriate Nl* result type or throws error if name not found
-- Throws if name lookup is ambiguous
lookupVName :: (MonadTc m) => Ctx -> VNameL -> m VNameLookupResult
lookupVName ctx (name, sr) = do
  -- Search definitions in the current file
  case HM.lookup name ctx.thisAst.vDefs of
    Just vDef ->
      pure $ NlAstValDef (mkFileCtx' ctx) vDef
    _ -> do
      -- Search imports
      found <- forM ctx.thisAstImports $ \(importPkgName, importNs, _, names) -> do
        let doCheck = isImported names (forgetNameType name)
        inp <- inputs
        if not doCheck
          then pure Nothing
          else
            if importPkgName == inp.pkgName
              then do
                let (ast, imports) = must $ HM.lookup importNs ctx.tcIn.allAsts
                let defMaybe = HM.lookup name ast.vDefs
                pure $ case defMaybe of
                  Just x ->
                    let d = NlAstValDef (mkFileCtx importNs (ast, imports) ctx.tcIn) x
                     in Just (importNs, d)
                  _ -> Nothing
              else do
                importPkg <- getDepPkg importPkgName
                fqnMaybe <- lookupVNameInPkg importPkg importNs name
                case fqnMaybe of
                  Nothing -> pure Nothing
                  Just fqn -> pure $ Just (importNs, NlValDef importPkgName importNs fqn)

      case catMaybes found of
        [] -> throw sr $ "Name not found: " <> un name
        ((ns, x) : xs) -> do
          unless (all ((== ns) . fst) xs)
            $ throw sr
            $ "Ambiguous name: "
            <> un name
          pure x

isImported :: ImportNames -> Name -> Bool
isImported names name = case names of
  NoNames -> False
  AllNames -> True
  VisibleNames ns -> name `elem` (fst <$> ns)
  HiddenNames ns -> name `notElem` (fst <$> ns)

-- Result of looking up a member value name (in module)
data VNameMemberLookupResult
  = NlMembAstValDef Ctx TName A.TDef A.VDef A.TypeExpr -- Member in current package's module (Ctx is outer ctx, block is not set)
  | NlMembValDef PkgName H.Module VFqn -- Imported member from module in another package

-- Looks up a member value name in all relevant modules
-- Searches both current AST and imported namespaces
-- Returns all matching members from all relevant import blocks
-- Used for resolving method calls on types
lookupMembVName :: (MonadTc m) => Ctx -> (Either VName OpName, SrcRange) -> m [VNameMemberLookupResult]
lookupMembVName ctx (name, _sr) = do
  let thisAstTDefs = snd <$> toList ctx.thisAst.tDefs

  let thisPkgLookup importNames astTDefs newCtx = case name of
        Left n ->
          flip mapMaybe astTDefs $ \tDef -> case tDef.tDef of
            A.Module t d _ _
              | n `elem` HM.keys d.nameMap && isImported importNames (forgetNameType $ fst tDef.name) ->
                  Just $ NlMembAstValDef newCtx (fst tDef.name) tDef (must $ HM.lookup n d.nameMap) t
            _ -> Nothing
        Right op ->
          flip concatMap astTDefs $ \tDef -> case tDef.tDef of
            A.Module t d _ _
              | op `elem` HM.keys d.opMap && isImported importNames (forgetNameType $ fst tDef.name) ->
                  let vDefs = maybe [] toList (HM.lookup op d.opMap)
                   in vDefs <&> \vDef -> NlMembAstValDef newCtx (fst tDef.name) tDef vDef t
            _ -> []

  let thisAstModules = thisPkgLookup AllNames thisAstTDefs (mkFileCtx' ctx)

  otherNsResults <- forM ctx.thisAstImports $ \(importPkgName, importNs, _, names) -> do
    inp <- inputs
    if importPkgName == inp.pkgName
      then do
        let (ast, imports) = must $ HM.lookup importNs ctx.tcIn.allAsts
        let astTDefs = snd <$> toList ast.tDefs
        pure $ thisPkgLookup names astTDefs (mkFileCtx importNs (ast, imports) ctx.tcIn)
      else do
        importPkg <- getDepPkg importPkgName
        modules <- getAllModulesInNs importPkg importNs

        let modules' = concat $ case name of
              Left n ->
                modules <&> \i ->
                  ([(i, n) | isImported names (forgetNameType (i.name :: TName)) && n `elem` i.vDefNames])
              Right op ->
                modules <&> \i ->
                  if isImported names (forgetNameType (i.name :: TName))
                    then let xs = maybe [] toList $ HM.lookup op i.ops in xs <&> (i,)
                    else []

        pure $ modules' <&> \(i, vName) ->
          let vFqn = VFqn $ un i.fqn <> "." <> un vName
           in NlMembValDef importPkgName i vFqn

  pure $ thisAstModules <> concat otherNsResults

-- Result of looking up all modules
data AllModulesResult
  = FoundAstModule Ctx A.TDef
  | FoundModule PkgName H.Module

-- TODO Cache this
findAllModules :: (MonadTc m) => Ctx -> m [AllModulesResult]
findAllModules ctx = do
  let thisAstTDefs = snd <$> toList ctx.thisAst.tDefs

  let thisPkgLookup astTDefs newCtx =
        flip mapMaybe astTDefs
          $ \astTDef -> case astTDef.tDef of A.Module {} -> Just $ FoundAstModule newCtx astTDef; _ -> Nothing

  let thisAstModules = thisPkgLookup thisAstTDefs (mkFileCtx' ctx)

  otherNsResults <- forM ctx.thisAstImports $ \(importPkgName, importNs, _, _) -> do
    inp <- inputs
    if importPkgName == inp.pkgName
      then do
        let (ast, imports) = must $ HM.lookup importNs ctx.tcIn.allAsts
        let astTDefs = snd <$> toList ast.tDefs
        pure $ thisPkgLookup astTDefs (mkFileCtx importNs (ast, imports) ctx.tcIn)
      else do
        importPkg <- getDepPkg importPkgName
        modules <- getAllModulesInNs importPkg importNs
        pure $ modules <&> FoundModule importPkgName

  pure $ thisAstModules <> concat otherNsResults
