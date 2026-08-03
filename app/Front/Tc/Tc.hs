-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Tc (typeCheckPackage) where

import Control.Exception (try)
import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Reader (ReaderT (runReaderT))
import Data.Either (isLeft)
import Data.HashMap.Strict qualified as HM
import Data.HashTable.IO qualified as HT
import Data.IORef (newIORef, readIORef)
import Data.Maybe (isNothing)
import Error (Error (Error), ErrorSeverity (SevError))
import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.Tc.Context
import Front.Tc.Error (MonadTcError (throw, throwTcException, tryTcKeepErrors), TcException)
import Front.Tc.Inputs
import Front.Tc.Names
import Front.Tc.State
import Front.Tc.StateImpl qualified as TcSt
import Front.Tc.Traits
import Front.Tc.Types
import Front.Tc.VDef
import MhPrelude
import Names
import Vars

-- Main entry point for type checking a package
-- Processes all ASTs in the package, checks types, builds export lists
typeCheckPackage :: PkgName -> HashTable PkgName H.Hir -> HashMap Namespace A.Ast -> IO ([Error], Maybe H.Hir)
typeCheckPackage pkgName depPkgs allAsts = do
  errs <- newIORef []
  allAstsOrErr <-
    try @TcException
      $ flip runReaderT (TcSt.ImportsPpState depPkgs errs)
      $ gatherImports pkgName allAsts

  let checkIfHasErrs = do
        allErrsAndWarnings <- readIORef errs <&> reverse
        pure (allErrsAndWarnings, notNull $ filter (\(Error _ sev _ _) -> sev == SevError) allErrsAndWarnings)
  (allErrsAndWarnings', hasErrs') <- checkIfHasErrs

  case allAstsOrErr of
    Left _ -> do
      pure (allErrsAndWarnings', Nothing)
    Right _ | hasErrs' -> do
      pure (allErrsAndWarnings', Nothing)
    Right allAsts''' -> do
      let allAsts' = HM.fromList allAsts'''
      ir <- H.Hir pkgName <$> HT.new <*> HT.new <*> HT.new <*> HT.new <*> HT.new
      let inp = Inputs pkgName allAsts'
      s <- TcSt.State ir inp depPkgs <$> newIORef 0 <*> HT.new <*> pure errs
      res <- try @TcException $ runReaderT (typeCheckPackage' :: TcSt.Tc ()) s
      (allErrsAndWarnings, hasErrs) <- checkIfHasErrs
      pure (allErrsAndWarnings, if isLeft res || hasErrs then Nothing else Just s.ir)

gatherImports ::
  (MonadTcError m, MonadTcImports m, MonadVars m) =>
  PkgName ->
  HashMap Namespace A.Ast ->
  m [(Namespace, (A.Ast, ImportsList))]
gatherImports thisPkg allAsts =
  forM (toList allAsts)
    $ \(ns, ast) -> getImports thisPkg allAsts ns ast <&> \i -> (ns, (ast, i))

typeCheckPackage' :: (MonadTc m) => m ()
typeCheckPackage' = do
  i <- inputs
  forM_ (toList i.allAsts) $ \(ns, astAndImports@(ast, _)) -> do
    let outerCtx = mkFileCtx ns astAndImports i
    vExports <- newVar []
    tExports <- newVar []
    allModules <- newVar []
    forM_ (toList ast.tDefs) $ \(_, tDef) -> do
      case tDef.tDef of
        A.TypeDecl _ _ -> do
          (fqn, _) <- visitTDef2 outerCtx tDef
          modVar tExports ((fst tDef.name, H.TNameExport fqn H.IsTypeDef) :)
        A.TypeAliasDecl _ -> do
          (fqn, _) <- visitTDef1 outerCtx tDef
          modVar tExports ((fst tDef.name, H.TNameExport fqn H.IsTypeDef) :)
        A.BuiltinTypeDecl -> do
          (fqn, _) <- visitTDef1 outerCtx tDef
          modVar tExports ((fst tDef.name, H.TNameExport fqn H.IsTypeDef) :)
        A.Module _ vDefs _ _ -> do
          (gp, forType, blkFqn, _, traits, allTraitNames, wh) <- visitBlockDecl outerCtx tDef

          forM_ allTraitNames $ \n ->
            unless (n `elem` (vDefs.nameMap <&> fst . (.name)))
              $ throw tDef.name
              $ "Missing implementation for trait definition '"
              <> un n
              <> "'"

          let mod =
                H.Module
                  gp
                  (fst tDef.name)
                  blkFqn
                  forType
                  (HM.keys vDefs.nameMap)
                  (vDefs.opMap <&> (<&> ((.name) >>> fst)))
                  traits
                  wh
          modVar tExports ((fst tDef.name, H.TNameExport blkFqn $ H.IsModule mod) :)
          modVar allModules (mod :)
        A.Trait d _ _ -> do
          trait <- visitTrait outerCtx tDef d.vDefsOrdered d.opMap
          modVar tExports ((fst tDef.name, H.TNameExport trait.fqn $ H.IsTrait trait) :)
    forM_ (toList ast.vDefs) $ \(_, astVDef) -> do
      (fqn, vDef) <- visitVDef outerCtx astVDef def
      modVar vExports ((fst vDef.name, fqn) :)

    vExports' <- getVar vExports
    tExports' <- getVar tExports
    allModules' <- getVar allModules
    addExportedDefs ns vExports' tExports' allModules'

  wasErr <- newVar False
  forM_ (toList i.allAsts) $ \(ns, astAndImports@(ast, _)) -> do
    let outerCtx = mkFileCtx ns astAndImports i
    forM_ (toList ast.vDefs) $ \(_, astVDef) -> do
      (fqn, vDef) <- visitVDef outerCtx astVDef def
      let tNameToGp = HM.fromList $ zip ((snd >>> fst) <$> astVDef.genParams) vDef.genParams
      let ctx =
            outerCtx
              { fqn = Just $ Left fqn,
                genParams = vDef.genParams,
                blockWhereClauses = def,
                vDefWhereClauses = vDef.whereClauses,
                tNameToGp,
                thisDefType = Just vDef.type'
              }
      successMaybe <- tryTcKeepErrors $ forM_ astVDef.expr $ visitVDefExpr ctx vDef.type'
      when (isNothing successMaybe) $ setVar wasErr True

    forM_ (toList ast.tDefs) $ \(_, tDef) -> do
      case tDef.tDef of
        A.TypeDecl _ _ -> pure ()
        A.TypeAliasDecl _ -> pure ()
        A.BuiltinTypeDecl -> pure ()
        A.Trait {} -> pure ()
        A.Module _ vDefs _ _ -> do
          (_, forType, _, ctxWithGenParams, _, _, wh) <- visitBlockDecl outerCtx tDef

          let modCtx = ctxWithGenParams {block = Just (fst tDef.name, forType)}
          forM_ (toList vDefs.nameMap) $ \(_, astVDef) -> do
            (vFqn, vDef) <- visitVDef modCtx astVDef wh

            let tNameToGp = HM.fromList $ zip ((snd >>> fst) <$> (tDef.genParams <> astVDef.genParams)) vDef.genParams
            let ctx =
                  modCtx
                    { fqn = Just $ Left vFqn,
                      genParams = vDef.genParams, -- Already includes module generic parameters
                      blockWhereClauses = wh,
                      vDefWhereClauses = vDef.whereClauses,
                      tNameToGp,
                      thisDefType = Just vDef.type'
                    }
            successMaybe <- tryTcKeepErrors $ forM_ astVDef.expr $ visitVDefExpr ctx vDef.type'
            when (isNothing successMaybe) $ setVar wasErr True
  wasErr' <- getVar wasErr
  when wasErr' throwTcException
