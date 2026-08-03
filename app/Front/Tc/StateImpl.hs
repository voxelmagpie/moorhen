-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.StateImpl where

import Control.Exception (throwIO, try)
import Control.Monad (forM, when)
import Control.Monad.Reader (MonadIO (liftIO), MonadReader (ask), ReaderT (runReaderT), asks)
import Data.HashTable.IO qualified as HT
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Maybe (isJust, mapMaybe)
import Error (Error)
import Front.Ast qualified as A
import Front.Hir
import Front.Hir qualified as H
import Front.Tc.Context (Ctx)
import Front.Tc.Error (MonadTcError (..), TcException (TcException))
import Front.Tc.Inputs
import Front.Tc.PType (PType)
import Front.Tc.State
import MhPrelude
import Names
import Vars

type VisitExprFnTc = Ctx -> PType -> A.Expr -> Tc (H.Expr, [H.Type])

data State = State
  { -- State
    ir :: Hir,
    inputs :: Inputs,
    depPkgs :: HashTable PkgName Hir,
    nextLocalVarUid :: IORef Int,
    blockDeclCache :: HashTable (Namespace, TName) BlockCached,
    -- Errors
    errorsRev :: IORef [Error]
  }

type Tc = ReaderT State IO

-- TcPre monad is used for preprocessing import lists before the main type checking pass

data ImportsPpState = ImportsPpState
  { depPkgs :: HashTable PkgName Hir,
    errorsRev :: IORef [Error]
  }

type TcImpPre = ReaderT ImportsPpState IO

-- -- --

instance MonadVars Tc where
  type Var Tc = IORef
  newVar = liftIO . newIORef
  setVar v x = liftIO $ writeIORef v x
  getVar v = liftIO $ readIORef v
  modVar v f = liftIO $ modifyIORef' v f

instance MonadTcImports Tc where
  type Pkg Tc = Hir
  depPkgExists name = do
    x <- asks (.depPkgs)
    liftIO $ HT.lookup x name <&> isJust
  getDepPkg name = do
    x <- asks (.depPkgs)
    liftIO $ HT.lookup x name <&> must
  lookupTNameInPkg pkg ns n =
    liftIO $ HT.lookup pkg.exports ns >>= \case
      Just (_, nameToFqn, _) -> liftIO $ HT.lookup nameToFqn n
      _ -> pure Nothing
  lookupVNameInPkg pkg ns n =
    liftIO $ HT.lookup pkg.exports ns >>= \case
      Just (nameToFqn, _, _) -> liftIO $ HT.lookup nameToFqn n
      _ -> pure Nothing
  namespaceExistsInPkg pkg ns = liftIO $ HT.lookup pkg.exports ns <&> isJust
  namesFoundInPkg pkg ns names = do
    (vs, ts, _) <- liftIO $ HT.lookup pkg.exports ns <&> must
    forM names $ \n -> case nameToVNameOrTName n of
      Left n' -> liftIO $ HT.lookup vs n' <&> isJust
      Right n' -> liftIO $ HT.lookup ts n' <&> isJust
  getAllModulesInNs pkg ns = do
    liftIO $ HT.lookup pkg.exports ns <&> (must >>> thd3)

instance MonadTc Tc where
  getThisPkg = do
    hir <- asks (.ir)
    pure (hir.name, hir)
  getTDef1Maybe hir fqn = do
    liftIO $ HT.lookup hir.tDefs1 fqn
  getTDef2Maybe hir fqn = do
    liftIO $ HT.lookup hir.tDefs2 fqn
  getVDefMaybe hir fqn = do
    liftIO $ HT.lookup hir.vDefs fqn
  inputs = asks (.inputs)
  addTDef1 fqn d = do
    x <- asks (.ir.tDefs1)
    liftIO $ HT.insert x fqn d
  addTDef2 fqn d = do
    x <- asks (.ir.tDefs2)
    liftIO $ HT.insert x fqn d
  addVDef fqn d = do
    x <- asks (.ir.vDefs)
    liftIO $ HT.insert x fqn d
  addVDefExpr fqn e nextUid = do
    x <- asks (.ir.vDefExpr)
    liftIO $ HT.insert x fqn $ H.VDefExpr e nextUid
  addExportedDefs ns vs ts allModules = do
    x <- asks (.ir.exports)
    vs' <- liftIO $ HT.fromList vs
    ts' <- liftIO $ HT.fromList ts
    liftIO $ HT.insert x ns (vs', ts', allModules)
  mkLocalVarUid = do
    nextLocalVarUid <- asks (.nextLocalVarUid)
    i <- liftIO $ readIORef nextLocalVarUid
    liftIO $ modifyIORef' nextLocalVarUid (+ 1)
    pure $ LocalVarUid i
  getNextLocalVarUid = do
    nextLocalVarUid <- asks (.nextLocalVarUid)
    liftIO $ readIORef nextLocalVarUid
  resetLocalVarUids = do
    nextLocalVarUid <- asks (.nextLocalVarUid)
    liftIO $ writeIORef nextLocalVarUid 0
  getBlockDeclMaybe ns name = do
    cache <- asks (.blockDeclCache)
    liftIO $ HT.lookup cache (ns, name)
  addBlockDeclCache ns name x = do
    cache <- asks (.blockDeclCache)
    liftIO $ HT.insert cache (ns, name) x

instance MonadTcError Tc where
  getErrsListRev = do
    x <- asks (.errorsRev)
    liftIO $ readIORef x

  consErr e = do
    x <- asks (.errorsRev)
    liftIO $ modifyIORef' x (e :)

  throwTcException = liftIO $ throwIO $ TcException ()

  tryTcKeepErrors x = do
    r <- ask
    e <- liftIO $ try @TcException $ runReaderT x r
    errs <- getErrsListRev
    when (length errs > 100) throwTcException
    pure $ case e of Left _ -> Nothing; Right y -> Just y

instance MonadVars TcImpPre where
  type Var TcImpPre = IORef
  newVar = liftIO . newIORef
  setVar v x = liftIO $ writeIORef v x
  getVar v = liftIO $ readIORef v
  modVar v f = liftIO $ modifyIORef' v f

instance MonadTcImports TcImpPre where
  type Pkg TcImpPre = Hir
  depPkgExists name = do
    x <- asks (.depPkgs)
    liftIO $ HT.lookup x name <&> isJust
  getDepPkg name = do
    x <- asks (.depPkgs)
    liftIO $ HT.lookup x name <&> must
  lookupTNameInPkg pkg ns n =
    liftIO $ HT.lookup pkg.exports ns >>= \case
      Just (_, nameToFqn, _) -> liftIO $ HT.lookup nameToFqn n
      _ -> pure Nothing
  lookupVNameInPkg pkg ns n =
    liftIO $ HT.lookup pkg.exports ns >>= \case
      Just (nameToFqn, _, _) -> liftIO $ HT.lookup nameToFqn n
      _ -> pure Nothing
  namespaceExistsInPkg pkg ns = liftIO $ HT.lookup pkg.exports ns <&> isJust
  namesFoundInPkg pkg ns names = do
    (vs, ts, _) <- liftIO $ HT.lookup pkg.exports ns <&> must
    forM names $ \n -> case nameToVNameOrTName n of
      Left n' -> liftIO $ HT.lookup vs n' <&> isJust
      Right n' -> liftIO $ HT.lookup ts n' <&> isJust
  getAllModulesInNs pkg ns = do
    (_, ts, _) <- liftIO $ HT.lookup pkg.exports ns <&> must
    ts' <- liftIO $ HT.toList ts
    let modules = flip mapMaybe ts' $ \(_, export) -> case export.typ of
          IsModule blk -> Just blk
          _ -> Nothing
    pure modules

instance MonadTcError TcImpPre where
  getErrsListRev = do
    x <- asks (.errorsRev)
    liftIO $ readIORef x

  consErr e = do
    x <- asks (.errorsRev)
    liftIO $ modifyIORef' x (e :)

  throwTcException = liftIO $ throwIO $ TcException ()

  tryTcKeepErrors x = do
    r <- ask
    e <- liftIO $ try @TcException $ runReaderT x r
    errs <- getErrsListRev
    when (length errs > 100) throwTcException
    pure $ case e of Left _ -> Nothing; Right y -> Just y
