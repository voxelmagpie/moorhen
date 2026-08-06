-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{- HLINT ignore "Use head" -}

module Mid.Optimiser (optimisePackage) where

import Control.Monad (forM, forM_, unless)
import Control.Monad.Reader (MonadIO (liftIO), ReaderT (runReaderT), ask, asks)
import Data.HashMap.Strict qualified as HM
import Data.HashTable.IO qualified as HT
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Text qualified as T
import MhPrelude
import Mid.Mir qualified as M
import Names
import SrcLoc (SrcRange)
import Vars

-- Arbitrary value that determines how small a closure's expression needs to be to get inlined
inliningCutOff :: Int
inliningCutOff = 20

-- If greater than 1 then the inliner becomes recursive
maxInliningDepth :: Int
maxInliningDepth = 1

data KnownValue = KnownConst M.Const | KnownClosure M.Fn (Maybe KnownValue)

class (MonadVars m) => MonadOpt m where
  type Pkg m :: Type
  getThisPkg :: m (PkgName, Pkg m)
  getPkg :: PkgName -> m (Pkg m)
  getVDefs :: Pkg m -> m [M.VDef]
  getVDef :: VFqn -> m M.VDef
  addOptimisedVDef :: VFqn -> M.VDef -> m ()
  getOptimisedVDef :: VFqn -> m (Maybe M.VDef)
  vDefIsVisited :: VFqn -> m Bool
  setVDefVisited :: VFqn -> m ()
  generateNewUid :: m M.LocalVarUid
  getNextUid :: m Int
  setNextUid :: Int -> m ()
  getDepthLimit :: m Int
  setDepthLimit :: Int -> m ()

optimisePackage :: HashMap PkgName M.Mir -> PkgName -> IO M.Mir
optimisePackage pkgs pkgName = do
  let pkg = must $ HM.lookup pkgName pkgs
  emptyVDefs <- HT.new
  let newPkg = M.Mir {name = pkg.name, vDefs = emptyVDefs}
  depthLimRef <- newIORef 0
  visited <- HT.new
  nextUidRef <- newIORef 0
  let state = State pkgs pkg pkgName newPkg visited nextUidRef depthLimRef
  runReaderT optimisePackage' state
  pure newPkg

optimisePackage' :: (MonadOpt m) => m ()
optimisePackage' = do
  (pkgName, pkg) <- getThisPkg
  vdefs <- getVDefs pkg
  forM_ vdefs $ optimiseVDef pkgName

optimiseVDef' :: (MonadOpt m) => PkgName -> VFqn -> m M.VDef
optimiseVDef' pkgName vFqn = do
  vDef <- getVDef vFqn
  optimiseVDef pkgName vDef

optimiseVDef :: (MonadOpt m) => PkgName -> M.VDef -> m M.VDef
optimiseVDef pkg vDef = do
  (thisPkg, _) <- getThisPkg
  if pkg == thisPkg
    then do
      visited <- vDefIsVisited vDef.fqn
      if not visited
        then do
          setVDefVisited vDef.fqn
          case vDef.exprMaybe of
            Nothing -> do
              addOptimisedVDef vDef.fqn vDef
              pure vDef
            Just expr -> do
              d <- getDepthLimit
              savedNextUid <- getNextUid

              setNextUid vDef.nextLocalUid
              setDepthLimit maxInliningDepth
              (expr', value) <- constFoldInlineExpr [] expr
              nextLocalUid <- getNextUid
              -- TODO Simplification pass

              setNextUid savedNextUid
              setDepthLimit d

              let value' = case value of Just (KnownConst c) -> Just c; _ -> Nothing

              let vDef' = vDef {M.exprMaybe = Just expr', M.value = value', M.nextLocalUid}
              addOptimisedVDef vDef.fqn vDef'

              pure vDef'
        else
          fromMaybe vDef <$> getOptimisedVDef vDef.fqn
    else
      pure vDef

type VarMap = [(M.LocalVarUid, KnownValue)]

constFoldInlineExpr :: forall m. (MonadOpt m) => VarMap -> M.Expr -> m (M.Expr, Maybe KnownValue)
constFoldInlineExpr startingVars exprToOpt = do
  let go :: VarMap -> M.Expr -> m (M.Expr, Maybe KnownValue)
      go vars expr@(expr', sr) = case expr' of
        M.EVar uid ->
          -- Don't need to change the expression, loading a var is free
          pure (expr, lookup uid vars)
        M.ELoadConst x -> pure (expr, Just $ KnownConst x)
        M.EGlobal vFqn -> do
          vDef <- optimiseVDef' (vFqnToPkg vFqn) vFqn
          let v = case vDef.value of Just x -> KnownConst x; _ -> KnownConst $ M.CFn vFqn
          pure (expr, Just v)
        M.EUnreachable {} -> pure (expr, Nothing)
        M.EBreak {} -> pure (expr, Nothing)
        M.EContinue {} -> pure (expr, Nothing)
        M.EVec xs -> do
          xs' <- forM xs $ go vars
          let knownConstsMaybe = forM xs' $ (snd >>> (\case Just (KnownConst c) -> Just c; _ -> Nothing))
          case knownConstsMaybe of
            Just cs -> do
              let c = M.CVec cs
              pure ((M.ELoadConst c, snd expr), Just $ KnownConst c)
            _ ->
              pure ((M.EVec $ fst <$> xs', snd expr), Nothing)
        M.EFnCall callee ps isAsync retType -> do
          (callee', calleeValue) <- go vars callee
          ps' <- forM ps $ go vars

          let fnCallExprNoInlining = ((M.EFnCall callee' (fst <$> ps') isAsync retType, sr), Nothing)
          case calleeValue of
            Just (KnownConst (M.CFn fqn))
              | all (snd >>> isJust) ps' && "#builtins/:" `T.isPrefixOf` un fqn ->
                  evalBuiltin fqn (snd <$> ps') sr fnCallExprNoInlining
            Just (KnownClosure _ (Just (KnownConst c))) -> do
              pure (valueToExpr sr c, Just $ KnownConst c)
            _ -> do
              calleeValue' <- case calleeValue of
                Just (KnownConst (M.CFn vFqn)) -> do
                  vDef <- getVDef vFqn
                  pure $ vDef.value <&> KnownConst
                _ -> pure calleeValue

              depthLim <- getDepthLimit
              case calleeValue' of
                Just (KnownClosure fn _) | depthLim > 0 -> do
                  -- Save current next UID in case we don't inline
                  savedNextUid <- getNextUid
                  setDepthLimit $ depthLim - 1

                  (newExpr', valMaybe) <-
                    if any (snd >>> isJust) ps'
                      then do
                        let vars' = flip mapMaybe (zip fn.params ps') $ \((uid, _, _, _), (_, c)) -> case c of
                              Just c' -> Just (uid, c')
                              _ -> Nothing
                        constFoldInlineExpr vars' fn.expr
                      else
                        pure (fn.expr, Nothing)

                  case valMaybe of
                    Just (KnownConst c) ->
                      pure (valueToExpr sr c, Just $ KnownConst c)
                    _ -> do
                      -- Create id map for renaming parameters and (id, expr) for storing parameters in variables
                      -- Var expressions just get mapped directly to the local variable
                      newUids <- forM (zip fn.params ps') $ \((uid, _, _, _), (e, _)) -> case fst e of
                        M.EVar uid' ->
                          pure ((uid, uid'), Nothing)
                        _ -> do
                          uid' <- generateNewUid
                          pure ((uid, uid'), Just (uid', e))

                      newExpr <- renameExpr (fst <$> newUids) newExpr'

                      setDepthLimit depthLim

                      if weighExpression newExpr < inliningCutOff
                        then do
                          -- All parameters (except EVar) need to be stored in locals
                          -- The renamed & inlined expression accesses these variables instead of it's original parameters
                          let stmts =
                                catMaybes (snd <$> newUids)
                                  <&> \(newUid, argExpr) ->
                                    (M.SLet newUid Nothing False argExpr, sr)
                          let e = if null stmts then newExpr else (M.EDoBlock stmts (Just newExpr), sr)
                          pure (e, Nothing)
                        else do
                          -- Restore next uid state since new uids from closure params & fnExpr are discarded
                          setNextUid savedNextUid
                          pure fnCallExprNoInlining
                _ -> do
                  pure fnCallExprNoInlining
        M.EClosure fn -> do
          (e, retValue) <- go vars fn.expr
          let fn' = fn {M.expr = e}
          pure ((M.EClosure fn', sr), Just $ KnownClosure fn' retValue)
        M.EDoBlock stmts exprMaybe -> do
          varsVar <- newVar vars
          stmts' <- forM stmts $ goStmt varsVar
          e <- case exprMaybe of
            Just e -> do
              vars' <- getVar varsVar
              (e', val) <- go vars' e
              pure ((M.EDoBlock stmts' (Just e'), sr), val)
            _ ->
              pure ((M.EDoBlock stmts' Nothing, sr), Nothing)
          pure e
        M.EIf cond thenExpr elseExpr ty -> do
          (cond', condVal) <- go vars cond
          case condVal of
            Just (KnownConst (M.CBool True)) ->
              go vars thenExpr
            Just (KnownConst (M.CBool False)) ->
              go vars elseExpr
            _ -> do
              (thenExpr', _) <- go vars thenExpr
              (elseExpr', _) <- go vars elseExpr
              pure ((M.EIf cond' thenExpr' elseExpr' ty, sr), Nothing)
        M.EProduct exprs -> do
          exprs' <- forM exprs $ go vars
          pure ((M.EProduct $ fst <$> exprs', sr), Nothing)
        M.ESum types idx valExpr -> do
          (valExpr', _) <- go vars valExpr
          pure ((M.ESum types idx valExpr', sr), Nothing)
        M.EAnd left right -> do
          -- This is short-circuiting so can't do constant folding unless code is pure (TODO)
          (left', _) <- go vars left
          (right', _) <- go vars right
          pure ((M.EAnd left' right', sr), Nothing)
        M.EOr left right -> do
          (left', _) <- go vars left
          (right', _) <- go vars right
          pure ((M.EOr left' right', sr), Nothing)
        M.ETry tryExpr catchClauses finallyExpr -> do
          (tryExpr', _) <- go vars tryExpr
          catchClauses' <- forM catchClauses $ \(ts, uid, sr', body) -> do
            (body', _) <- go vars body
            pure (ts, uid, sr', body')
          finallyExpr' <- forM finallyExpr $ go vars >>> (<&> fst)
          pure ((M.ETry tryExpr' catchClauses' finallyExpr', sr), Nothing)
        M.EThrow throwExpr ty -> do
          (throwExpr', _) <- go vars throwExpr
          pure ((M.EThrow throwExpr' ty, sr), Nothing)
        M.EIndex e idx name ->
          go vars e <&> \(e', _) -> ((M.EIndex e' idx name, sr), Nothing)
        M.ESumTypeActiveIndex e ->
          go vars e <&> \(e', _) -> ((M.ESumTypeActiveIndex e', sr), Nothing)
        M.ESumTypeGet e ->
          go vars e <&> \(e', _) -> ((M.ESumTypeGet e', sr), Nothing)
        M.EImplicitCast e ->
          go vars e <&> \(e', _) -> ((M.EImplicitCast e', sr), Nothing)
        M.ESignExtendInt e ->
          go vars e <&> \(e', _) -> ((M.ESignExtendInt e', sr), Nothing)
        M.EIntToF64 e ->
          go vars e <&> \(e', _) -> ((M.EIntToF64 e', sr), Nothing)
        M.ECastNumber e ty ->
          go vars e <&> \(e', _) -> ((M.ECastNumber e' ty, sr), Nothing)

      goStmt :: Var m VarMap -> M.Stmt -> m M.Stmt
      goStmt varsVar (stmt, sr) = do
        vars <- getVar varsVar
        case stmt of
          M.SLet uid name mut expr -> do
            (expr', value) <- go vars expr
            unless mut $ forM_ value $ \v -> modVar varsVar ((uid, v) :)
            pure (M.SLet uid name mut expr', sr)
          M.SRecLet uid name expr -> do
            (expr', _) <- go vars expr
            pure (M.SRecLet uid name expr', sr)
          M.SLetUninit {} -> do
            pure (stmt, sr)
          M.SExpr expr -> do
            (expr', _) <- go vars expr
            pure (M.SExpr expr', sr)
          M.SAssign uid name expr -> do
            (expr', _) <- go vars expr
            pure (M.SAssign uid name expr', sr)
          M.SLoop expr uid -> do
            (expr', _) <- go vars expr
            pure (M.SLoop expr' uid, sr)

  go startingVars exprToOpt

evalBuiltin ::
  (MonadOpt m) => VFqn -> [Maybe KnownValue] -> SrcRange -> (M.Expr, Maybe KnownValue) -> m (M.Expr, Maybe KnownValue)
evalBuiltin (VFqn fqn) ps'' sr fnExpr = do
  let doIntCmpFn op =
        case (must $ ps'' !! 0, must $ ps'' !! 1) of
          (KnownConst (M.CInt x), KnownConst (M.CInt y)) -> do
            let b = x `op` y
            pure ((M.ELoadConst $ M.CBool b, sr), Just $ KnownConst $ M.CBool b)
          _ -> undefined

  let doIntNumFn op =
        case (must $ ps'' !! 0, must $ ps'' !! 1) of
          (KnownConst (M.CInt x), KnownConst (M.CInt y)) -> do
            let z = x `op` y
            -- Int is 53-bit
            let intMax = 4503599627370497
            let intMin = -4503599627370496
            if z >= intMin && z <= intMax
              then
                pure ((M.ELoadConst $ M.CInt $ fromIntegral z, sr), Just $ KnownConst $ M.CInt z)
              else
                pure fnExpr
          _ -> undefined

  case T.drop (T.length "#builtins/:") fqn of
    "VecBuiltins.length" -> case must $ ps'' !! 0 of
      KnownConst (M.CVec xs) -> do
        let i = length xs
        pure ((M.ELoadConst $ M.CInt $ fromIntegral i, sr), Just $ KnownConst $ M.CInt $ fromIntegral i)
      _ -> undefined
    "VecBuiltins.atOrPanic" -> case (must $ ps'' !! 0, must $ ps'' !! 1) of
      (KnownConst (M.CVec xs), KnownConst (M.CInt i)) -> do
        let c = xs !! fromIntegral i
        pure (valueToExpr (snd $ fst fnExpr) c, Just $ KnownConst $ c)
      _ -> undefined
    "IntBuiltins.eq" -> doIntCmpFn (==)
    "IntBuiltins.neq" -> doIntCmpFn (/=)
    "IntBuiltins.gt" -> doIntCmpFn (>)
    "IntBuiltins.gte" -> doIntCmpFn (>=)
    "IntBuiltins.lt" -> doIntCmpFn (<)
    "IntBuiltins.lte" -> doIntCmpFn (<=)
    "IntBuiltins.add" -> doIntNumFn (+)
    "IntBuiltins.sub" -> doIntNumFn (-)
    "IntBuiltins.mul" -> doIntNumFn (*)
    _ -> pure fnExpr

valueToExpr :: SrcRange -> M.Const -> M.Expr
valueToExpr sr c = (M.ELoadConst c, sr)

type UidMap = [(M.LocalVarUid, M.LocalVarUid)]

renameExpr :: forall m. (MonadOpt m) => UidMap -> M.Expr -> m M.Expr
renameExpr startingUidMap exprToRename = do
  let go :: UidMap -> M.Expr -> m M.Expr
      go uidMap expr@(expr', sr) = case expr' of
        M.EVar uid -> do
          let uid' = fromMaybe uid $ lookup uid uidMap
          pure (M.EVar uid', sr)
        M.ELoadConst {} -> pure expr
        M.EVec xs -> do
          xs' <- forM xs $ go uidMap
          pure (M.EVec xs', sr)
        M.EGlobal {} -> pure expr
        M.EClosure fn -> do
          params <- forM fn.params $ \(_, a, b, c) -> do
            uid' <- generateNewUid
            pure (uid', a, b, c)
          let newUids = zip (fn.params <&> \(x, _, _, _) -> x) (params <&> \(x, _, _, _) -> x)
          e' <- go (newUids <> uidMap) (fn.expr)
          let fn' = fn {M.params, M.expr = e'}
          pure (M.EClosure fn', sr)
        M.EFnCall fnExpr args isAsync t -> do
          fnExpr' <- go uidMap fnExpr
          args' <- forM args $ go uidMap
          pure (M.EFnCall fnExpr' args' isAsync t, sr)
        M.EDoBlock ss e -> do
          uidMapVar <- newVar uidMap
          ss' <- forM ss $ goStmt uidMapVar
          e' <- do uidMap' <- getVar uidMapVar; forM e $ go uidMap'
          pure (M.EDoBlock ss' e', sr)
        M.EIf cond thenE elseE t -> do
          cond' <- go uidMap cond
          thenE' <- go uidMap thenE
          elseE' <- go uidMap elseE
          pure (M.EIf cond' thenE' elseE' t, sr)
        M.EProduct (List2 a b cs) -> do
          a' <- go uidMap a
          b' <- go uidMap b
          cs' <- forM cs $ go uidMap
          pure (M.EProduct (List2 a' b' cs'), sr)
        M.ESum types idx e -> do
          e' <- go uidMap e
          pure (M.ESum types idx e', sr)
        M.EUnreachable {} -> pure expr
        M.EAnd x y -> do
          x' <- go uidMap x
          y' <- go uidMap y
          pure (M.EAnd x' y', sr)
        M.EOr x y -> do
          x' <- go uidMap x
          y' <- go uidMap y
          pure (M.EOr x' y', sr)
        M.ETry {tryExpr, catch, finally} -> do
          tryExpr' <- go uidMap tryExpr
          catch' <- forM catch $ \(ts, uid, sr', e) -> do
            uid' <- generateNewUid
            e' <- go ((uid, uid') : uidMap) e
            pure (ts, uid', sr', e')
          finally' <- forM finally $ go uidMap
          pure (M.ETry {tryExpr = tryExpr', catch = catch', finally = finally'}, sr)
        M.EThrow e t -> do
          e' <- go uidMap e
          pure (M.EThrow e' t, sr)
        M.EIndex e i nameMaybe -> do
          e' <- go uidMap e
          pure (M.EIndex e' i nameMaybe, sr)
        M.ESumTypeActiveIndex e -> do
          e' <- go uidMap e
          pure (M.ESumTypeActiveIndex e', sr)
        M.ESumTypeGet e -> do
          e' <- go uidMap e
          pure (M.ESumTypeGet e', sr)
        M.EBreak uid -> do
          let uid' = must $ lookup uid uidMap
          pure (M.EBreak uid', sr)
        M.EContinue uid -> do
          let uid' = must $ lookup uid uidMap
          pure (M.EContinue uid', sr)
        M.EImplicitCast e -> do
          e' <- go uidMap e
          pure (M.EImplicitCast e', sr)
        M.ESignExtendInt e -> do
          e' <- go uidMap e
          pure (M.ESignExtendInt e', sr)
        M.EIntToF64 e -> do
          e' <- go uidMap e
          pure (M.EIntToF64 e', sr)
        M.ECastNumber e t -> do
          e' <- go uidMap e
          pure (M.ECastNumber e' t, sr)
      goStmt :: Var m UidMap -> M.Stmt -> m M.Stmt
      goStmt uidMapVar (s', sr) = do
        uidMap <- getVar uidMapVar
        case s' of
          M.SLet uid nameMaybe isMut e -> do
            uid' <- generateNewUid
            e' <- go uidMap e
            modVar uidMapVar ((uid, uid') :)
            pure (M.SLet uid' nameMaybe isMut e', sr)
          M.SRecLet uid nameMaybe e -> do
            uid' <- generateNewUid
            let uidMap' = (uid, uid') : uidMap
            e' <- go uidMap' e
            setVar uidMapVar uidMap'
            pure (M.SRecLet uid' nameMaybe e', sr)
          M.SLetUninit uid t -> do
            uid' <- generateNewUid
            modVar uidMapVar ((uid, uid') :)
            pure (M.SLetUninit uid' t, sr)
          M.SExpr e -> do
            e' <- go uidMap e
            pure (M.SExpr e', sr)
          M.SAssign uid nameMaybe e -> do
            let uid' = fromMaybe uid $ lookup uid uidMap
            e' <- go uidMap e
            pure (M.SAssign uid' nameMaybe e', sr)
          M.SLoop e uid -> do
            uid' <- generateNewUid
            e' <- go ((uid, uid') : uidMap) e
            pure (M.SLoop e' uid', sr)
  go startingUidMap exprToRename

weighExpression :: M.Expr -> Int
weighExpression (e, _) = case e of
  M.ELoadConst {} -> 1
  M.EVec xs -> 2 + sum (weighExpression <$> xs)
  M.EVar {} -> 1
  M.EGlobal {} -> 1
  M.EClosure fn -> 1 + length fn.params + weighExpression fn.expr
  M.EFnCall e' ps _ _ -> 2 + weighExpression e' + sum (weighExpression <$> ps)
  M.EDoBlock ss exprMaybe -> sum (weighStmt <$> ss) + maybe 0 weighExpression exprMaybe
  M.EIf a b c _ -> 2 + weighExpression a + weighExpression b + weighExpression c
  M.EProduct xs -> 2 + sum (weighExpression <$> xs)
  M.ESum _ _ e' -> 2 + weighExpression e'
  M.EUnreachable {} -> 2
  M.EAnd l r -> 2 + weighExpression l + weighExpression r
  M.EOr l r -> 2 + weighExpression l + weighExpression r
  M.ETry {tryExpr, catch, finally} ->
    3 + weighExpression tryExpr + sum (catch <&> \(_, _, _, e') -> weighExpression e') + maybe 0 weighExpression finally
  M.EThrow {} -> 2
  M.EIndex e' _ _ -> 1 + weighExpression e'
  M.ESumTypeActiveIndex e' -> 1 + weighExpression e'
  M.ESumTypeGet e' -> 1 + weighExpression e'
  M.EBreak {} -> 2
  M.EContinue {} -> 2
  M.EImplicitCast e' -> 1 + weighExpression e'
  M.ESignExtendInt e' -> 1 + weighExpression e'
  M.EIntToF64 e' -> 1 + weighExpression e'
  M.ECastNumber e' _ -> 1 + weighExpression e'

weighStmt :: M.Stmt -> Int
weighStmt (s, _) = case s of
  M.SLet _ _ _ e -> weighExpression e
  M.SRecLet _ _ e -> weighExpression e
  M.SLetUninit {} -> 0
  M.SExpr e -> weighExpression e
  M.SAssign _ _ e -> 1 + weighExpression e
  M.SLoop e _ -> 1 + weighExpression e

data State = State
  { pkgs :: HashMap PkgName M.Mir,
    thisPkg :: M.Mir,
    thisPkgName :: PkgName,
    newPkg :: M.Mir,
    visited :: HashTableSet VFqn,
    nextUid :: IORef Int,
    depthLim :: IORef Int
  }

type OptM = ReaderT State IO

instance MonadVars OptM where
  type Var OptM = IORef
  newVar = liftIO . newIORef
  setVar v x = liftIO $ writeIORef v x
  getVar v = liftIO $ readIORef v
  modVar v f = liftIO $ modifyIORef' v f

instance MonadOpt OptM where
  type Pkg OptM = M.Mir
  getThisPkg = do
    s <- ask
    pure (s.thisPkgName, s.thisPkg)
  getPkg pkgName = do
    s <- ask
    pure $ must $ HM.lookup pkgName s.pkgs
  getVDefs pkg = liftIO $ (snd <$>) <$> HT.toList pkg.vDefs
  getOptimisedVDef fqn = do
    p <- asks (.newPkg)
    liftIO $ HT.lookup p.vDefs fqn
  addOptimisedVDef fqn vdef = do
    p <- asks (.newPkg)
    liftIO $ HT.insert p.vDefs fqn vdef
  vDefIsVisited vFqn = do
    x <- asks (.visited)
    liftIO $ HT.lookup x vFqn <&> isJust
  setVDefVisited vFqn = do
    x <- asks (.visited)
    liftIO $ HT.insert x vFqn ()
  getVDef fqn = do
    pkg <- getPkg $ vFqnToPkg fqn
    liftIO $ HT.lookup pkg.vDefs fqn <&> must
  generateNewUid = do
    nextUidRef <- asks (.nextUid)
    i <- liftIO $ readIORef nextUidRef
    liftIO $ writeIORef nextUidRef (i + 1)
    pure $ M.LocalVarUid i
  getNextUid = do
    nextUidRef <- asks (.nextUid)
    liftIO $ readIORef nextUidRef
  setNextUid i = do
    nextUidRef <- asks (.nextUid)
    liftIO $ writeIORef nextUidRef i
  getDepthLimit = do
    x <- asks (.depthLim)
    liftIO $ readIORef x
  setDepthLimit d = do
    x <- asks (.depthLim)
    liftIO $ writeIORef x d
