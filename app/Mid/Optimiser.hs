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
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Text qualified as T
import MhPrelude
import Mid.Mir qualified as M
import Names
import SrcLoc (SrcRange)
import Vars

-- Arbitrary value that determines how small a closure's expression needs to be to get inlined
inliningCutOff :: Int
inliningCutOff = 20

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
  clearSeenVars :: m ()
  addSeenVar :: M.LocalVarUid -> m ()
  isVarSeen :: M.LocalVarUid -> m Bool

optimisePackage :: HashMap PkgName M.Mir -> PkgName -> IO M.Mir
optimisePackage pkgs pkgName = do
  let pkg = must $ HM.lookup pkgName pkgs
  emptyVDefs <- HT.new
  let newPkg = M.Mir {name = pkg.name, vDefs = emptyVDefs}
  visited <- HT.new
  nextUidRef <- newIORef 0
  seenVars <- HT.new
  seenVars' <- newIORef seenVars
  let state = State pkgs pkg pkgName newPkg visited nextUidRef seenVars'
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
              savedNextUid <- getNextUid

              setNextUid vDef.nextLocalUid

              -- expr' <- pure expr >>= constFoldExpr 2 [] >>= simplifyExpr >>= constFoldExpr 2 [] >>= simplifyExpr
              expr' <- pure expr >>= constFoldExpr 0 [] >>= simplifyExpr
              nextLocalUid <- getNextUid
              setNextUid savedNextUid

              let vDef' = vDef {M.exprMaybe = Just expr', M.nextLocalUid}
              addOptimisedVDef vDef.fqn vDef'

              pure vDef'
        else
          fromMaybe vDef <$> getOptimisedVDef vDef.fqn
    else
      pure vDef

data Value = KnownConst M.Const | KnownClosure M.Fn | KnownCoroutine M.Fn | KnownAlias M.LocalVarUid
  deriving (Show, Eq)

type VarMap = [(M.LocalVarUid, Value)]

exprToConstMaybe :: M.Expr' -> Maybe M.Const
exprToConstMaybe = \case M.ELoadConst c -> Just c; _ -> Nothing

-- Also runs simplifier when inlining
constFoldExpr :: forall m. (MonadOpt m) => Int -> VarMap -> M.Expr -> m M.Expr
constFoldExpr inlineDepth startingVars exprToOpt = do
  let go :: VarMap -> M.Expr -> m M.Expr
      go vars expr@(expr', sr) = case expr' of
        M.EVar uid n -> do
          case lookup uid vars of
            Just (KnownConst c) -> pure (M.ELoadConst c, sr)
            Just (KnownAlias uid') -> pure (M.EVar uid' n, sr)
            _ -> pure expr
        M.ELoadConst {} -> pure expr
        M.EGlobal vFqn -> do
          vDef <- optimiseVDef' (vFqnToPkg vFqn) vFqn
          case vDef.exprMaybe of
            Just (e@(M.ELoadConst {}), _) -> pure (e, sr)
            Just (M.EClosure _, _) -> pure (M.ELoadConst $ M.CFn vFqn, sr)
            Nothing | (case vDef.type' of M.TFunc {} -> True; _ -> False) -> pure (M.ELoadConst $ M.CFn vFqn, sr)
            _ -> pure expr
        M.EUnreachable {} -> pure expr
        M.EBreak {} -> pure expr
        M.EContinue {} -> pure expr
        M.EVec xs -> do
          xs' <- forM xs $ go vars
          let knownConstsMaybe = forM xs' $ (fst >>> exprToConstMaybe)
          case knownConstsMaybe of
            Just cs -> do
              let c = M.CVec cs
              pure (M.ELoadConst c, snd expr)
            _ ->
              pure (M.EVec xs', snd expr)
        M.EFnCall callee ps isAsync retType -> do
          callee' <- go vars callee
          ps' <- forM ps $ go vars

          let fnCallExprNoInlining = (M.EFnCall callee' ps' isAsync retType, sr)
          let paramsConstsMaybe = (fst >>> exprToConstMaybe) <$> ps'
          let allParamsKnown = sequence paramsConstsMaybe
          -- let someParamsKnown = flip any ps' $ \(p, _) -> case p of
          --       M.EVar uid _ -> case lookup uid vars of
          --         Just (KnownConst _) -> True
          --         Just (KnownClosure _) -> True
          --         _ -> False
          --       M.EFnCall (M.EVar uid _, _) _ _ _ -> case lookup uid vars of
          --         Just (KnownCoroutine _) -> True
          --         _ -> False
          --       M.ELoadConst {} -> True
          --       M.EClosure {} -> True
          --       _ -> False
          let someParamsKnown = True
          --
          case (fst callee', allParamsKnown) of
            (M.ELoadConst (M.CFn (VFqn "#builtins/:VecBuiltins.iter")), _) ->
              pure $ ps' !! 0
            ((M.ELoadConst (M.CFn fqn)), Just paramsConsts)
              | "#builtins/:" `T.isPrefixOf` un fqn ->
                  evalBuiltin fqn paramsConsts sr fnCallExprNoInlining
            _ | inlineDepth > 0 -> do
              fnMaybe <- case fst callee' of
                (M.EVar uid _) -> do
                  case lookup uid vars of
                    Just (KnownClosure fn) ->
                      pure $ Just fn
                    _ -> pure Nothing
                (M.ELoadConst (M.CFn fnFqn)) -> do
                  vDef <- optimiseVDef' (vFqnToPkg fnFqn) fnFqn
                  case vDef.exprMaybe of
                    -- TODO Store weight as part of M.Fn or M.VDef
                    Just (M.EClosure fn, _)
                      | weighExpression fn.expr
                          < inliningCutOff ->
                          pure $ Just fn
                    _ -> pure Nothing
                _ -> pure Nothing

              case fnMaybe of
                Just fn | someParamsKnown -> do
                  -- Create id->id map for renaming fn parameters in fn.expr
                  -- And id->expr map for storing those parameters in variables
                  newUids <- forM (zip fn.params ps') $ \((uid, _, _, _), e) -> do
                    uid' <- generateNewUid
                    pure ((uid, uid'), (uid', e))

                  -- Apply newUids
                  newExpr <- renameExpr (fst <$> newUids) [] [] fn.expr

                  -- All parameters (except EVar) need to be stored in locals
                  -- The renamed & inlined expression accesses these variables instead of it's original parameters
                  let stmts' =
                        (snd <$> newUids)
                          <&> \(newUid, argExpr) ->
                            (M.SLet newUid Nothing False argExpr, sr)

                  -- Callee cannot be discarded in case it has effects
                  let stmts = (M.SExpr callee', sr) : stmts'

                  let e =
                        if isNothing fn.yieldType
                          then
                            -- Normal function call.
                            -- Function call expression is replaced with let statements for parameters then the fn expr
                            mkDo stmts (Just newExpr) sr
                          else do
                            -- Coroutine.
                            -- The expression needs to be wrapped in a closure
                            let fn' =
                                  M.Fn
                                    { params = [],
                                      ret = M.TUnit,
                                      expr = newExpr,
                                      effects = M.Effects True True,
                                      fqn = fn.fqn,
                                      isAsync = False,
                                      yieldType = fn.yieldType
                                    }
                            let e' = M.EFnCall (M.EClosure fn', sr) [] False (M.TIter $ must fn.yieldType)
                            mkDo stmts (Just (e', sr)) sr

                  e' <- constFoldExpr (inlineDepth - 1) vars e
                  simplifyExpr e'
                -- pure e
                _ ->
                  pure fnCallExprNoInlining
            _ -> pure fnCallExprNoInlining
        M.EClosure fn -> do
          e <- go vars fn.expr
          let fn' = fn {M.expr = e}
          pure (M.EClosure fn', sr)
        M.EDoBlock stmts exprMaybe -> do
          varsVar <- newVar vars

          stmts' <- forM stmts $ \(stmt, sr') -> do
            vars' <- getVar varsVar
            case stmt of
              M.SLet uid name mut e -> do
                e' <- go vars' e
                unless mut
                  $ case fst e' of
                    M.ELoadConst c ->
                      modVar varsVar ((uid, KnownConst c) :)
                    M.EClosure fn
                      | isNothing fn.yieldType && notNull fn.params && weighExpression fn.expr < inliningCutOff ->
                          modVar varsVar ((uid, KnownClosure fn) :)
                    (M.EFnCall (M.EClosure fn, _) [] _ _)
                      | isJust fn.yieldType && weighExpression fn.expr < inliningCutOff ->
                          modVar varsVar ((uid, KnownCoroutine fn) :)
                    M.EVar uid' _ ->
                      modVar varsVar ((uid, KnownAlias uid') :)
                    _ -> pure ()
                pure (M.SLet uid name mut e', sr')
              M.SRecLet uid name e -> do
                e' <- go vars' e
                pure (M.SRecLet uid name e', sr')
              M.SLetUninit {} ->
                pure (stmt, sr')
              M.SExpr e -> do
                e' <- go vars' e
                pure (M.SExpr e', sr')
              M.SAssign uid name e -> do
                e' <- go vars' e
                pure (M.SAssign uid name e', sr')
              M.SLoop e uid -> do
                e' <- go vars' e
                pure (M.SLoop e' uid, sr')
              M.SBreakBlock e uid -> do
                e' <- go vars' e
                pure (M.SBreakBlock e' uid, sr')
              M.SForEach {iterExpr, bodyExpr, elemUid, label} -> do
                iterExpr' <- go vars' iterExpr
                bodyExpr' <- go vars' bodyExpr
                let noInline = (stmt {M.iterExpr = iterExpr', M.bodyExpr = bodyExpr'}, sr')
                fnMaybe <- case iterExpr' of
                  (M.EFnCall (M.EClosure fn, _) [] _ _, _) -> pure $ Just fn
                  (M.EFnCall (M.ELoadConst (M.CFn fnFqn), _) [] _ _, _) -> do
                    vDef <- optimiseVDef' (vFqnToPkg fnFqn) fnFqn
                    case vDef.exprMaybe of
                      -- TODO Store weight as part of M.Fn or M.VDef
                      Just (M.EClosure fn, _)
                        | weighExpression fn.expr
                            < inliningCutOff
                            && isJust fn.yieldType -> do
                            pure $ Just fn
                      _ -> pure Nothing
                  (M.EFnCall ((M.EVar uid _), _) [] _ _, _) ->
                    case lookup uid vars' of
                      Just (KnownClosure fn) ->
                        pure $ Just fn
                      _ -> pure Nothing
                  ((M.EVar uid _), _) -> do
                    case lookup uid vars' of
                      Just (KnownCoroutine fn) ->
                        pure $ Just fn
                      _ -> pure Nothing
                  _ -> pure Nothing
                case fnMaybe of
                  Just fn -> do
                    -- Inline
                    s <- do
                      outerBlockUid <- generateNewUid
                      e1 <- replaceYield elemUid (label, outerBlockUid) bodyExpr' fn.expr
                      let e2 = (M.SExpr e1, sr')

                      let breakOuter = (M.SExpr (M.EBreak outerBlockUid, sr), sr)
                      let outerBlockExpr = (M.EDoBlock ([e2, breakOuter]) Nothing, sr)
                      let outerBlock = (M.SBreakBlock outerBlockExpr outerBlockUid, sr)
                      pure outerBlock
                    let w = weighExpression (M.EDoBlock [s] Nothing, sr)
                    let weightChange = w - weighExpression bodyExpr' - weighExpression iterExpr'
                    pure $ if weightChange < inliningCutOff then s else noInline
                  _ -> do
                    pure noInline

          eMaybe <- forM exprMaybe $ \e -> do
            vars' <- getVar varsVar
            go vars' e

          pure $ mkDo stmts' eMaybe sr
        M.EIf cond thenExpr elseExpr ty -> do
          cond' <- go vars cond
          case fst cond' of
            (M.ELoadConst (M.CBool True)) ->
              go vars thenExpr
            (M.ELoadConst (M.CBool False)) ->
              go vars elseExpr
            _ -> do
              thenExpr' <- go vars thenExpr
              elseExpr' <- go vars elseExpr
              pure (M.EIf cond' thenExpr' elseExpr' ty, sr)
        M.EProduct exprs -> do
          exprs' <- forM exprs $ go vars
          pure (M.EProduct exprs', sr)
        M.ESum types idx valExpr -> do
          valExpr' <- go vars valExpr
          pure (M.ESum types idx valExpr', sr)
        M.EAnd left right -> do
          left' <- go vars left
          case fst left' of
            (M.ELoadConst (M.CBool False)) -> pure left'
            (M.ELoadConst (M.CBool True)) -> go vars right
            _ -> do
              right' <- go vars right
              pure (M.EAnd left' right', sr)
        M.EOr left right -> do
          left' <- go vars left
          case fst left' of
            (M.ELoadConst (M.CBool True)) -> pure left'
            (M.ELoadConst (M.CBool False)) -> go vars right
            _ -> do
              right' <- go vars right
              pure (M.EOr left' right', sr)
        M.ETry tryExpr catchClauses finallyExpr -> do
          tryExpr' <- go vars tryExpr
          catchClauses' <- forM catchClauses $ \(ts, uid, sr', body) -> do
            body' <- go vars body
            pure (ts, uid, sr', body')
          finallyExpr' <- forM finallyExpr $ go vars
          pure (M.ETry tryExpr' catchClauses' finallyExpr', sr)
        M.EThrow throwExpr ty -> do
          throwExpr' <- go vars throwExpr
          pure (M.EThrow throwExpr' ty, sr)
        M.EYield throwExpr -> do
          yieldExpr' <- go vars throwExpr
          pure (M.EYield yieldExpr', sr)
        M.EIndex e idx name -> go vars e <&> \e' -> (M.EIndex e' idx name, sr)
        M.ESumTypeActiveIndex e -> go vars e <&> \e' -> (M.ESumTypeActiveIndex e', sr)
        M.ESumTypeGet e -> go vars e <&> \e' -> (M.ESumTypeGet e', sr)
        M.EUnreachableCast e t -> go vars e <&> \e' -> (M.EUnreachableCast e' t, sr)
        M.EAddFnEffects e t -> go vars e <&> \e' -> (M.EAddFnEffects e' t, sr)
        M.ESignExtendInt e -> go vars e <&> \e' -> (M.ESignExtendInt e', sr)
        M.EIntToF64 e -> go vars e <&> \e' -> (M.EIntToF64 e', sr)
        M.ECastNumber e ty -> go vars e <&> \e' -> (M.ECastNumber e' ty, sr)

  go startingVars exprToOpt

-- Does not call into any other passes
simplifyExpr :: forall m. (MonadOpt m) => M.Expr -> m M.Expr
simplifyExpr exprToOpt = do
  clearSeenVars

  let go :: M.Expr -> m M.Expr
      go expr@(expr', sr) = case expr' of
        M.EVar uid _ -> do
          addSeenVar uid
          pure expr
        M.ELoadConst {} -> pure expr
        M.EGlobal {} -> pure expr
        M.EUnreachable {} -> pure expr
        M.EBreak uid -> addSeenVar uid >> pure expr
        M.EContinue {} -> pure expr
        M.EVec xs -> forM xs go <&> \xs' -> (M.EVec xs', snd expr)
        M.EFnCall (M.EDoBlock ss (Just doExpr), _) ps isAsync t ->
          go (M.EDoBlock ss $ Just (M.EFnCall doExpr ps isAsync t, sr), sr)
        M.EFnCall callee ps isAsync retType -> do
          callee' <- go callee
          ps' <- forM ps go

          case fst callee' of
            M.EClosure fn | isNothing fn.yieldType -> do
              let stmts =
                    zip fn.params ps' <&> \((uid, _, _, _), e) ->
                      (M.SLet uid Nothing False e, snd e)
              pure $ mkDo stmts (Just fn.expr) (snd callee')
            _ ->
              pure (M.EFnCall callee' ps' isAsync retType, sr)
        M.EClosure fn -> do
          e <- go fn.expr
          let fn' = fn {M.expr = e}
          pure (M.EClosure fn', sr)
        M.EDoBlock [] (Just e) -> go e
        M.EDoBlock [(M.SExpr blk@(M.EDoBlock _ Nothing, _), _)] Nothing -> go blk
        --
        -- Removes unused statements
        --
        M.EDoBlock stmts (exprMaybe) -> do
          exprMaybe' <- forM exprMaybe go

          -- TODO Could traverse the tree, look for impure EFnCall, EThrow, EYield, EUnreachable, SAssign
          let exprCanBeCulled = \case
                M.ELoadConst {} -> True
                M.EGlobal {} -> True
                M.EClosure {} -> True
                M.EFnCall (M.EClosure fn, _) [] _ _ | isJust fn.yieldType -> True
                M.EVar {} -> True
                M.EDoBlock [] Nothing -> True
                M.EVec [] -> True
                -- TODO EFnCall if pure (need effect information in the expression)
                _ -> False

          stmtsMaybeRev <- forM (reverse stmts) $ \s'@(s, sr') -> case s of
            M.SLet uid n mut e -> do
              used <- isVarSeen uid
              if used
                then do
                  go e <&> \e' -> case e' of
                    (M.EDoBlock stmts' (Just doExpr), _) -> stmts' <> [(M.SLet uid n mut doExpr, sr')]
                    (M.EDoBlock stmts' Nothing, _) -> stmts' <> [(M.SLet uid n mut (M.EDoBlock [] Nothing, sr'), sr')]
                    _ -> [(M.SLet uid n mut e', sr')]
                else
                  if exprCanBeCulled (fst e)
                    then
                      pure []
                    else do
                      go e <&> \e' -> case e' of
                        (M.EDoBlock stmts' (Just doExpr), _) -> stmts' <> [(M.SExpr doExpr, sr')]
                        (M.EDoBlock stmts' Nothing, _) -> stmts'
                        _ -> [(M.SExpr e', sr')]
            M.SRecLet uid n e -> do
              used <- isVarSeen uid
              if used
                then go e <&> \e' -> [(M.SRecLet uid n e', sr')]
                else pure []
            M.SLetUninit uid _ -> do
              used <- isVarSeen uid
              pure $ if used then [s'] else []
            M.SExpr e -> do
              if exprCanBeCulled $ fst e
                then
                  pure []
                else do
                  go e <&> \e' -> case e' of
                    (M.EDoBlock stmts' (Just doExpr), _) -> stmts' <> [(M.SExpr doExpr, sr')]
                    (M.EDoBlock stmts' Nothing, _) -> stmts'
                    _ -> [(M.SExpr e', sr')]
            M.SAssign uid n e -> do
              addSeenVar uid
              e' <- go e
              pure [(M.SAssign uid n e', sr')]
            M.SLoop e uid -> do
              e' <- go e
              pure [(M.SLoop e' uid, sr')]
            M.SBreakBlock e uid -> do
              e' <- go e
              used <- isVarSeen uid
              pure
                $ if used
                  then
                    [(M.SBreakBlock e' uid, sr')]
                  else case e' of
                    (M.EDoBlock stmts' (Just doExpr), _) -> stmts' <> [(M.SExpr doExpr, sr')]
                    (M.EDoBlock stmts' Nothing, _) -> stmts'
                    _ -> [(M.SExpr e', sr')]
            M.SForEach {iterExpr, bodyExpr} -> do
              iterExpr' <- go iterExpr
              bodyExpr' <- go bodyExpr
              pure [(s {M.iterExpr = iterExpr', M.bodyExpr = bodyExpr'}, sr')]

          let stmts' = concat $ reverse stmtsMaybeRev

          pure $ case exprMaybe' of
            (Just (M.EDoBlock stmts'' doExpr, _)) -> mkDo (stmts' <> stmts'') doExpr sr
            _ -> mkDo stmts' exprMaybe' sr
        M.EIf cond thenExpr elseExpr ty -> do
          cond' <- go cond
          thenExpr' <- go thenExpr
          elseExpr' <- go elseExpr
          pure (M.EIf cond' thenExpr' elseExpr' ty, sr)
        M.EProduct exprs -> do
          exprs' <- forM exprs go
          pure (M.EProduct exprs', sr)
        M.ESum types idx valExpr -> do
          valExpr' <- go valExpr
          pure (M.ESum types idx valExpr', sr)
        M.EAnd left right -> do
          left' <- go left
          right' <- go right
          pure (M.EAnd left' right', sr)
        M.EOr left right -> do
          left' <- go left
          right' <- go right
          pure (M.EOr left' right', sr)
        M.ETry tryExpr catchClauses finallyExpr -> do
          tryExpr' <- go tryExpr
          catchClauses' <- forM catchClauses $ \(ts, uid, sr', body) -> do
            body' <- go body
            pure (ts, uid, sr', body')
          finallyExpr' <- forM finallyExpr $ go
          pure (M.ETry tryExpr' catchClauses' finallyExpr', sr)
        M.EThrow throwExpr ty -> do
          throwExpr' <- go throwExpr
          pure (M.EThrow throwExpr' ty, sr)
        M.EYield throwExpr -> do
          yieldExpr' <- go throwExpr
          pure (M.EYield yieldExpr', sr)
        M.EIndex e idx name -> go e <&> \e' -> (M.EIndex e' idx name, sr)
        M.ESumTypeActiveIndex e -> go e <&> \e' -> (M.ESumTypeActiveIndex e', sr)
        M.ESumTypeGet e -> go e <&> \e' -> (M.ESumTypeGet e', sr)
        M.EUnreachableCast e t -> go e <&> \e' -> (M.EUnreachableCast e' t, sr)
        M.EAddFnEffects e t -> go e <&> \e' -> (M.EAddFnEffects e' t, sr)
        M.ESignExtendInt e -> go e <&> \e' -> (M.ESignExtendInt e', sr)
        M.EIntToF64 e -> go e <&> \e' -> (M.EIntToF64 e', sr)
        M.ECastNumber e ty -> go e <&> \e' -> (M.ECastNumber e' ty, sr)

  go exprToOpt

mkDo :: [M.Stmt] -> Maybe M.Expr -> SrcRange -> M.Expr
mkDo [] (Just e) _sr = e
mkDo ss e sr = (M.EDoBlock ss e, sr)

replaceYield :: (MonadOpt m) => M.LocalVarUid -> (M.LocalVarUid, M.LocalVarUid) -> M.Expr -> M.Expr -> m M.Expr
replaceYield elemUid breakUidMap withExpr inExpr@(_, sr) = do
  let go = replaceYield elemUid breakUidMap withExpr
  case fst inExpr of
    M.ELoadConst {} -> pure inExpr
    M.EVec xs -> forM xs go <&> \xs' -> (M.EVec xs', sr)
    M.EVar {} -> pure inExpr
    M.EGlobal {} -> pure inExpr
    -- Yields inside a nested closure belong to that closure, not the iterator being inlined
    M.EClosure {} -> pure inExpr
    M.EFnCall callee args isAsync t -> do
      callee' <- go callee
      args' <- forM args go
      pure (M.EFnCall callee' args' isAsync t, sr)
    M.EDoBlock stmts doExpr -> do
      stmts' <- forM stmts $ \(s', sr') -> case s' of
        M.SLet uid nameMaybe isMut e -> go e <&> \e' -> (M.SLet uid nameMaybe isMut e', sr')
        M.SRecLet uid nameMaybe e -> go e <&> \e' -> (M.SRecLet uid nameMaybe e', sr')
        M.SLetUninit {} -> pure (s', sr')
        M.SExpr e -> go e <&> \e' -> (M.SExpr e', sr')
        M.SAssign uid nameMaybe e -> go e <&> \e' -> (M.SAssign uid nameMaybe e', sr')
        M.SLoop e uid -> go e <&> \e' -> (M.SLoop e' uid, sr')
        M.SBreakBlock e uid -> go e <&> \e' -> (M.SBreakBlock e' uid, sr')
        M.SForEach {iterExpr, bodyExpr} -> do
          iterExpr' <- go iterExpr
          bodyExpr' <- go bodyExpr
          pure (s' {M.iterExpr = iterExpr', M.bodyExpr = bodyExpr'}, sr')
      doExpr' <- forM doExpr go
      pure (mkDo stmts' doExpr' sr)
    M.EIf cond thenE elseE t -> do
      cond' <- go cond
      thenE' <- go thenE
      elseE' <- go elseE
      pure (M.EIf cond' thenE' elseE' t, sr)
    M.EProduct (List2 a b cs) -> do
      a' <- go a
      b' <- go b
      cs' <- forM cs go
      pure (M.EProduct (List2 a' b' cs'), sr)
    M.ESum types idx e -> go e <&> \e' -> (M.ESum types idx e', sr)
    M.EUnreachable {} -> pure inExpr
    M.EAnd x y -> do
      x' <- go x
      y' <- go y
      pure (M.EAnd x' y', sr)
    M.EOr x y -> do
      x' <- go x
      y' <- go y
      pure (M.EOr x' y', sr)
    M.ETry {tryExpr, catch, finally} -> do
      tryExpr' <- go tryExpr
      catch' <- forM catch $ \(ts, uid, sr', e) -> do
        e' <- go e
        pure (ts, uid, sr', e')
      finally' <- forM finally go
      pure (M.ETry {tryExpr = tryExpr', catch = catch', finally = finally'}, sr)
    M.EThrow e t -> do
      go e <&> \e' -> (M.EThrow e' t, sr)
    M.EYield e -> do
      e' <- go e
      yieldUid <- generateNewUid
      let yieldStmt = (M.SLet yieldUid Nothing False e', sr)
      outerBlockUid <- generateNewUid
      withExpr' <- renameExpr [(elemUid, yieldUid)] [breakUidMap] [(fst breakUidMap, outerBlockUid)] withExpr
      let withExpr'Stmt = (M.SExpr withExpr', sr)
      let breakOuter = (M.SExpr (M.EBreak outerBlockUid, sr), sr)
      let outerBlockExpr = (M.EDoBlock ([withExpr'Stmt, breakOuter]) Nothing, sr)
      let outerBlock = (M.SBreakBlock outerBlockExpr outerBlockUid, sr)
      pure (mkDo [yieldStmt, outerBlock] Nothing sr)
    M.EIndex e i nameMaybe -> go e <&> \e' -> (M.EIndex e' i nameMaybe, sr)
    M.ESumTypeActiveIndex e -> go e <&> \e' -> (M.ESumTypeActiveIndex e', sr)
    M.ESumTypeGet e -> go e <&> \e' -> (M.ESumTypeGet e', sr)
    M.EBreak {} -> pure inExpr
    M.EContinue {} -> pure inExpr
    M.EUnreachableCast e t -> go e <&> \e' -> (M.EUnreachableCast e' t, sr)
    M.EAddFnEffects e t -> go e <&> \e' -> (M.EAddFnEffects e' t, sr)
    M.ESignExtendInt e -> go e <&> \e' -> (M.ESignExtendInt e', sr)
    M.EIntToF64 e -> go e <&> \e' -> (M.EIntToF64 e', sr)
    M.ECastNumber e t -> go e <&> \e' -> (M.ECastNumber e' t, sr)

evalBuiltin ::
  (MonadOpt m) => VFqn -> [M.Const] -> SrcRange -> M.Expr -> m M.Expr
evalBuiltin (VFqn fqn) params sr fnCallExpr = do
  let doIntCmpFn op =
        case (params !! 0, params !! 1) of
          (M.CInt x, M.CInt y) -> do
            let b = x `op` y
            pure (M.ELoadConst $ M.CBool b, sr)
          _ -> undefined

  let doIntNumFn op =
        case (params !! 0, params !! 1) of
          (M.CInt x, M.CInt y) -> do
            let z = x `op` y
            -- Int is 53-bit
            let intMax = 4503599627370497
            let intMin = -4503599627370496
            if z >= intMin && z <= intMax
              then
                pure (M.ELoadConst $ M.CInt $ fromIntegral z, sr)
              else
                pure fnCallExpr
          _ -> undefined

  case T.drop (T.length "#builtins/:") fqn of
    "VecBuiltins.length" -> case params !! 0 of
      M.CVec xs -> do
        let i = length xs
        pure (M.ELoadConst $ M.CInt $ fromIntegral i, sr)
      _ -> undefined
    "VecBuiltins.atOrPanic" -> case (params !! 0, params !! 1) of
      (M.CVec xs, M.CInt i) -> do
        pure $ case xs !? fromIntegral i of
          Just c -> valueToExpr (snd fnCallExpr) c
          _ -> fnCallExpr
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
    "IntBuiltins.div" | params !! 1 /= M.CInt 0 -> doIntNumFn (div)
    "IntBuiltins.rem" | params !! 1 /= M.CInt 0 -> doIntNumFn (rem)
    _ -> pure fnCallExpr

valueToExpr :: SrcRange -> M.Const -> M.Expr
valueToExpr sr c = (M.ELoadConst c, sr)

type UidMap = [(M.LocalVarUid, M.LocalVarUid)]

-- break/continueUidMap is for inlining coroutines
renameExpr :: forall m. (MonadOpt m) => UidMap -> UidMap -> UidMap -> M.Expr -> m M.Expr
renameExpr startingUidMap breakUidMap continueUidMap exprToRename = do
  let go :: UidMap -> M.Expr -> m M.Expr
      go uidMap expr@(expr', sr) = case expr' of
        M.EVar uid n -> do
          let uid' = fromMaybe uid $ lookup uid uidMap
          pure (M.EVar uid' n, sr)
        M.ELoadConst {} -> pure expr
        M.EVec xs -> forM xs (go uidMap) <&> \xs' -> (M.EVec xs', sr)
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
        M.EDoBlock ss doExpr -> do
          uidMapVar <- newVar uidMap
          ss' <- forM ss $ \(s', sr') -> do
            uidMap' <- getVar uidMapVar
            case s' of
              M.SLet uid nameMaybe isMut e -> do
                uid' <- generateNewUid
                e' <- go uidMap' e
                modVar uidMapVar ((uid, uid') :)
                pure (M.SLet uid' nameMaybe isMut e', sr')
              M.SRecLet uid nameMaybe e -> do
                uid' <- generateNewUid
                let uidMap'' = (uid, uid') : uidMap'
                e' <- go uidMap'' e
                setVar uidMapVar uidMap''
                pure (M.SRecLet uid' nameMaybe e', sr')
              M.SLetUninit uid t -> do
                uid' <- generateNewUid
                modVar uidMapVar ((uid, uid') :)
                pure (M.SLetUninit uid' t, sr')
              M.SExpr e -> do
                e' <- go uidMap' e
                pure (M.SExpr e', sr')
              M.SAssign uid nameMaybe e -> do
                let uid' = fromMaybe uid $ lookup uid uidMap'
                e' <- go uidMap' e
                pure (M.SAssign uid' nameMaybe e', sr')
              M.SLoop e uid -> do
                uid' <- generateNewUid
                e' <- go ((uid, uid') : uidMap') e
                pure (M.SLoop e' uid', sr')
              M.SBreakBlock e uid -> do
                uid' <- generateNewUid
                e' <- go ((uid, uid') : uidMap') e
                pure (M.SBreakBlock e' uid', sr')
              M.SForEach {iterExpr, elemUid, elemNameMaybe, label, bodyExpr} -> do
                iterExpr' <- go uidMap' iterExpr
                elemUid' <- generateNewUid
                label' <- generateNewUid
                bodyExpr' <- go ((elemUid, elemUid') : (label, label') : uidMap') bodyExpr
                let e' =
                      M.SForEach
                        { iterExpr = iterExpr',
                          elemUid = elemUid',
                          elemNameMaybe,
                          label = label',
                          bodyExpr = bodyExpr'
                        }
                pure (e', sr')
          doExpr' <- do uidMap' <- getVar uidMapVar; forM doExpr $ go uidMap'
          pure (mkDo ss' doExpr' sr)
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
        M.ESum types idx e -> go uidMap e <&> \e' -> (M.ESum types idx e', sr)
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
        M.EThrow e t -> go uidMap e <&> \e' -> (M.EThrow e' t, sr)
        M.EYield e -> go uidMap e <&> \e' -> (M.EYield e', sr)
        M.EIndex e i nameMaybe -> go uidMap e <&> \e' -> (M.EIndex e' i nameMaybe, sr)
        M.ESumTypeActiveIndex e -> go uidMap e <&> \e' -> (M.ESumTypeActiveIndex e', sr)
        M.ESumTypeGet e -> go uidMap e <&> \e' -> (M.ESumTypeGet e', sr)
        M.EBreak uid -> case lookup uid breakUidMap of
          Just uid' -> pure (M.EBreak uid', sr)
          _ -> pure (M.EBreak $ must $ lookup uid uidMap, sr)
        M.EContinue uid -> case lookup uid continueUidMap of
          Just uid' -> pure (M.EBreak uid', sr) -- break is correct
          _ -> pure (M.EContinue $ must $ lookup uid uidMap, sr)
        M.EUnreachableCast e t -> go uidMap e <&> \e' -> (M.EUnreachableCast e' t, sr)
        M.EAddFnEffects e t -> go uidMap e <&> \e' -> (M.EAddFnEffects e' t, sr)
        M.ESignExtendInt e -> go uidMap e <&> \e' -> (M.ESignExtendInt e', sr)
        M.EIntToF64 e -> go uidMap e <&> \e' -> (M.EIntToF64 e', sr)
        M.ECastNumber e t -> go uidMap e <&> \e' -> (M.ECastNumber e' t, sr)

  go startingUidMap exprToRename

weighExpression :: M.Expr -> Int
weighExpression (e, _) = case e of
  M.ELoadConst {} -> 0
  M.EVec xs -> 1 + sum (weighExpression <$> xs)
  M.EVar {} -> 0
  M.EGlobal {} -> 1
  M.EClosure fn -> 1 + length fn.params + weighExpression fn.expr
  M.EFnCall e' ps _ _ -> 1 + weighExpression e' + sum (weighExpression <$> ps)
  M.EDoBlock ss exprMaybe -> sum (weighStmt <$> ss) + maybe 0 weighExpression exprMaybe
  M.EIf a b c _ -> 1 + weighExpression a + weighExpression b + weighExpression c
  M.EProduct xs -> 1 + sum (weighExpression <$> xs)
  M.ESum _ _ e' -> 1 + weighExpression e'
  M.EUnreachable {} -> 1
  M.EAnd l r -> 1 + weighExpression l + weighExpression r
  M.EOr l r -> 1 + weighExpression l + weighExpression r
  M.ETry {tryExpr, catch, finally} ->
    1 + weighExpression tryExpr + sum (catch <&> \(_, _, _, e') -> weighExpression e') + maybe 0 weighExpression finally
  M.EThrow e' _ -> 1 + weighExpression e'
  M.EYield e' -> 1 + weighExpression e'
  M.EIndex e' _ _ -> 1 + weighExpression e'
  M.ESumTypeActiveIndex e' -> 1 + weighExpression e'
  M.ESumTypeGet e' -> 1 + weighExpression e'
  M.EBreak {} -> 1
  M.EContinue {} -> 1
  M.EUnreachableCast e' _ -> 1 + weighExpression e'
  M.EAddFnEffects e' _ -> weighExpression e'
  M.ESignExtendInt e' -> 1 + weighExpression e'
  M.EIntToF64 e' -> 1 + weighExpression e'
  M.ECastNumber e' _ -> 1 + weighExpression e'

weighStmt :: M.Stmt -> Int
weighStmt (s, _) = case s of
  M.SLet _ _ _ e -> weighExpression e
  M.SRecLet _ _ e -> 1 + weighExpression e
  M.SLetUninit {} -> 0
  M.SExpr e -> weighExpression e
  M.SAssign _ _ e -> 1 + weighExpression e
  M.SLoop e _ -> 1 + weighExpression e
  M.SBreakBlock e _ -> weighExpression e
  M.SForEach {iterExpr, bodyExpr} -> 1 + weighExpression iterExpr + weighExpression bodyExpr

data State = State
  { pkgs :: HashMap PkgName M.Mir,
    thisPkg :: M.Mir,
    thisPkgName :: PkgName,
    newPkg :: M.Mir,
    visited :: HashTableSet VFqn,
    nextUid :: IORef Int,
    seenVars :: IORef (HashTableSet M.LocalVarUid)
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
  clearSeenVars = do
    seenVarsRef <- asks (.seenVars)
    x <- liftIO $ HT.new
    liftIO $ writeIORef seenVarsRef x
  addSeenVar uid = do
    seenVarsRef <- asks (.seenVars)
    x <- liftIO $ readIORef seenVarsRef
    liftIO $ HT.insert x uid ()
  isVarSeen uid = do
    seenVarsRef <- asks (.seenVars)
    x <- liftIO $ readIORef seenVarsRef
    liftIO $ HT.lookup x uid <&> isJust
