-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{- HLINT ignore "Use head" -}

module Mid.HirToMir (toMir, MonadToMir (..)) where

import Control.Monad (forM, forM_)
import Control.Monad.Reader (MonadIO (liftIO), ReaderT (runReaderT), asks)
import Data.Foldable (Foldable (foldl1))
import Data.HashMap.Strict qualified as HM
import Data.HashTable.IO qualified as HT
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import Data.List (findIndex)
import Data.Maybe (fromMaybe, isJust)
import Data.Text qualified as T
import Front.Hir qualified as H
import Front.HirFns (isGenericOverEffect, typeToTextFull)
import GHC.Stack (HasCallStack)
import MhPrelude
import Mid.Mir qualified as M
import Names
import SrcLoc (SrcRange, srcRangeOf)
import Vars

-- MaybeAsync is for functions generic over the effect type
data IsAsync = NotAsync | MaybeAsync | IsAsync
  deriving (Show, Generic, Eq)

instance Semigroup IsAsync where
  x <> y | x == IsAsync || y == IsAsync = IsAsync
  x <> y | x == MaybeAsync || y == MaybeAsync = MaybeAsync
  _ <> _ = NotAsync

instance Monoid IsAsync where
  mempty = NotAsync

class (MonadVars m) => MonadToMir m where
  type Pkg m :: Type
  getThisPkg :: m (PkgName, Pkg m)
  getPkg :: PkgName -> m (Pkg m)
  getVDefs :: Pkg m -> m [(VFqn, H.VDef)]
  getVDefValue :: Pkg m -> VFqn -> m (Maybe H.VDefExpr)
  getDataTypeDefs :: Pkg m -> m [(TFqn, H.DataTypeDef)]
  getTDef :: Pkg m -> TFqn -> m H.TDef
  getDataTypeDef :: Pkg m -> TFqn -> m H.DataTypeDef
  getVDef :: Pkg m -> VFqn -> m H.VDef
  getTypeExport :: TFqn -> m H.TNameExport
  getModule :: TFqn -> m H.Module
  getTrait :: TFqn -> m H.Trait
  addVDef :: VFqn -> M.VDef -> m ()
  getIsAsync :: m Bool
  setIsAsync :: Bool -> m ()
  resetFnState :: m ()
  mkLocalVarUid :: m M.LocalVarUid
  getNextVarUid :: m Int
  setNextVarUid :: Int -> m ()
  generateWhereParamUid :: H.FromWhereClauseSource -> m M.LocalVarUid
  getWhereParamUid :: H.FromWhereClauseSource -> m (Maybe M.LocalVarUid)
  setVFqn :: VFqn -> m ()
  getVFqn :: m VFqn

toMir :: HashMap PkgName H.Hir -> PkgName -> IO M.Mir
toMir pkgs pkgName = do
  let hir = must $ HM.lookup pkgName pkgs
  c <- M.Mir hir.name <$> HT.new
  s <- State pkgs pkgName hir c <$> newIORef 0 <*> newIORef Nothing <*> newIORef Nothing <*> newIORef False <*> newIORef Nothing
  _ <- runReaderT toMir' s
  pure c

toMir' :: (MonadToMir m) => m ()
toMir' = do
  (_, pkg) <- getThisPkg

  dataTypeDefs <- getDataTypeDefs pkg

  forM_ dataTypeDefs $ \(tFqn, dataTypeDef) -> do
    forM (zip (toList dataTypeDef.dataCons) [0 :: Int ..]) $ \(H.DataCons (name, sr) x, dcIdx) -> do
      case x of
        H.RecordFields _ -> pure ()
        H.TupleFields [] -> pure ()
        H.TupleFields xs -> do
          -- Create a function that initialises the type
          let vFqn = VFqn $ "_" <> un tFqn <> "_" <> un name
          t <- cvtType dataTypeDef.t1.selfType
          ps <- forM xs cvtType
          let type' = M.TFunc ps t def False
          let pNames = [0 .. length xs - 1] <&> M.LocalVarUid
          let params = zip pNames ps <&> \(uid, t') -> (uid, Nothing, t', sr)
          let getters = pNames <&> \uid -> (M.EVar uid, sr)
          let e = mkDataConsInit ps getters dcIdx sr
          let fn = M.Fn params t e def vFqn False
          let nextUid = length xs
          let vDef = M.VDef (un name, sr) vFqn type' (Just (M.EClosure fn, sr)) Nothing nextUid
          addVDef vFqn vDef

  vDefs <- getVDefs pkg
  forM_ vDefs $ \(vFqn, vDef) -> do
    type' <- cvtType vDef.type'
    eMaybe <- getVDefValue pkg vFqn
    let needsBlockImplicitParam = isJust eMaybe && notNull (toList vDef.moduleWhereClauses)
    let needsImplicitParam = isJust eMaybe && notNull (toList vDef.whereClauses)
    let vDefName = first un vDef.name

    let go inAsyncCode fqn = do
          resetFnState
          setVFqn fqn
          setIsAsync inAsyncCode
          forM_ eMaybe $ \x -> setNextVarUid x.nextLocalUid
          whParamUidBlk <-
            if needsBlockImplicitParam
              then
                generateWhereParamUid H.FromBlockWheres
              else pure $ M.LocalVarUid (-1)
          whParamUid <-
            if needsImplicitParam
              then
                generateWhereParamUid H.FromVDefWheres
              else pure $ M.LocalVarUid (-1)
          exprMaybe <- case eMaybe of
            Just x -> Just <$> cvtExpr x.expr
            _ -> pure Nothing -- Builtin
            --
          let mkWrapper clauses whUid retType expr = do
                t <- mkWhereDataType $ un clauses <&> snd
                let wrapperType = M.TFunc [t] retType (M.Effects True True) False
                let sr = snd vDef.name
                let clo =
                      M.EClosure
                        $ M.Fn
                          { params = [(whUid, Nothing, t, sr)],
                            ret = retType,
                            expr,
                            effects = (M.Effects True True),
                            fqn = fqn,
                            isAsync = False
                          }
                pure ((clo, sr), wrapperType)

          (e, t) <- do
            let e1 = exprMaybe
            (e2, t2) <-
              if needsImplicitParam
                then
                  mkWrapper vDef.whereClauses whParamUid type' (must e1) <&> first Just
                else pure (e1, type')
            (e3, t3) <-
              if needsBlockImplicitParam
                then
                  mkWrapper vDef.moduleWhereClauses whParamUidBlk t2 (must e2) <&> first Just
                else pure (e2, t2)
            pure (e3, t3)

          nextUid <- getNextVarUid
          addVDef fqn $ M.VDef vDefName fqn t e Nothing nextUid
    if isGenericOverEffect vDef.genParams
      then do
        go False (VFqn $ un vFqn <> "$sync")
        go True (VFqn $ un vFqn <> "$async")
      else
        go False vFqn

-- dConssTypes can be set to [] if this is a product type, must be correct for sum types though
mkDataConsInit :: [M.Type] -> [M.Expr] -> Int -> SrcRange -> M.Expr
mkDataConsInit dConssTypes xs dcIdx sr = do
  let value = case listToList2 xs of
        Nothing | null xs -> (M.EDoBlock [] Nothing, sr)
        Nothing -> must $ head xs
        Just xs' -> (M.EProduct xs', sr)
  case listToList2 dConssTypes of
    Nothing ->
      value
    Just ts
      | all (== M.TUnit) ts ->
          (M.ELoadConst $ M.CI32 $ fromIntegral dcIdx, sr)
    Just ts ->
      (M.ESum ts dcIdx value, sr)

mkDestructureStmts :: (MonadToMir m) => H.Destructure -> M.Expr -> m [M.Stmt]
mkDestructureStmts (H.DIgnore, _, _) _ = pure []
mkDestructureStmts (H.DName n uid isMut, _, sr) e = do
  pure [(M.SLet (M.LocalVarUid $ un uid) (Just (un n, sr)) isMut e, sr)]
mkDestructureStmts (H.DTuple ds, _, sr) expr = do
  -- For tuples, use EIndex to access each element by position
  ss <- forM (zip [0 :: Int ..] (toList ds)) $ \(i, d) -> do
    let idxExpr = (M.EIndex expr i Nothing, sr)
    mkDestructureStmts d idxExpr
  pure $ concat ss
mkDestructureStmts (H.DDataCons dcInfo ds, _, sr) expr = do
  if dcInfo.isProduct
    then do
      case ds of
        List1 d [] ->
          -- Newtype
          mkDestructureStmts d expr
        _ -> do
          ss <- forM (zip [0 :: Int ..] (toList ds)) $ \(i, d) -> do
            let idxExpr = (M.EIndex expr i Nothing, sr)
            mkDestructureStmts d idxExpr
          pure $ concat ss
    else undefined
mkDestructureStmts (H.DRecord dcInfo ds, _, sr) expr = do
  if dcInfo.isProduct
    then do
      ss <- forM (zip [0 :: Int ..] ds) $ \(i, (n, d)) -> do
        let idxExpr = (M.EIndex expr i (Just n), sr)
        mkDestructureStmts d idxExpr
      pure $ concat ss
    else undefined
mkDestructureStmts (H.DAs n uid isMut d, _, sr) expr = do
  ss <- mkDestructureStmts d expr
  pure $ (M.SLet (M.LocalVarUid $ un uid) (Just $ first un n) isMut expr, sr) : ss

cvtClosure ::
  (MonadToMir m) =>
  H.Type -> [H.Destructure] -> H.Expr -> SrcRange -> m M.Expr
cvtClosure cloType cloArgs e'@(_, bodyType, _) sr = do
  let eff = case cloType of H.TFunc _ _ x -> x; _ -> undefined
  cloAsync <- effectCouldContainAsync eff

  -- Save current async state and set based on closure async flag
  -- It is possible that we have an async closure within a non-async closure, so long as it isn't called
  oldAsync <- getIsAsync
  async <- case cloAsync of
    NotAsync -> pure False
    IsAsync -> pure True
    MaybeAsync -> pure oldAsync
  setIsAsync async

  -- Convert closure arguments to parameter variables
  -- TODO If a destructure is DName then don't create redundant variable declarations
  params <- forM cloArgs $ \(_, t, sr') -> do
    t' <- cvtType t
    uid <- mkLocalVarUid
    pure (uid, Nothing, t', sr')

  -- Convert body expression & return type
  expr' <- cvtExpr e'
  let paramUids = params <&> \(x, _, _, sr') -> (M.EVar x, sr')
  destructureStmts <- forM (zip cloArgs paramUids) $ uncurry mkDestructureStmts
  let expr = (M.EDoBlock (concat destructureStmts) $ Just expr', sr)
  ret <- cvtType bodyType

  -- Restore previous async state
  setIsAsync oldAsync

  -- Set effects based on async flag
  let effects' = M.Effects {noThrow = True, pure = not async}

  -- Set effects based on HIR effect type

  let effects =
        effects' <> case cloType of
          H.TFunc _ _ ef -> findEffs ef
          _ -> error "Closure not TFunc"

  -- Create Mir function
  fqn <- getVFqn
  let fn = M.Fn {params, ret, expr, effects, fqn, isAsync = async}
  pure (M.EClosure fn, sr)

unreachableType :: H.Type
unreachableType = H.TNamed (TFqn "#builtins/:Unreachable") []

findEffs :: H.Type -> M.Effects
findEffs = \case
  H.TEffect ts -> mconcat $ findEffs <$> toList ts
  H.TNamed (TFqn "#builtins/:Throws") _ -> M.Effects {noThrow = False, pure = True}
  H.TNamed (TFqn "#builtins/:Impure") _ -> M.Effects {noThrow = True, pure = False}
  _ -> def

getDataConstructorTypes :: (MonadToMir m) => H.DataTypeDef -> m [M.Type]
getDataConstructorTypes dataTypeDef = do
  forM (toList dataTypeDef.dataCons) $ \(H.DataCons _ fs) -> do
    let fs' = case fs of
          H.TupleFields xs -> xs
          H.RecordFields xs -> snd <$> toList xs
    xs <- forM fs' cvtType
    pure $ case xs of
      [] -> M.TUnit
      [x] -> x
      (x : y : zs) -> M.TProduct $ List2 x y zs

gatherTraitWhereData :: (MonadToMir m) => SrcRange -> (H.TraitRef, H.ChosenTrait) -> m M.Expr
gatherTraitWhereData sr ((traitFqn, _), chosenTrait) = do
  a <- getIsAsync
  case chosenTrait of
    H.FromWhereClause loc -> do
      whUid <- getWhereParamUid loc.src
      let getVarExpr = (M.EVar $ must whUid, sr)
      let indexed1 =
            if loc.whereClausesTotal <= 1
              then
                getVarExpr
              else
                (M.EIndex getVarExpr loc.whereClauseIdx Nothing, sr)
      pure
        $ if loc.whereClauseTraitsTotal <= 1
          then
            getVarExpr
          else
            (M.EIndex indexed1 loc.whereClauseTraitIdx Nothing, sr)
    H.FromModule modFqn _genArgs modWhs -> do
      pkg <- getPkg $ tFqnToPkg modFqn
      trait <- getTrait traitFqn
      let traitNamesOrdered = trait.vDefs <&> ((.vDef.name) >>> fst)
      let fqns = traitNamesOrdered <&> \n -> VFqn $ un modFqn <> "." <> un n
      let exprs = fqns <&> \x -> (M.EGlobal x, sr)
      exprs' <-
        case modWhs of
          [] -> pure exprs
          (w : ws) -> do
            modWhs' <- gatherTraitsWhereData sr $ List1 w ws
            forM (zip fqns exprs) $ \(vFqn, e') -> do
              vDef <- getVDef pkg vFqn
              vDefType <- cvtType vDef.type'
              pure (M.EFnCall e' [modWhs'] a vDefType, sr)

      pure $ case exprs' of
        [] -> (M.EDoBlock [] Nothing, sr)
        e : es -> mkProductExprIfMany $ List1 e es

mkProductExprIfMany :: List1 M.Expr -> M.Expr
mkProductExprIfMany xs = case xs of
  List1 x [] -> x
  List1 x (y : zs) -> (M.EProduct $ List2 x y zs, srcRangeOf xs xs)

gatherTraitsWhereData :: (MonadToMir m) => SrcRange -> List1 (List1 (H.TraitRef, H.ChosenTrait)) -> m M.Expr
gatherTraitsWhereData sr ts = do
  xs <- forM ts $ \xs -> do
    ys <- forM xs $ gatherTraitWhereData sr
    pure $ mkProductExprIfMany ys
  pure $ mkProductExprIfMany xs

mkApplyWhereClausesExpr ::
  forall m. (MonadToMir m) => SrcRange -> M.Type -> H.WhereClauseTraitsList -> M.Expr -> m M.Expr
mkApplyWhereClausesExpr sr t' ts defExpr = do
  a <- getIsAsync

  case ts of
    [] -> pure defExpr
    y : ys -> do
      xs <- gatherTraitsWhereData sr $ List1 y ys
      pure (M.EFnCall defExpr [xs] a t', sr)

cvtExpr :: forall m. (MonadToMir m) => H.Expr -> m M.Expr
cvtExpr (e, t, sr) = do
  e' <- case e of
    H.ELitInt x -> pure $ M.ELoadConst $ M.CInt $ fromIntegral x
    H.ELitInt32 x -> pure $ M.ELoadConst $ M.CI32 $ fromIntegral x
    H.ELitBool x -> pure $ M.ELoadConst $ M.CBool x
    H.ELitString x -> pure $ M.ELoadConst $ M.CString x
    H.ELitFloat x -> pure $ M.ELoadConst $ M.CFloat x
    H.ELitList xs -> do
      xs' <- forM xs cvtExpr
      pure $ M.EVec xs'
    H.EVar id -> do
      pure $ M.EVar $ M.LocalVarUid $ un id
    H.EGlobal {}
      | t == unreachableType ->
          pure $ M.EUnreachable ""
    H.EWheresGet {}
      | t == unreachableType ->
          pure $ M.EUnreachable ""
    H.EGlobal fqn' _ isGenericOverEffects traits -> do
      a <- getIsAsync
      let fqn = if isGenericOverEffects then VFqn $ un fqn' <> (if a then "$async" else "$sync") else fqn'
      if null traits.mod && null traits.vDef
        then
          pure $ M.EGlobal fqn
        else do
          t' <- cvtType t

          t1 <-
            if null traits.vDef
              then pure t'
              else do
                whDataType <- mkWhereDataType $ traits.vDef <&> (<&> fst)
                pure $ M.TFunc [whDataType] t' def a
          e1 <- mkApplyWhereClausesExpr sr t1 traits.mod (M.EGlobal fqn, sr)
          e2 <- mkApplyWhereClausesExpr sr t' traits.vDef e1
          pure $ fst e2
    H.EWheresGet {traitLoc, fnIdx, nextWhereClauses} -> do
      whUid <- getWhereParamUid traitLoc.src
      let getVarExpr = (M.EVar $ must whUid, sr)
          indexed1 =
            if traitLoc.whereClausesTotal <= 1
              then
                getVarExpr
              else
                (M.EIndex getVarExpr traitLoc.whereClauseIdx Nothing, sr)
          indexed2 =
            if traitLoc.whereClauseTraitsTotal <= 1
              then
                indexed1
              else
                (M.EIndex indexed1 traitLoc.whereClauseTraitIdx Nothing, sr)
          indexed3 =
            if traitLoc.traitDefsTotal <= 1
              then
                indexed2
              else
                (M.EIndex indexed2 fnIdx Nothing, sr)
      t' <- cvtType t
      e' <- mkApplyWhereClausesExpr sr t' nextWhereClauses indexed3
      pure $ fst e'
    H.EClosure params e' -> do
      cvtClosure t params e' sr <&> fst
    H.EFnCall (H.EDataCons (H.DataConsInfo {dcIdx}), calleeType, _) args -> do
      args' <- forM args cvtExpr
      let t' = case calleeType of H.TFunc _ r _ -> r; _ -> undefined
      dataTypeDef <- getTNamedTDef2 t'
      dConssTypes <- getDataConstructorTypes dataTypeDef
      pure $ fst $ mkDataConsInit dConssTypes args' dcIdx sr
    H.EFnCall callee args -> do
      callee' <- cvtExpr callee
      args' <- forM args cvtExpr
      inAsyncCode <- getIsAsync
      retType <- cvtType t

      let eff = case snd3 callee of H.TFunc _ _ x -> x; _ -> undefined
      fnIsAsync <- effectCouldContainAsync eff
      let async = inAsyncCode && fnIsAsync /= NotAsync

      pure $ M.EFnCall callee' args' async retType
    H.EDoBlock stmts e' -> do
      ss <- concat <$> forM stmts cvtStmt
      e'' <- forM e' cvtExpr
      pure $ M.EDoBlock ss e''
    H.EIf a b c -> do
      a' <- cvtExpr a
      b' <- cvtExpr b
      c' <- cvtExpr c
      t' <- cvtType t
      pure $ M.EIf a' b' c' t'
    H.ETuple xs ->
      M.EProduct <$> forM xs cvtExpr
    H.EAnd lhs rhs -> do
      lhs' <- cvtExpr lhs
      rhs' <- cvtExpr rhs
      pure $ M.EAnd lhs' rhs'
    H.EOr lhs rhs -> do
      lhs' <- cvtExpr lhs
      rhs' <- cvtExpr rhs
      pure $ M.EOr lhs' rhs'
    H.EMatch matchExpr bs -> do
      -- Store match expression in a variable so it isn't repeated in each if expression
      uid <- mkLocalVarUid
      let scrutineeVar = (M.EVar uid, sr)
      matchExpr' <- cvtExpr matchExpr
      let letStmt = (M.SLet uid Nothing False matchExpr', snd matchExpr')

      -- The match expression is put in a labelled loop so it can break when a match is found
      lbl <- mkLocalVarUid

      -- Create a temporary mutable variable (SLet) with no initial value that holds the result
      resultUid <- mkLocalVarUid
      resultType <- cvtType t
      let resultStmt = (M.SLetUninit resultUid resultType, sr)

      let unitExpr = (M.EDoBlock [] Nothing, sr)

      -- Patterns & bodies of branches
      ifs <- forM (toList bs) $ \b -> do
        -- Body, assign to temp var, set notMatched
        bodyExpr <- cvtExpr b.expr
        let bodyExpr' =
              ( M.EDoBlock
                  [ (M.SAssign resultUid Nothing bodyExpr, sr),
                    (M.SExpr (M.EBreak lbl, sr), sr)
                  ]
                  Nothing,
                sr
              )

        -- Optional if expression for guard
        guardExpr <- forM b.guard cvtExpr

        let outerIfThen' =
              case guardExpr of
                Just x ->
                  (M.EIf x bodyExpr' unitExpr M.TUnit, sr)
                _ -> bodyExpr'

        -- Outermost if for pattern conditions
        (conds, patStmts) <- mkPatternMatchConds scrutineeVar b.pattern
        let notMatchedAndPtnConds = case conds of
              [] -> (M.ELoadConst $ M.CBool True, sr)
              _ -> foldl1 (\a' b' -> (M.EAnd a' b', sr)) conds
        let outerIfThen = (M.EDoBlock patStmts $ Just outerIfThen', sr)
        let outerIf = (M.EIf notMatchedAndPtnConds outerIfThen unitExpr M.TUnit, sr)
        pure (M.SExpr outerIf, sr)

      let noMatch = (M.SExpr (M.EUnreachable "Unhandled pattern", sr), sr)
      let resultVar = (M.EVar resultUid, sr)
      let loop = (M.SLoop (M.EDoBlock ([letStmt] <> ifs <> [noMatch]) Nothing, sr) lbl, sr)
      pure (M.EDoBlock [resultStmt, loop] (Just resultVar))
    H.EDataCons (H.DataConsInfo {fqn, dcName, dcIdx, isFn}) -> do
      if isFn
        then do
          let fqn' = VFqn $ T.concat ["_", un fqn, "_", un dcName]
          pure $ M.EGlobal fqn'
        else do
          dataTypeDef <- getTNamedTDef2 t
          dConssTypes <- getDataConstructorTypes dataTypeDef
          pure $ fst $ mkDataConsInit dConssTypes [] dcIdx sr
    H.ETry tryExpr catchClauses finallyExpr -> do
      tryExpr' <- cvtExpr tryExpr
      catchClauses' <- forM catchClauses $ \(destr, bodyExpr) -> do
        let exceptionType = snd3 destr
        let typeStr = typeToTextFull exceptionType
        uid' <- mkLocalVarUid
        bodyExpr' <- cvtExpr bodyExpr
        destructStmts <- mkDestructureStmts destr (M.EVar uid', sr)
        let expr = (M.EDoBlock destructStmts (Just bodyExpr'), sr)
        pure (typeStr, uid', thd3 destr, expr)
      finallyExpr' <- forM finallyExpr cvtExpr
      pure $ M.ETry tryExpr' catchClauses' finallyExpr'
    H.EThrow expr@(_, exType, _) -> do
      expr' <- cvtExpr expr
      pure $ M.EThrow expr' (typeToTextFull exType)
    H.EIndex expr idx -> do
      expr' <- cvtExpr expr
      pure $ M.EIndex expr' idx Nothing
    H.EFieldAccess expr@(_, fieldType, _) (fieldName, _) -> do
      expr' <- cvtExpr expr
      dataTypeDef <- getTNamedTDef2 fieldType
      let (H.DataCons _ fields) = dataTypeDef.dataCons !! 0
      let fieldIdx = case fields of
            H.TupleFields _ -> error "TupleFields in EFieldAccess"
            H.RecordFields fs -> fromMaybe (error "Field not found") $ findIndex (fst >>> (== fieldName)) $ toList fs
      pure $ M.EIndex expr' fieldIdx (Just fieldName)
    H.ERecordInit dcInfo exprs fieldExprIndices -> do
      exprUids <- forM (toList exprs) $ \expr -> do
        expr' <- cvtExpr expr
        uid <- mkLocalVarUid
        pure (uid, expr')
      dataTypeDef <- getTNamedTDef2 t
      let (H.DataCons _ fields) = toList dataTypeDef.dataCons !! dcInfo.dcIdx
      let fieldOrder = case fields of
            H.TupleFields _ -> error "TupleFields in ERecordInit"
            H.RecordFields fs -> toList fs <&> fst
      let sortedUids =
            fieldOrder <&> \field -> case lookup field $ toList fieldExprIndices of
              Just i -> fst $ exprUids !! i
              Nothing -> error "Field not found in record init"
      let varExprs = sortedUids <&> \uid -> (M.EVar uid, sr)
      dConssTypes <- getDataConstructorTypes dataTypeDef
      let recordExpr = mkDataConsInit dConssTypes varExprs dcInfo.dcIdx sr
      let letStmts = exprUids <&> \(uid, expr') -> (M.SLet uid Nothing False expr', snd expr')
      pure $ M.EDoBlock letStmts (Just recordExpr)
    H.ENewtypeAccess expr -> fst <$> cvtExpr expr
    H.EBreak lbl -> pure $ M.EBreak $ M.LocalVarUid $ un lbl
    H.EContinue lbl -> pure $ M.EContinue $ M.LocalVarUid $ un lbl
    H.EUpdate expr updateExprs updatePart -> do
      expr' <- cvtExpr expr
      updateExprs' <- forM updateExprs cvtExpr
      -- Create local variables for each expression in updateExprs', pass [EVar] into cvtUpdatePart
      updateVarUids <- forM updateExprs' $ const mkLocalVarUid
      let updateLetStmts =
            zip updateVarUids updateExprs' <&> \(uid, expr'') -> (M.SLet uid Nothing False expr'', sr)
      let updateVarExprs = updateVarUids <&> \uid -> (M.EVar uid, sr)
      updatePartExpr <- cvtUpdatePart expr' updateVarExprs updatePart
      pure $ M.EDoBlock updateLetStmts (Just updatePartExpr)
    H.EImplicitCast expr -> fst <$> cvtExpr expr
    H.ESignExtendInt expr -> do
      expr' <- cvtExpr expr
      pure $ M.ESignExtendInt expr'
    H.EIntToF64 expr -> do
      expr' <- cvtExpr expr
      pure $ M.EIntToF64 expr'
    H.ECastNumber expr -> do
      expr' <- cvtExpr expr
      toType <- cvtType t
      pure $ M.ECastNumber expr' toType
    H.ECastToTraitType expr chosenTrait -> do
      expr' <- cvtExpr expr
      let trait = case t of
            H.TNamed fqn genArgs -> (fqn, genArgs)
            _ -> undefined
      wh <- gatherTraitWhereData sr (trait, chosenTrait)
      pure $ M.EProduct $ List2 expr' wh []
  pure (e', sr)

cvtUpdatePart :: (MonadToMir m) => M.Expr -> [M.Expr] -> H.EUpdatePart -> m M.Expr
cvtUpdatePart scrutinee exprs updatePart = do
  let sr = snd scrutinee
  case updatePart of
    H.EUpdateValue i -> pure $ exprs !! i
    H.EUpdateNoChange -> pure scrutinee
    H.EUpdateTuple parts -> do
      updatedElements <- forM (zipList1 (List1 0 [1 :: Int ..]) parts) $ \(i, part) -> do
        let innerExpr = (M.EIndex scrutinee i Nothing, sr)
        case part of
          H.EUpdateValue idx -> pure $ exprs !! idx
          H.EUpdateNoChange -> pure innerExpr
          _ -> cvtUpdatePart innerExpr exprs part
      case listToList2 $ toList updatedElements of
        Nothing -> pure $ updatedElements !! 0 -- Newtype
        Just es -> pure (M.EProduct es, sr)
    H.EUpdateRecord dcInfo parts -> do
      let partsList = toList parts
      updatedFields <- forM (zip [0 :: Int ..] partsList) $ \(i, (fieldName, part)) -> do
        let innerExpr = (M.EIndex scrutinee i (Just fieldName), sr)
        case part of
          H.EUpdateValue idx -> pure $ exprs !! idx
          H.EUpdateNoChange -> pure innerExpr
          _ -> cvtUpdatePart innerExpr exprs part
      pure $ mkDataConsInit [] updatedFields dcInfo.dcIdx sr

-- Returns (conditions, destructure statements)
mkPatternMatchConds :: (MonadToMir m) => M.Expr -> H.Pattern -> m ([M.Expr], [M.Stmt])
mkPatternMatchConds scrutinee (ptn, _, sr) = case ptn of
  H.PIgnore ->
    pure ([], [])
  H.PName name uid -> do
    pure ([], [(M.SLet (M.LocalVarUid $ un uid) (Just (un name, sr)) False scrutinee, sr)])
  H.PTuple ps -> do
    condsStmts <- forM (zip [0 :: Int ..] (toList ps)) $ \(i, p) -> do
      let idxExpr = (M.EIndex scrutinee i Nothing, sr)
      mkPatternMatchConds idxExpr p
    let (conds, stmts) = unzip condsStmts
    pure (concat conds, concat stmts)
  H.PDataCons dcInfo ps ->
    mkDataConsPatternMatch scrutinee dcInfo ((Nothing,) <$> toList ps) sr
  H.PRecord dcInfo ps ->
    mkDataConsPatternMatch scrutinee dcInfo (first Just <$> ps) sr

-- Helper for pattern matching on data constructors and records
-- The Maybe VName is the debugging info for record accessors
mkDataConsPatternMatch ::
  (MonadToMir m) => M.Expr -> H.DataConsInfo -> [(Maybe VName, H.Pattern)] -> SrcRange -> m ([M.Expr], [M.Stmt])
mkDataConsPatternMatch scrutinee dcInfo fieldPatterns sr = do
  if dcInfo.isProduct
    then do
      condsStmts <- forM (zip [0 :: Int ..] fieldPatterns) $ \(i, (mName, p)) -> do
        let idxExpr = (M.EIndex scrutinee i mName, sr)
        mkPatternMatchConds idxExpr p
      let (conds, stmts) = unzip condsStmts
      pure (concat conds, concat stmts)
    else do
      let isEnum = dcInfo.isEnum

      -- Check tag
      let tagExpr = if isEnum then scrutinee else (M.ESumTypeActiveIndex scrutinee, sr)
      let tagCondition =
            (,sr)
              $ M.EFnCall
                (M.EGlobal (VFqn "#builtins/:I32Builtins.eq"), sr)
                [tagExpr, (M.ELoadConst $ M.CI32 (fromIntegral dcInfo.dcIdx), sr)]
                False
                M.TBool

      -- Get payload
      let payloadExpr = (M.ESumTypeGet scrutinee, sr)

      -- Check fields
      condsStmts <- forM (zip [0 :: Int ..] fieldPatterns) $ \(i, (mName, p)) -> do
        let fieldExpr = if length fieldPatterns == 1 then payloadExpr else (M.EIndex payloadExpr i mName, sr)
        mkPatternMatchConds fieldExpr p
      let (fieldConds, fieldStmts) = unzip condsStmts
      pure (tagCondition : concat fieldConds, concat fieldStmts)

cvtStmt :: (MonadToMir m) => H.Stmt -> m [M.Stmt]
cvtStmt (stmt, sr) = case stmt of
  H.SLet d expr -> do
    expr' <- cvtExpr expr
    uid <- mkLocalVarUid
    let letStmt = (M.SLet uid Nothing False expr', sr)
    destrStmts <- mkDestructureStmts d (M.EVar uid, sr)
    pure $ letStmt : destrStmts
  H.SRecLet name hirUid (expr, t, _) -> do
    case expr of
      H.EClosure params e' -> do
        let uid' = M.LocalVarUid $ un hirUid
        expr' <- cvtClosure t params e' sr
        pure [(M.SRecLet uid' (Just $ first un name) expr', sr)]
      _ -> undefined
  H.SExpr expr -> do
    expr' <- cvtExpr expr
    pure [(M.SExpr expr', sr)]
  H.SWhen condExpr expr -> do
    cond' <- cvtExpr condExpr
    body' <- cvtExpr expr
    let elseExpr = (M.EDoBlock [] Nothing, sr) -- Empty block for else branch
    pure [(M.SExpr (M.EIf cond' body' elseExpr M.TUnit, sr), sr)]
  H.SAssign hirUid name expr -> do
    expr' <- cvtExpr expr
    let uid' = M.LocalVarUid (un hirUid)
    pure [(M.SAssign uid' (Just $ first un name) expr', sr)]
  H.SLoop expr lbl -> do
    expr' <- cvtExpr expr
    pure [(M.SLoop expr' (M.LocalVarUid $ un lbl), sr)]
  H.SForEach {destr, inExpr, bodyExpr, label} -> do
    -- Create temporary mutable variable for the iterator
    uid' <- mkLocalVarUid
    let iteratorVar = (M.EVar uid', sr)

    -- Convert the iterator expression
    inExpr' <- cvtExpr inExpr

    -- Create initial assignment: mutable temporary = iterator expression
    let initStmt = (M.SLet uid' Nothing True inExpr', sr)

    -- Create the loop body: an EDoBlock that:
    -- 1. Checks if iterator is at end (tag 0 = end) and breaks if so
    -- 2. Otherwise, gets the payload (tag 1 = (value, lazy-next))
    -- 3. Destructures the value
    -- 4. Runs the body expression
    -- 5. Updates iterator = lazy-next()

    -- Check if iterator is at end (tag 0)
    let tagExpr = (M.ESumTypeActiveIndex iteratorVar, sr)
    let endCondition =
          (,sr)
            $ M.EFnCall
              (M.EGlobal (VFqn "#builtins/:IntBuiltins.eq"), sr)
              [tagExpr, (M.ELoadConst $ M.CInt 0, sr)]
              False
              M.TBool

    -- Create break statement if at end
    let lbl = M.LocalVarUid $ un label
    let breakStmt = (M.SExpr (M.EIf endCondition (M.EBreak lbl, sr) (M.EDoBlock [] Nothing, sr) M.TUnit, sr), sr)

    -- Get payload
    let payloadExpr = (M.ESumTypeGet iteratorVar, sr)

    -- Destructure the value (first element of payload)
    destructureStmts <- mkDestructureStmts destr (M.EIndex payloadExpr 0 Nothing, sr)

    -- Convert body expression
    bodyExpr' <- cvtExpr bodyExpr
    let bodyStmt = (M.SExpr bodyExpr', sr)

    -- Get next iterator (second element of payload)
    let nextIterClosure = (M.EIndex payloadExpr 1 Nothing, sr)

    -- Call next-iter function
    foreachVarType <- cvtType $ snd3 destr
    let evalExpr = (M.EFnCall nextIterClosure [] False foreachVarType, sr)

    -- Update the iterator variable with the result of eval
    let updateStmt = (M.SAssign uid' Nothing evalExpr, sr)

    -- Build the loop body as an EDoBlock
    let loopBody = (M.EDoBlock (breakStmt : destructureStmts <> [bodyStmt, updateStmt]) Nothing, sr)

    -- Create the SLoop statement
    let loopStmt = (M.SLoop loopBody lbl, sr)

    pure [initStmt, loopStmt]

getTNamedTDef2 :: (MonadToMir m, HasCallStack) => H.Type -> m H.DataTypeDef
getTNamedTDef2 (H.TNamed fqn _) = do
  let pkg = tFqnToPkg fqn
  pkg' <- getPkg pkg
  getDataTypeDef pkg' fqn
getTNamedTDef2 t = error $ "getTNamedTDef2 not TNamed: " <> show t

effectCouldContainAsync :: (MonadToMir m) => H.Type -> m IsAsync
effectCouldContainAsync (H.TNamed (TFqn "#builtins/:AsyncEffect") _) = pure IsAsync
effectCouldContainAsync (H.TNamed fqn _) = do
  let pkg = tFqnToPkg fqn
  tDef <- getPkg pkg >>= \pkg' -> getTDef pkg' fqn
  if tDef.tDefType == H.IsGenParam then pure MaybeAsync else pure NotAsync
effectCouldContainAsync (H.TEffect es) = forM (toList es) effectCouldContainAsync <&> mconcat
effectCouldContainAsync _ = pure NotAsync

cvtType :: forall m. (MonadToMir m) => H.Type -> m M.Type
cvtType t'' = do
  -- Returns list of recursive data types (subset of seen)
  let cvtType' :: [TFqn] -> H.Type -> m (M.Type, [TFqn])
      cvtType' seen t = case t of
        H.TFunc {params, ret, eff} -> do
          ps' <- forM params $ cvtType' seen
          let ps = fst <$> ps'
          let recTypes1 = concatMap snd ps'
          (r, recTypes2) <- cvtType' seen ret
          let efs = findEffs eff
          couldBeAsync <- effectCouldContainAsync eff
          inAsyncCode <- getIsAsync
          let async = case couldBeAsync of
                NotAsync -> False
                MaybeAsync -> inAsyncCode
                IsAsync -> True
          pure (M.TFunc ps r efs async, recTypes1 <> recTypes2)
        H.TTuple xs -> do
          xs' <- forM xs $ cvtType' seen
          pure (M.TProduct $ fst <$> xs', concatMap snd $ toList xs')
        H.TNamed fqn genArgs -> do
          let pkgName = tFqnToPkg fqn
          if fqn `elem` seen
            then do
              pure (M.TAny, [fqn])
            else do
              pkg <- getPkg pkgName
              tDef <- getTDef pkg fqn
              case tDef.tDefType of
                H.IsAlias -> undefined -- Aliases don't get represented as TNamed
                H.IsGenParam ->
                  pure (M.TAny, [])
                H.IsBuiltin ->
                  (,[]) <$> case T.drop (T.length "#builtins/:") (un fqn) of
                    "Int" -> pure M.TInt
                    "I32" -> pure M.TI32
                    "Real" -> pure M.TReal
                    "Unit" -> pure M.TUnit
                    "Unreachable" -> pure M.TUnit
                    "String" -> pure M.TString
                    "Bool" -> pure M.TBool
                    "Any" -> pure M.TAny
                    "Lazy" -> forM genArgs cvtType <&> M.TVec . (!! 0)
                    "Vec" -> forM genArgs cvtType <&> M.TVec . (!! 0)
                    _ -> error "Unknown builtin"
                H.IsDataDef -> do
                  dataTypeDef <- getDataTypeDef pkg fqn
                  let convertDCons fields = do
                        let fields' = case fields of
                              H.TupleFields xs -> xs
                              H.RecordFields xs -> snd <$> toList xs
                        fs <- forM fields' (cvtType' (fqn : seen))
                        let fs' = case fst <$> fs of
                              [] -> M.TUnit
                              [t'] -> t'
                              (t0 : t1 : ts) -> M.TProduct $ List2 t0 t1 ts
                        pure (fs', concatMap snd fs)
                  case dataTypeDef.dataCons of
                    List1 (H.DataCons _ fields) [] -> do
                      dcs'' <- convertDCons fields
                      pure $ first (if fqn `elem` snd dcs'' then M.TRecursive else identity) dcs''
                    List1 dc0 (dc1 : dcs') -> do
                      let dcs = List2 dc0 dc1 dcs'
                      dcs'' <- forM dcs $ \(H.DataCons _ fields) -> convertDCons fields
                      let recs = concatMap snd dcs''
                      let sumType = M.TSum $ fst <$> dcs''
                      pure ((if fqn `elem` recs then M.TRecursive else identity) sumType, recs)
                H.IsTrait' -> do
                  traitType <- mkTraitType fqn
                  pure (M.TProduct $ List2 M.TAny traitType [], [])
        H.TEffect _ -> error "Abstract type"
        H.TLifetime _ -> error "Abstract type"
  fst <$> cvtType' [] t''

mkTraitType :: (MonadToMir m) => TFqn -> m M.Type
mkTraitType fqn = do
  trait <- getTrait fqn
  ts <- forM trait.vDefs $ \vDef -> do
    t <- cvtType vDef.vDef.type'
    if null $ un vDef.vDef.whereClauses
      then
        pure t
      else do
        wh <- mkWhereDataType $ un vDef.vDef.whereClauses <&> snd
        pure $ M.TFunc [wh] t (M.Effects True True) False
  pure $ case ts of
    [] -> M.TUnit
    [x] -> x
    x : y : zs -> M.TProduct $ List2 x y zs

mkProductIfMany :: List1 M.Type -> M.Type
mkProductIfMany xs = case xs of
  List1 x [] -> x
  List1 x (y : zs) -> M.TProduct $ List2 x y zs

mkWhereDataType :: (MonadToMir m) => [List1 H.TraitRef] -> m M.Type
mkWhereDataType wh = do
  let go traitRefs = do
        xs <- forM traitRefs $ \(fqn, _) -> mkTraitType fqn
        pure $ mkProductIfMany xs
  case wh of
    [] -> undefined
    [x] -> go x
    (x : xs) -> do
      ys <- forM (List1 x xs) go
      pure $ mkProductIfMany ys

type ToMirM = ReaderT State IO

data State = State
  { pkgs :: HashMap PkgName H.Hir,
    thisPkgName :: PkgName,
    thisPkg :: H.Hir,
    mir :: M.Mir,
    nextTmpId :: IORef Int,
    whereParamUidBlk :: IORef (Maybe M.LocalVarUid),
    whereParamUidVDef :: IORef (Maybe M.LocalVarUid),
    isAsync :: IORef Bool,
    vFqn :: IORef (Maybe VFqn)
  }

instance MonadVars ToMirM where
  type Var ToMirM = IORef
  newVar = liftIO . newIORef
  setVar v x = liftIO $ writeIORef v x
  getVar v = liftIO $ readIORef v
  modVar v f = liftIO $ modifyIORef' v f

instance MonadToMir ToMirM where
  type Pkg ToMirM = H.Hir
  getThisPkg = do
    thisPkgName <- asks (.thisPkgName)
    thisPkg <- asks (.thisPkg)
    pure (thisPkgName, thisPkg)
  getPkg name = do
    x <- asks (.pkgs)
    pure $ must $ HM.lookup name x
  getVDefs pkg = liftIO $ HT.toList pkg.vDefs
  getVDefValue pkg fqn = liftIO $ HT.lookup pkg.vDefExpr fqn
  getDataTypeDefs pkg = liftIO $ HT.toList pkg.dataTypeDefs
  addVDef fqn v = do
    vDefs <- asks (.mir.vDefs)
    liftIO $ HT.insert vDefs fqn v
  getVDef hir fqn =
    liftIO $ HT.lookup hir.vDefs fqn <&> must
  getTDef hir fqn =
    liftIO $ HT.lookup hir.tDefs1 fqn <&> must
  getDataTypeDef hir fqn =
    liftIO $ HT.lookup hir.dataTypeDefs fqn <&> must
  getTypeExport fqn = do
    hir <- getPkg $ tFqnToPkg fqn
    (_, x, _) <- liftIO $ HT.lookup hir.exports (tFqnToNamespace fqn) <&> must
    liftIO $ HT.lookup x (tFqnToName fqn) <&> must
  getModule fqn = do
    getTypeExport fqn <&> ((.typ) >>> \case H.IsModule b -> b; _ -> undefined)
  getTrait fqn = do
    getTypeExport fqn <&> ((.typ) >>> \case H.IsTrait t -> t; _ -> undefined)
  getIsAsync = do
    ref <- asks (.isAsync)
    liftIO $ readIORef ref
  setIsAsync is = do
    ref <- asks (.isAsync)
    liftIO $ writeIORef ref is
  resetFnState = do
    setIsAsync False
    ref <- asks (.nextTmpId)
    liftIO $ writeIORef ref 0
  mkLocalVarUid = do
    ref <- asks (.nextTmpId)
    i <- liftIO $ readIORef ref
    liftIO $ writeIORef ref (i + 1)
    pure $ M.LocalVarUid i
  getNextVarUid = do
    ref <- asks (.nextTmpId)
    liftIO $ readIORef ref
  setNextVarUid i = do
    ref <- asks (.nextTmpId)
    liftIO $ writeIORef ref i
  generateWhereParamUid src = do
    uid <- mkLocalVarUid
    ref <- asks $ case src of H.FromBlockWheres -> (.whereParamUidBlk); H.FromVDefWheres -> (.whereParamUidVDef)
    liftIO $ writeIORef ref $ Just uid
    pure uid
  getWhereParamUid src = do
    ref <- asks $ case src of H.FromBlockWheres -> (.whereParamUidBlk); H.FromVDefWheres -> (.whereParamUidVDef)
    liftIO $ readIORef ref
  setVFqn fqn = do
    x <- asks (.vFqn)
    liftIO $ writeIORef x $ Just fqn
  getVFqn = do
    x <- asks (.vFqn)
    liftIO $ readIORef x <&> must
