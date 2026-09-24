-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{- HLINT ignore "Use maybe" -}

module Front.Tc.Expr where

import Control.Monad (forM, forM_, unless, when)
import Data.Either (isLeft)
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.List (findIndex)
import Data.Maybe (catMaybes, fromMaybe, isNothing, mapMaybe)
import Data.Text qualified as T
import Error (ErrorSeverity (SevWarning))
import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.HirFns (isGenericOverEffect, typeContainsFqn, typeContainsFqnMatch, typeToText)
import Front.Tc.Context
import Front.Tc.Error (MonadTcError (addError, throw))
import Front.Tc.Generics
import Front.Tc.Names
import Front.Tc.PType
import Front.Tc.Patterns
import Front.Tc.State
import Front.Tc.Traits
import Front.Tc.Types
import Front.Tc.VDef
import Front.TypeKind (TypeKind (MonoType))
import GHC.Stack (HasCallStack)
import MhPrelude
import Names
import SrcLoc (SrcRange, srcRangeOf)
import Vars

-- It is safe to use these TNamed values without calling the visit type def function as the builtins package has already
-- been type checked as #builtins does not contain any expressions + type definitions are visited before expressions

anyType :: H.Type
anyType = H.TNamed (TFqn "#builtins/:Any") []

boolHint :: PType
boolHint = TNamedP (TFqn "#builtins/:Bool") []

boolType :: H.Type
boolType = H.TNamed (TFqn "#builtins/:Bool") []

unitHint :: PType
unitHint = TNamedP (TFqn "#builtins/:Unit") []

unitType :: H.Type
unitType = H.TNamed (TFqn "#builtins/:Unit") []

unreachableType :: H.Type
unreachableType = H.TNamed (TFqn "#builtins/:Unreachable") []

intType :: H.Type
intType = H.TNamed (TFqn "#builtins/:Int") []

i32Type :: H.Type
i32Type = H.TNamed (TFqn "#builtins/:I32") []

stringType :: H.Type
stringType = H.TNamed (TFqn "#builtins/:String") []

realType :: H.Type
realType = H.TNamed (TFqn "#builtins/:Real") []

-- Changes to this type signature must be mirrored in Expr.hs-boot
visitExpr :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitExpr ctx typeHint e = do
  case fst e of
    A.ELitInt {} -> visitELitInt ctx typeHint e
    A.ELitFloat {} -> visitELitFloat ctx typeHint e
    A.ELitBool {} -> visitELitBool ctx typeHint e
    A.ELitString {} -> visitELitString ctx typeHint e
    A.ELitList {} -> visitELitList ctx typeHint e
    A.EVar {} -> visitEVar ctx typeHint e
    A.EClosure {} -> visitEClosure ctx typeHint e
    A.EFnCall {} -> visitEFnCall ctx typeHint e
    A.EDoBlock {} -> visitEDoBlock ctx typeHint e
    A.EIf {} -> visitEIf ctx typeHint e
    A.ETuple {} -> visitETuple ctx typeHint e
    A.EAnd {} -> visitEAnd ctx typeHint e
    A.EOr {} -> visitEOr ctx typeHint e
    A.EMatch {} -> visitEMatch ctx typeHint e
    A.EDataCons {} -> visitEDataCons ctx typeHint e
    A.EMemberCall {} -> visitEMemberCall ctx typeHint e
    A.ETry {} -> visitETry ctx typeHint e
    A.EThrow {} -> visitEThrow ctx typeHint e
    A.EYield {} -> visitEYield ctx typeHint e
    A.EIndex {} -> visitEIndex ctx typeHint e
    A.EFieldAccess {} -> visitEFieldAccess ctx typeHint e
    A.ERecordInit {} -> visitERecordInit ctx typeHint e
    A.EBreak {} -> visitEBreak ctx typeHint e
    A.EContinue {} -> visitEContinue ctx typeHint e
    A.EUpdate {} -> visitEUpdate ctx typeHint e
    A.EExplicitType {} -> visitEExplicitType ctx typeHint e
    A.EAs {} -> visitEAs ctx typeHint e

visitELitInt :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitELitInt _ typeHint (theExpr, sr) = case theExpr of
  A.ELitInt i -> do
    case typeHint of
      TNamedP (TFqn "#builtins/:I32") _
        | i >= -2147483648 && i <= 2147483647 ->
            pure (H.ELitInt32 $ fromIntegral i, i32Type, sr)
      TNamedP (TFqn "#builtins/:Real") _
        | i >= -9007199254740992 && i <= 9007199254740992 ->
            pure (H.ELitFloat $ tShow i, realType, sr)
      _ ->
        pure (H.ELitInt i, intType, sr)
  _ -> undefined

visitELitFloat :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitELitFloat _ _ (theExpr, sr) = case theExpr of
  A.ELitFloat f ->
    pure (H.ELitFloat f, realType, sr)
  _ -> undefined

visitELitBool :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitELitBool _ _ (theExpr, sr) = case theExpr of
  A.ELitBool b ->
    pure (H.ELitBool b, boolType, sr)
  _ -> undefined

visitELitString :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitELitString _ _ (theExpr, sr) = case theExpr of
  A.ELitString s ->
    pure (H.ELitString s, stringType, sr)
  _ -> undefined

visitELitList :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitELitList ctx typeHint (theExpr, sr) = case theExpr of
  A.ELitList es -> do
    case head es of
      Just e0 -> do
        let e0Hint = case typeHint of
              TNamedP (TFqn "#builtins/:Vec") [t] -> t
              _ -> TUnknown
        e0'@(_, t, _) <- visitExpr ctx e0Hint e0
        let hint = typeToPType t
        tail' <- forM (tail es) $ \e -> do
          e' <- visitExpr ctx hint e
          e'' <- implicitCast ctx e' t
          pure e''

        let t' = H.TNamed (TFqn "#builtins/:Vec") [t]
        pure (H.ELitList $ e0' : tail', t', sr)
      _ -> do
        t <- case pTypeToType typeHint of
          Just x@(H.TNamed (TFqn "#builtins/:Vec") [_]) -> pure x
          _ -> throw sr "Unable to deduce type of empty list"

        pure (H.ELitList [], t, sr)
  _ -> undefined

-- Called when a local variable is referenced in the handling of A.EVar
-- This function exists because EFnCall handles EVar itself
usedLocalVar :: (MonadTc m) => Ctx -> Variable -> SrcRange -> m (H.Expr', H.Type, SrcRange)
usedLocalVar ctx var sr = do
  when (var.closureDepth /= ctx.closureDepth) $ addCapture var.uid

  when (var.isMutable && var.closureDepth < ctx.closureDepth) $ do
    let l = H.TLifetime var.closureDepth var.scopeDepth
    addEffect $ H.TNamed (TFqn "#builtins/:MutVarEff") [l]

  pure (H.EVar var.uid (un $ fst var.name), var.typ, sr)

visitEVar :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEVar ctx typeHint (theExpr, sr) = case theExpr of
  A.EVar qualMaybe name genArgs -> do
    let findGlobal = do
          (fqn, vDef) <- lookupGlobalVDef ctx qualMaybe name sr

          (t, ts, whs) <- case genArgs of
            [] -> do
              let gps = vDef.genParams <&> (.fqn)
              gpTypes <- inferGenericArgs [] vDef.genParams typeHint vDef.type' sr
              let t = substituteGenerics (zip gps gpTypes) vDef.type'
              let gpMap = zip vDef.genParams gpTypes <&> \(gp, a) -> (gp.fqn, a)
              whs <- findTraitImpls ctx gpMap vDef.whereClauses sr
              pure (t, def, whs)
            _ -> do
              unless (length genArgs == length vDef.genParams) $ throw sr "Wrong number of generic arguments"
              genArgs' <- forM genArgs $ visitTypeExpr ctx
              checkGenArgKinds $ zip vDef.genParams $ zip genArgs' $ snd <$> genArgs
              let gpMap = zip vDef.genParams genArgs' <&> \(gp, a) -> (gp.fqn, a)
              whs <- findTraitImpls ctx gpMap vDef.whereClauses sr
              let t = substituteGenerics gpMap vDef.type'
              pure (t, genArgs', whs)
          let whs' = H.WhereClauseTraits {mod = [], vDef = whs}
          pure (H.EGlobal fqn ts (isGenericOverEffect vDef.genParams) whs', t, sr)

    case qualMaybe of
      Just _ -> findGlobal
      _ -> case findLocalVarByName ctx name of
        Just var -> do
          unless (null genArgs) $ throw sr "Local variables cannot be generic"
          usedLocalVar ctx var sr
        _ -> findGlobal
  _ -> undefined

visitEClosure :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEClosure outerCtx typeHint (theExpr, sr) = case theExpr of
  A.EClosure params astExpr -> do
    let closureDepth = H.ClosureDepth $ un outerCtx.closureDepth + 1
    -- inLoop is to disambiguate the record update :/
    let ctx = outerCtx {closureDepth, inLoop = outerCtx.inLoop}

    explicitParamTypes <- forM params $ \(_, t) -> forM t $ visitTypeExpr ctx

    let (paramsTypesHints, retTypeHint) = case typeHint of
          TFuncP ps r _ef ->
            (ps <> replicate (max 0 $ length params - length ps) TUnknown, r)
          _ -> (replicate (length params) TUnknown, TUnknown)

    paramsTypes <- forM (zip3 params explicitParamTypes paramsTypesHints) $ \(((_, sr'), _), t, h) -> case t of
      Just t' -> pure t'
      _ -> case pTypeToType h of
        Just t' -> pure t'
        _ -> throw sr' "Unable to infer closure parameter type"

    outerCloEffs <- getEffects
    outerCloCaps <- getCaptures
    outerCloDecls <- getLocalDecls
    setEffects def
    setCaptures def
    setLocalDecls def

    ctxVar <- newVar ctx
    params' <- forM (zip params paramsTypes) $ \((d, _), t) -> visitDestructure ctxVar t d
    ctx' <- getVar ctxVar
    e@(_, retType, _) <- visitExpr ctx' retTypeHint astExpr <&> (`implicitCastHint` retTypeHint)

    thisCloEffs <- getEffects
    caps <- getCaptures
    decls <- getLocalDecls

    setEffects outerCloEffs
    setCaptures $ outerCloCaps <> (caps `HS.difference` decls)
    setLocalDecls outerCloDecls

    assertM $ flip all thisCloEffs $ \case H.TNamed {} -> True; _ -> False
    let efType = H.TEffect thisCloEffs
    let fnType = H.TFunc paramsTypes retType efType

    pure (H.EClosure params' e caps, fnType, sr)
  _ -> undefined

visitEFnCall :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEFnCall ctx typeHint (theExpr, sr) = case theExpr of
  A.EFnCall astCalleeExpr astArgsExprs -> do
    calleeExprOrHint <- case fst astCalleeExpr of
      A.EVar qualMaybe name [] -> do
        let findGlobal = do
              (fqn, vDef) <- lookupGlobalVDef ctx qualMaybe name sr

              let gp = vDef.genParams
              if null gp
                then pure $ Left (H.EGlobal fqn [] False def, vDef.type', sr)
                else do
                  let paramHints = replicate (length astArgsExprs) TUnknown
                  gpHints <- inferGenericArgsHints [] vDef.genParams (TFuncP paramHints typeHint TUnknown) vDef.type' sr
                  let gps' = vDef.genParams <&> (.fqn)
                  pure $ Right $ genericTypeToPType (zip gps' gpHints) vDef.type'

        case qualMaybe of
          Just _ -> findGlobal
          _ -> case findLocalVarByName ctx name of
            Just var -> do
              Left <$> usedLocalVar ctx var sr
            _ -> findGlobal
      A.EDataCons qualMaybe name [] ->
        getDataCons' ctx typeHint qualMaybe name $ \fqn dataTypeDef -> do
          (H.DataCons _ dcContents, dcIdx) <- findDConsInType name dataTypeDef
          genericType <- case dcContents of
            H.TupleFields xs | notNull xs -> pure $ H.TFunc xs dataTypeDef.t1.selfType (H.TEffect def)
            _ -> throw sr "data constructor is not callable"
          let dcInfo =
                H.DataConsInfo
                  { fqn,
                    dcName = fst name,
                    dcIdx,
                    isFn = True,
                    isProduct = length dataTypeDef.dataCons == 1,
                    isEnum = dataTypeDef.isEnumType
                  }
          if null dataTypeDef.t1.genParams
            then
              pure $ Left (H.EDataCons dcInfo, genericType, sr)
            else do
              let gps = dataTypeDef.t1.genParams
              let gps' = gps <&> (.fqn)
              let paramHints = replicate (length astArgsExprs) TUnknown
              let h = TFuncP paramHints typeHint TUnknown
              gpHints <- inferGenericArgsHints [] gps h genericType sr
              pure $ Right $ genericTypeToPType (zip gps' gpHints) genericType
      _ -> do
        let hint = TFuncP (replicate (length astArgsExprs) TUnknown) typeHint TUnknown
        Left <$> visitExpr ctx hint astCalleeExpr

    case calleeExprOrHint of
      Left (_, H.TFunc ps _ _, _) ->
        unless (length ps == length astArgsExprs) $ throw sr "Wrong number of arguments to function"
      -- Will be checked later
      _ -> pure ()

    let paramsHints =
          let x = case calleeExprOrHint of
                Left (_, H.TFunc ps _ _, _) -> typeToPType <$> ps
                Right (TFuncP ps _ _) -> ps
                _ -> []
           in x <> replicate (max 0 $ length astArgsExprs - length x) TUnknown

    argsExprs <- forM (zip astArgsExprs paramsHints) $ \(e, h) -> visitExpr ctx h e

    calleeExpr <- case calleeExprOrHint of
      Left e -> pure e
      Right _ -> do
        let paramsHints' = argsExprs <&> (snd3 >>> typeToPType)
        visitExpr ctx (TFuncP paramsHints' typeHint TUnknown) astCalleeExpr

    (argsExprs', retType, fnEffs) <- case snd3 calleeExpr of
      H.TFunc ps r ef -> do
        unless (length ps == length astArgsExprs) $ throw sr "Wrong number of arguments to function"
        as <- forM (zip ps argsExprs) $ \(ex, argExpr) ->
          implicitCast ctx argExpr ex
        pure (as, r, case ef of H.TEffect x -> x; _ -> undefined)
      _ -> throw astCalleeExpr "Type is not a function"

    do
      efs <- getEffects <&> (<> fnEffs)
      assertM $ flip all efs $ \case H.TNamed {} -> True; _ -> False
      setEffects $ flip filter efs $ \case
        H.TNamed (TFqn "#builtins/:MutVarEff") [H.TLifetime closureDepth scopeDepth] ->
          assert
            (scopeDepth <= ctx.scopeDepth && closureDepth <= ctx.closureDepth)
            (closureDepth < ctx.closureDepth)
        _ -> True

    pure (H.EFnCall (H.CalleeExpr calleeExpr) argsExprs', retType, sr)
  _ -> undefined

visitEDoBlock :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEDoBlock ctx typeHint (theExpr, sr) = case theExpr of
  A.EDoBlock ss eMaybe -> do
    let thisScopeDepth = H.ScopeDepth $ un ctx.scopeDepth + 1
    ctxVar <- newVar $ ctx {scopeDepth = thisScopeDepth, inLoop = ctx.inLoop}
    ss' <- forM ss $ \s -> do
      visitStmt ctxVar TUnknown s
    ctx' <- getVar ctxVar
    e <- forM eMaybe $ visitExpr ctx' typeHint
    let doBlkType = case e of
          Just (_, t', _) -> t'
          _ -> unitType

    let hasMutEff t =
          let isMutEff = \case
                H.TNamed (TFqn "#builtins/:MutVarEff") [H.TLifetime _ l] | l >= thisScopeDepth -> True
                _ -> False
           in case t of
                H.TFunc {ret, eff = H.TEffect effs} -> hasMutEff ret || any isMutEff effs
                H.TFunc {} -> undefined
                H.TTuple xs -> any hasMutEff xs
                H.TNamed _ gps -> any hasMutEff gps
                H.TEffect effs -> any isMutEff effs
                H.TLifetime {} -> False

    when (hasMutEff doBlkType) $ throw (maybe sr snd eMaybe) "Reference outlives mutable local variable"

    pure (H.EDoBlock ss' e, doBlkType, sr)
  _ -> undefined

visitEIf :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEIf ctx typeHint (theExpr, sr) = case theExpr of
  A.EIf astCondExpr astThenExpr astElseExpr -> do
    condExpr@(_, shouldBeBool, _) <- visitExpr ctx boolHint astCondExpr
    unless (shouldBeBool == boolType)
      $ throw astCondExpr
      $ "Condition type must be Bool, got "
      <> typeToText shouldBeBool
    thenExpr@(_, t0, _) <- visitExpr ctx typeHint astThenExpr
    elseExpr@(_, t1, _) <- visitExpr ctx typeHint astElseExpr
    let t = if t0 == unreachableType then t1 else t0
    thenExpr'@(_, t0', _) <- implicitCast ctx thenExpr t
    elseExpr'@(_, t1', _) <- implicitCast ctx elseExpr t

    unless (t0' == t1')
      $ throw
        sr
        ("If-else branch types do not match\nGot " <> typeToText t0 <> " and " <> typeToText t1)
    pure (H.EIf condExpr thenExpr' elseExpr', t, sr)
  _ -> undefined

visitETuple :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitETuple ctx typeHint (theExpr, sr) = case theExpr of
  A.ETuple es -> do
    let hints = case typeHint of
          TTupleP xs -> xs
          _ -> List2 TUnknown TUnknown $ replicate (length es - 2) TUnknown
    es' <- forM (zipList2 es hints) $ \(e, h) -> visitExpr ctx h e
    let t = H.TTuple $ (snd3) <$> es'
    let e = H.ETuple $ es'
    pure (e, t, sr)
  _ -> undefined

visitEAnd :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEAnd ctx _ (theExpr, sr) = case theExpr of
  A.EAnd lhs rhs -> do
    lhs' <- visitExpr ctx boolHint lhs
    lhs'' <- implicitCast ctx lhs' boolType
    rhs' <- visitExpr ctx boolHint rhs
    rhs'' <- implicitCast ctx rhs' boolType

    pure (H.EAnd lhs'' rhs'', boolType, sr)
  _ -> undefined

visitEOr :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEOr ctx _ (theExpr, sr) = case theExpr of
  A.EOr lhs rhs -> do
    lhs' <- visitExpr ctx boolHint lhs
    lhs'' <- implicitCast ctx lhs' boolType
    rhs' <- visitExpr ctx boolHint rhs
    rhs'' <- implicitCast ctx rhs' boolType

    pure (H.EOr lhs'' rhs'', boolType, sr)
  _ -> undefined

visitEMatch :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEMatch ctx typeHint (theExpr, sr) = case theExpr of
  A.EMatch caseExpr bs -> do
    caseExpr'@(_, exprType, _) <- visitExpr ctx TUnknown caseExpr
    -- TODO Ensure branch patterns are complete
    finalType <- newVar Nothing
    bs' <- forM bs $ \b -> do
      ctxVar <- newVar ctx
      p' <- visitPattern ctxVar exprType b.pattern
      ctx' <- getVar ctxVar
      guard <- forM b.guard $ visitExpr ctx' boolHint
      tMaybe <- getVar finalType
      let hint = case tMaybe of Just x -> typeToPType x; _ -> typeHint
      e'@(_, t, _) <- visitExpr ctx' hint b.expr
      e'' <- case tMaybe of
        Just ex'' -> do
          implicitCast ctx' e' ex''
        _ -> do
          unless (t == unreachableType) $ setVar finalType $ Just t
          pure e'
      pure (H.MatchBranch p' guard e'')

    t <- getVar finalType <&> fromMaybe unreachableType
    pure (H.EMatch caseExpr' bs', t, sr)
  _ -> undefined

visitEDataCons :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEDataCons ctx typeHint (theExpr, sr) = case theExpr of
  A.EDataCons qualMaybe name genArgs -> do
    e <- do
      (dcInfo, dataType, dcFieldTypes') <- getDataCons ctx typeHint qualMaybe name genArgs
      case dcFieldTypes' of
        H.TupleFields [] -> pure (H.EDataCons dcInfo, dataType, sr)
        H.TupleFields dcFieldTypes -> do
          let e = H.EDataCons dcInfo
          let t = H.TFunc dcFieldTypes dataType (H.TEffect def)
          pure (e, t, sr)
        H.RecordFields _ -> throw sr "Record data constructors cannot be used as function values"
    pure e
  _ -> undefined

data VisitMembCallLookupResult = VisitMembCallLookupResult
  { fqn :: VFqn,
    vDefType :: H.Type,
    vDefGenParams :: [H.GenParam],
    modParams :: [H.GenParam],
    modArgs :: [H.Type],
    modWhs :: H.WhereClauseTraitsList,
    vDefWhereClauses :: H.WhereClauses,
    whereClauseIdxMaybe :: Maybe H.WhereTraitLoc,
    fnIdx :: Int,
    fromTraitTypeMaybe :: Maybe (H.Trait, H.TraitVDef)
  }

visitEMemberCall :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEMemberCall ctx typeHint (theExpr, sr) = case theExpr of
  A.EMemberCall astLhsExpr name astExtraArgsExprs -> do
    lhs <- visitExpr ctx TUnknown astLhsExpr

    foundWithWrongNumParams <- newVar False
    let expectedParamsCount = 1 + length astExtraArgsExprs

    fromModules <-
      lookupMembVName ctx name >>= \xs -> forM xs $ \case
        NlMembAstValDef outerCtx _ blkTDef astVDef _ -> do
          BlockCached {genParams = gps, selfType, blkCtx, wh} <- visitBlockDecl outerCtx blkTDef

          modArgsMaybe <- tryInferGenericArgs [] gps (typeToPType $ snd3 lhs) selfType (thd3 lhs)
          case modArgsMaybe of
            Right modArgs -> do
              (fqn, vDef) <- visitVDef blkCtx astVDef wh
              case vDef.type' of
                H.TFunc ps _ _
                  | isLeft (fst name) || length ps == expectedParamsCount -> do
                      let gpMap = zip (gps <&> (.fqn)) modArgs
                      modWhs <- findTraitImpls ctx gpMap wh (thd3 lhs)
                      pure
                        $ Just
                          VisitMembCallLookupResult
                            { fqn,
                              vDefType = vDef.type',
                              vDefGenParams = drop (length gps) vDef.genParams,
                              modParams = gps,
                              modArgs,
                              modWhs,
                              vDefWhereClauses = vDef.whereClauses,
                              whereClauseIdxMaybe = Nothing,
                              fnIdx = -1,
                              fromTraitTypeMaybe = Nothing
                            }
                H.TFunc {} -> do
                  setVar foundWithWrongNumParams True
                  pure Nothing
                _ -> pure Nothing
            _ ->
              pure Nothing
        NlMembValDef pkgName blk vFqn -> do
          modArgsMaybe <-
            tryInferGenericArgs [] blk.genParams (typeToPType $ snd3 lhs) blk.forType (thd3 lhs)
          case modArgsMaybe of
            Right modArgs -> do
              pkg <- getDepPkg pkgName
              vDef <- getVDefMaybe pkg vFqn <&> must
              case vDef.type' of
                H.TFunc ps _ _
                  | isLeft (fst name) || length ps == expectedParamsCount -> do
                      let gpMap = zip (blk.genParams <&> (.fqn)) modArgs
                      modWhs <- findTraitImpls ctx gpMap blk.whereClauses (thd3 lhs)
                      pure
                        $ Just
                          VisitMembCallLookupResult
                            { fqn = vFqn,
                              vDefType = vDef.type',
                              vDefGenParams = drop (length blk.genParams) vDef.genParams,
                              modParams = blk.genParams,
                              modArgs,
                              modWhs,
                              vDefWhereClauses = vDef.whereClauses,
                              whereClauseIdxMaybe = Nothing,
                              fnIdx = -1,
                              fromTraitTypeMaybe = Nothing
                            }
                H.TFunc {} -> do
                  setVar foundWithWrongNumParams True
                  pure Nothing
                _ -> pure Nothing
            _ ->
              pure Nothing

    fromWhereClauses <-
      lookupMembVNameInCtxWhere ctx (snd3 lhs) (fst name) >>= \xs -> forM xs $ \(traitLoc, trait, vDef) -> do
        let ctxWhs = case traitLoc.src of
              H.FromBlockWheres -> ctx.blockWhereClauses
              H.FromVDefWheres -> ctx.vDefWhereClauses
        let (_, traits) = toList ctxWhs !! traitLoc.whereClauseIdx
        let (_, traitGenArgs) = traits !! traitLoc.whereClauseTraitIdx
        case vDef.vDef.type' of
          H.TFunc ps _ _ | isLeft (fst name) || length ps == expectedParamsCount -> do
            pure
              $ Just
                VisitMembCallLookupResult
                  { fqn = vDef.vDef.fqn,
                    vDefType = vDef.vDef.type',
                    vDefGenParams = vDef.genParams,
                    modParams = trait.selfType : trait.genParams,
                    modArgs = snd3 lhs : traitGenArgs,
                    modWhs = def,
                    vDefWhereClauses = vDef.vDef.whereClauses,
                    whereClauseIdxMaybe = Just traitLoc,
                    fnIdx = vDef.idx,
                    fromTraitTypeMaybe = Nothing
                  }
          H.TFunc {} -> do
            setVar foundWithWrongNumParams True
            pure Nothing
          _ -> pure Nothing

    -- Trait as existential type / 'dyn trait
    fromTraitObject <- case snd3 lhs of
      H.TNamed fqn traitGenArgs -> do
        getTraitMaybe ctx.tcIn fqn <&> \case
          Just trait -> do
            let lookupName n = case HM.lookup n trait.names of
                  Just vDef ->
                    [ VisitMembCallLookupResult
                        { fqn = vDef.vDef.fqn,
                          vDefType = vDef.vDef.type',
                          vDefGenParams = vDef.genParams,
                          modParams = trait.selfType : trait.genParams,
                          modArgs = snd3 lhs : traitGenArgs,
                          modWhs = def,
                          vDefWhereClauses = vDef.vDef.whereClauses,
                          whereClauseIdxMaybe = Nothing,
                          fnIdx = vDef.idx,
                          fromTraitTypeMaybe = Just (trait, vDef)
                        }
                    ]
                  _ -> []
            case fst name of
              Left n -> lookupName n
              Right op ->
                case HM.lookup op trait.ops of
                  Just names ->
                    concat $ toList names <&> lookupName
                  _ -> []
          _ -> []
      _ -> pure []

    let getName = \case Left x -> un x; Right x -> un x
    (calleeExpr, extraArgsExprs) <- case (catMaybes (fromModules <> fromWhereClauses) <> fromTraitObject) of
      -- No results
      [] -> do
        wrongParamsCount <- getVar foundWithWrongNumParams
        throw name
          $ "Member definition '"
          <> getName (fst name)
          <> "'"
          <> (if wrongParamsCount then " with " <> tShow (1 + length astExtraArgsExprs) <> " parameters" else "")
          <> " not found for type "
          <> typeToText (snd3 lhs)
      -- Ambiguity
      _ : _ : _ -> throw name $ "Member name '" <> getName (fst name) <> "' is ambiguous"
      -- 1 result
      [ VisitMembCallLookupResult
          { fqn,
            vDefType,
            vDefGenParams,
            modParams,
            modArgs,
            modWhs,
            vDefWhereClauses,
            whereClauseIdxMaybe,
            fnIdx,
            fromTraitTypeMaybe
          }
        ] -> do
          calleeExprOrHint <- do
            let t = substituteGenerics (zip (modParams <&> (.fqn)) modArgs) vDefType
            if length vDefGenParams == 0
              then do
                let genOverEfs = isGenericOverEffect modParams
                case whereClauseIdxMaybe of
                  Just traitLoc -> do
                    let x = H.EWheresGet {traitLoc, fnIdx, nextWhereClauses = def}
                    pure $ Left $ H.CalleeExpr (x, t, sr)
                  _ -> case fromTraitTypeMaybe of
                    Just (trait, traitVDef) -> do
                      pure
                        $ Left
                        $ H.TraitTypeCalleeExpr
                          { fnType = vDefType,
                            traitDefIndex = traitVDef.idx,
                            traitDefsTotal = length trait.vDefs
                          }
                    _ -> do
                      let wh = H.WhereClauseTraits {mod = modWhs, vDef = def}
                      pure $ Left $ H.CalleeExpr (H.EGlobal fqn modArgs genOverEfs wh, t, sr)
              else do
                let paramHints = typeToPType (snd3 lhs) : replicate (length astExtraArgsExprs) TUnknown
                let ignore = modParams <&> (.fqn)
                gpHints <- inferGenericArgsHints ignore vDefGenParams (TFuncP paramHints typeHint TUnknown) vDefType sr
                let gpMap = zip (vDefGenParams <&> (.fqn)) gpHints
                pure $ Right $ genericTypeToPType gpMap t

          let calleeTypeOrHint = case calleeExprOrHint of
                Left (H.CalleeExpr (_, t, _)) -> Left t
                Left (H.TraitTypeCalleeExpr {fnType}) -> Left fnType
                Right x -> Right x

          case calleeTypeOrHint of
            Left (H.TFunc ps _ _) ->
              unless (length ps == 1 + length astExtraArgsExprs)
                $ throw (srcRangeOf name astExtraArgsExprs) "Wrong number of arguments to member function"
            -- Will be checked later
            _ -> pure ()

          let extraParamsHints =
                let x = case calleeTypeOrHint of
                      Left (H.TFunc ps _ _) -> typeToPType <$> tail ps
                      Right (TFuncP ps _ _) -> tail ps
                      _ -> []
                 in x <> replicate (max 0 $ length astExtraArgsExprs - length x) TUnknown

          extraArgsExprs <- forM (zip astExtraArgsExprs extraParamsHints) $ \(e, h) -> visitExpr ctx h e
          calleeExpr <- case calleeExprOrHint of
            Left e -> pure e
            Right _ -> do
              let extraParamsHints' = extraArgsExprs <&> (snd3 >>> typeToPType)
              let pType = TFuncP (typeToPType (snd3 lhs) : extraParamsHints') typeHint TUnknown
              let modParams' = modParams <&> (.fqn)
              genArgs <- inferGenericArgs modParams' vDefGenParams pType vDefType (thd3 lhs)
              let gps' = vDefGenParams <&> (.fqn)
              let gpMap = zip modParams' modArgs <> zip gps' genArgs
              let t = substituteGenerics gpMap vDefType
              let genOverEfs = isGenericOverEffect modParams || isGenericOverEffect vDefGenParams
              whs <- findTraitImpls ctx gpMap vDefWhereClauses (thd3 lhs)
              case whereClauseIdxMaybe of
                Just traitLoc -> do
                  let x = H.EWheresGet {traitLoc, fnIdx, nextWhereClauses = whs}
                  pure $ H.CalleeExpr (x, t, sr)
                _ -> case fromTraitTypeMaybe of
                  Just (trait, traitVDef) -> do
                    pure
                      $ H.TraitTypeCalleeExpr
                        { fnType = t,
                          traitDefIndex = traitVDef.idx,
                          traitDefsTotal = length trait.vDefs
                        }
                  _ -> do
                    let whs' = H.WhereClauseTraits {mod = modWhs, vDef = whs}
                    pure $ H.CalleeExpr (H.EGlobal fqn (modArgs <> genArgs) genOverEfs whs', t, sr)

          case fromTraitTypeMaybe of
            Just (trait, vDef) -> do
              case vDef.vDef.type' of
                H.TFunc (_ : ps) r ef -> do
                  let hasSelfInWrongPlace =
                        any (`typeContainsFqn` trait.fqn) ps
                          || typeContainsFqn r trait.fqn
                          || typeContainsFqn ef trait.fqn
                  when hasSelfInWrongPlace
                    $ throw sr
                    $ "Function is not usable through a trait type as "
                    <> "it uses the Self type in a place other than the first parameter"

                  when (typeContainsFqnMatch vDef.vDef.type' tFqnIsAssociatedType)
                    $ throw sr
                    $ "Function is not usable through a trait type as it uses associated types"
                _ -> pure () -- Non-function or 0-arg function type will be caught later
            _ -> pure ()

          pure (calleeExpr, extraArgsExprs)

    let calleeFnType = case calleeExpr of H.CalleeExpr (_, x, _) -> x; H.TraitTypeCalleeExpr {fnType} -> fnType

    (lhs', extraArgsExprs', retType, fnEffs) <- case calleeFnType of
      H.TFunc ps r ef -> do
        unless (length ps == length astExtraArgsExprs + 1)
          $ throw (srcRangeOf name astExtraArgsExprs) "Wrong number of arguments to member function"
        as <- forM (zip (tail ps) extraArgsExprs) $ \(ex, argExpr) ->
          implicitCast ctx argExpr ex
        pure (lhs, as, r, case ef of H.TEffect x -> x; _ -> undefined)
      _ -> throw astLhsExpr "Type is not a function"

    do
      efs <- getEffects <&> (<> fnEffs)
      assertM $ flip all efs $ \case H.TNamed {} -> True; _ -> False
      setEffects $ flip filter efs $ \case
        H.TNamed (TFqn "#builtins/:MutVarEff") [H.TLifetime closureDepth _] ->
          closureDepth < ctx.closureDepth
        _ -> True

    pure (H.EFnCall calleeExpr (lhs' : extraArgsExprs'), retType, sr)
  _ -> undefined

visitExprGetEffs :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitExprGetEffs a b c = do
  effsBefore <- getEffects
  setEffects def
  e <- visitExpr a b c
  effs <- getEffects
  setEffects effsBefore
  pure (e, effs)

visitETry :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitETry ctx typeHint (theExpr, sr) = case theExpr of
  A.ETry tryExpr catches finallyMaybe -> do
    (tryExpr', tryEffects) <- visitExprGetEffs ctx typeHint tryExpr
    let tryType = snd3 tryExpr'
    let catchHint = typeToPType tryType

    remainingEffects <- newVar tryEffects

    catches' <- forM catches $ \(destrMaybe, varSr, e) -> case destrMaybe of
      Nothing -> do
        setVar remainingEffects def
        e' <- visitExprGetEffs ctx catchHint e
        pure ((H.DIgnore, anyType, varSr), e')
      Just (astTypeExpr, destr) -> do
        exType <- visitTypeExpr ctx astTypeExpr

        ctxVar <- newVar ctx
        destr' <- visitDestructure ctxVar exType destr
        ctx' <- getVar ctxVar

        (e', effs) <- visitExprGetEffs ctx' catchHint e
        e'' <- implicitCast ctx' e' tryType
        modVar remainingEffects $ HS.delete (H.TNamed (TFqn "#builtins/:Throws") [exType])
        pure (destr', (e'', effs))
    finallyMaybe' <- forM finallyMaybe $ \e -> do
      e'@((_, t, _), _) <- visitExprGetEffs ctx unitHint e
      unless (t == unitType) $ throw e "Finally block/expression may not produce a value"
      pure e'

    let finallyEffects = maybe def snd finallyMaybe'

    newEffs <-
      getVar remainingEffects
        <&> \effs -> mconcat $ effs : finallyEffects : (toList catches' <&> snd . snd)

    getEffects >>= \effs' -> setEffects $ newEffs <> effs'

    let catches'' = catches' <&> second fst
    pure (H.ETry tryExpr' catches'' (finallyMaybe' <&> fst), tryType, sr)
  _ -> undefined

visitEThrow :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEThrow ctx typeHint (theExpr, sr) = case theExpr of
  A.EThrow e -> do
    e'@(_, exType, _) <- visitExpr ctx TUnknown e
    ex <- case pTypeToType typeHint of
      Just x -> pure x
      _ -> throw sr "Unable to deduce type"

    addEffect $ H.TNamed (TFqn "#builtins/:Throws") [exType]
    pure (H.EThrow e', ex, sr)
  _ -> undefined

visitEYield :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEYield ctx _ (theExpr, sr) = case theExpr of
  A.EYield e -> do
    typeHint <- case ctx.iteratorYieldType of
      Just t -> pure $ typeToPType t
      _ -> throw sr "Yield is only valid within iterators"
    e' <- visitExpr ctx typeHint e
    pure (H.EYield e', unitType, sr)
  _ -> undefined

visitEIndex :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEIndex ctx _ (theExpr, sr) = case theExpr of
  A.EIndex e i' -> do
    i <- if i' < 0 || i' >= 1000 then throw sr "Index out of range" else pure $ fromIntegral i'
    e'@(_, t, _) <- visitExpr ctx TUnknown e
    ts <- case t of
      H.TTuple ts -> pure $ toList ts
      H.TNamed {} -> do
        (dataTypeDef, (_, genArgs)) <- getDataDefType (snd e) t
        case dataTypeDef.dataCons of
          List1 (H.DataCons _ (H.TupleFields ts)) [] -> do
            let gpMap = zip (dataTypeDef.t1.genParams <&> (.fqn)) genArgs
            pure $ substituteGenerics gpMap <$> ts
          _ -> throw sr "Not a tuple or tuple-like data type"
      _ -> throw sr "Not a tuple or named type"
    t' <- case ts !? i of Just x -> pure x; _ -> throw sr "Index out of range"
    pure (if length ts == 1 then H.ENewtypeAccess e' else H.EIndex e' i, t', sr)
  _ -> undefined

visitEFieldAccess :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEFieldAccess ctx _ (theExpr, sr) = case theExpr of
  A.EFieldAccess e fieldName -> do
    e'@(_, recordType, _) <- visitExpr ctx TUnknown e
    (dataTypeDef, (_, genArgs)) <- getDataDefType (snd e) recordType
    fields <- case dataTypeDef.dataCons of
      List1 (H.DataCons _ (H.RecordFields fs)) [] -> do
        let gpMap = zip (dataTypeDef.t1.genParams <&> (.fqn)) genArgs
        pure $ fs <&> second (substituteGenerics gpMap)
      _ -> throw fieldName $ "Cannot access field '" <> un (fst fieldName) <> "' in value with non-record type"

    fieldType <- case lookup (fst fieldName) $ toList fields of
      Just x -> pure x
      _ -> throw fieldName $ "No such field: " <> un (fst fieldName)

    pure (H.EFieldAccess e' fieldName, fieldType, sr)
  _ -> undefined

visitERecordInit :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitERecordInit ctx typeHint (theExpr, sr) = case theExpr of
  A.ERecordInit astDataCons astFieldValues -> do
    -- Use the type expression to get the data constructor & type
    (dCons, recordType, dConsFields') <- case fst astDataCons of
      A.TNamed qualMaybe typeName typeArgs -> do
        getDataCons ctx typeHint qualMaybe typeName typeArgs
      _ -> error "Not a named type"
    dConsFields <- case dConsFields' of
      H.TupleFields _ -> throw sr "Not a record"
      H.RecordFields xs -> pure xs

    fieldValuesAndEffects <- forM astFieldValues $ \(n, eMaybe) -> do
      let e = case eMaybe of
            Just e' -> e'
            _ -> (A.EVar Nothing (fst n) [], snd n)
      -- Lookup field type in dConsFields
      expectedType <- case lookup (fst n) $ toList dConsFields of
        Just t -> pure t
        Nothing -> throw sr $ "Field '" <> un (fst n) <> "' not found in record"
      let hint = typeToPType expectedType
      e' <- visitExpr ctx hint e
      e'' <- implicitCast ctx e' expectedType
      pure e''

    let fieldExprs = fieldValuesAndEffects

    -- Check for missing fields
    namesAndIdxs <- forM dConsFields $ \(fieldName, _) -> do
      case findIndex (\((n, _), _) -> n == fieldName) $ toList astFieldValues of
        Just i -> pure (fieldName, i)
        _ ->
          throw sr
            $ "Missing field '"
            <> un fieldName
            <> "' in record initialization"

    let e = H.ERecordInit dCons fieldExprs namesAndIdxs
    pure (e, recordType, sr)
  _ -> undefined

visitEBreak :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEBreak ctx _ (theExpr, sr) = case theExpr of
  A.EBreak -> do
    lbl <- case ctx.inLoop of
      Just x -> pure x
      _ -> throw sr "Break expression is only valid within loops"
    pure (H.EBreak lbl, unreachableType, sr)
  _ -> undefined

visitEContinue :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEContinue ctx _ (theExpr, sr) = case theExpr of
  A.EContinue -> do
    lbl <- case ctx.inLoop of
      Just x -> pure x
      _ -> throw sr "Continue expression is only valid within loops"
    pure (H.EContinue lbl, unreachableType, sr)
  _ -> undefined

visitEUpdate :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEUpdate ctx _ (theExpr, sr) = case theExpr of
  A.EUpdate e setters -> do
    e'@(_, lhsType, _) <- visitExpr ctx TUnknown e

    -- Setter exprs may have side effects so they get stored in a list and referenced by index
    setterExprs <- newVar $ replicate (length setters) Nothing

    let -- Recursively build the EUpdatePart tree by walking the type.
        -- 'currentPrefix' tracks the accessor prefix we have matched so far.
        buildUpdatePart :: H.Type -> [A.AccessorChainPart'] -> m H.EUpdatePart
        buildUpdatePart t currentPrefix = do
          -- Check for any setter whose accessor chain ends here (at this prefix)
          let updateValueSetterIdxMaybe =
                flip mapMaybe (zip [0 :: Int ..] setters) $ \(i, (parts, _)) ->
                  if (fst <$> toList parts) == currentPrefix then Just i else Nothing

          case updateValueSetterIdxMaybe of
            (i : _) -> do
              -- Exact match for currentPrefix, just set the value
              oldExprMaybe <- getVar setterExprs <&> (!! i)
              assertM $ isNothing oldExprMaybe -- Parser should have caught this
              e'' <- visitExpr ctx (typeToPType t) $ snd $ setters !! i
              e''' <- implicitCast ctx e'' t
              modVar setterExprs $ updateAt i $ const $ Just e'''
              pure $ H.EUpdateValue i
            _ -> case t of
              H.TTuple ts -> do
                parts <- forM (zipList2 ts $ List2 0 1 [2 :: Int]) $ \(t', i) ->
                  buildUpdatePart t' $ currentPrefix <> [A.AccessorChainIndex i]
                pure $ H.EUpdateTuple $ list2ToList1 parts
              H.TNamed tFqn genArgs -> do
                tDef <- getTDef sr t
                if (tDef.tDefType /= H.IsDataDef) || tDef.typeKind /= MonoType
                  then
                    pure H.EUpdateNoChange
                  else do
                    (dataTypeDef, _) <- getDataDefType sr t
                    let gpMap = zip (dataTypeDef.t1.genParams <&> (.fqn)) genArgs
                    case dataTypeDef.dataCons of
                      List1 (H.DataCons _ (H.TupleFields [])) _ ->
                        throw sr "Cannot update empty types"
                      List1 (H.DataCons _ (H.TupleFields (t0 : ts))) _ -> do
                        let ts' = List1 t0 ts <&> substituteGenerics gpMap
                        parts <- forM (zipList1 ts' $ List1 0 [1 ..]) $ \(t', i) ->
                          buildUpdatePart t' $ currentPrefix <> [A.AccessorChainIndex i]
                        pure $ H.EUpdateTuple parts
                      List1 (H.DataCons _ (H.RecordFields fields)) [] -> do
                        -- Record type: single data constructor with named fields
                        let allFieldNames = fields <&> fst
                        parts <- forM allFieldNames $ \fieldName -> do
                          let genericFieldType = must $ lookup fieldName $ toList fields
                          let fieldType = substituteGenerics gpMap genericFieldType
                          p <- buildUpdatePart fieldType $ currentPrefix <> [A.AccessorChainName fieldName]
                          pure (fieldName, p)
                        let dCons =
                              H.DataConsInfo tFqn (fst dataTypeDef.t1.name) 0 False True dataTypeDef.isEnumType
                        pure $ H.EUpdateRecord dCons parts
                      List1 _ (_ : _) ->
                        throw sr "Update not supported for types with multiple data constructors"
              _ -> pure H.EUpdateNoChange

    updatePart <- buildUpdatePart lhsType []

    setterExprs'' <- getVar setterExprs
    forM_ (zip setters setterExprs'') $ \((ps, sr'), se) -> case se of
      Just _ -> pure ()
      _ -> do
        let acPartToText = \case
              A.AccessorChainName x -> un x
              A.AccessorChainIndex i -> tShow i
        let acChain = T.concat $ toList ps <&> (fst >>> acPartToText >>> ("." <>))
        throw sr' $ "No such field: " <> acChain

    let setterExprs' = must $ sequence setterExprs''
    pure (H.EUpdate e' setterExprs' updatePart, lhsType, sr)
  _ -> undefined

visitEExplicitType :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEExplicitType ctx _ (theExpr, _) = case theExpr of
  A.EExplicitType e t -> do
    t' <- visitTypeExpr ctx t
    e' <- visitExpr ctx (typeToPType t') e
    e'' <- implicitCast ctx e' t'
    pure e''
  _ -> undefined

visitEAs :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m H.Expr
visitEAs ctx _ (theExpr, sr) = case theExpr of
  A.EAs e t -> do
    toType <- visitTypeExpr ctx t
    e'@(_, actType, _) <- visitExpr ctx TUnknown e
    let isIntType (TFqn fqn) = fqn == "#builtins/:Int" || fqn == "#builtins/:I32"
    let isNumericType fqn'@(TFqn fqn) = isIntType fqn' || fqn == "#builtins/:Real"
    let err = throw sr "Unknown conversion"
    e'' <- case (actType, toType) of
      (H.TNamed fromFqn _, H.TNamed toFqn []) | isNumericType fromFqn && isNumericType toFqn -> do
        pure (H.ECastNumber e', toType, sr)
      (H.TNamed {}, H.TNamed toFqn []) | isIntType toFqn -> do
        tDef <- getTDef sr actType
        if tDef.tDefType /= H.IsBuiltin
          then do
            (dataTypeDef, _) <- getDataDefType sr actType
            if dataTypeDef.isEnumType
              then do
                pure (H.ECastNumber e', toType, sr)
              else
                err
          else err
      _ -> err
    pure e''
  _ -> undefined

getTDef :: (MonadTc m, HasCallStack) => SrcRange -> H.Type -> m H.TDef
getTDef sr t = case t of
  H.TNamed fqn _ -> do
    let pkg = tFqnToPkg fqn
    -- Look up the type definition
    pkg' <- getDepOrThisPkg pkg
    getTDefMaybe pkg' fqn <&> must
  _ -> throw sr "Not a named type"

visitStmt :: (MonadTc m) => Var m Ctx -> PType -> A.Stmt -> m H.Stmt
visitStmt ctxVar typeHint (astStmt, sr) = case astStmt of
  A.SLet destr astTypeExprMaybe astExpr -> do
    ctx <- getVar ctxVar

    typeMaybe <- forM astTypeExprMaybe $ visitTypeExpr ctx
    let typeHint' = case typeMaybe of Just x -> typeToPType x; _ -> TUnknown

    e' <- visitExpr ctx typeHint' astExpr
    e''@(_, t, _) <- case typeMaybe of Just x -> implicitCast ctx e' x; _ -> pure e'

    d <- visitDestructure ctxVar t destr
    pure (H.SLet d e'', sr)
  A.SRecLet name astTypeExpr astExpr -> do
    ctx <- getVar ctxVar

    explicitType <- visitTypeExpr ctx astTypeExpr
    let typeHint' = typeToPType explicitType

    uid <- mkLocalVarUid
    let ctx' = ctx {variables = Variable False name uid explicitType ctx.closureDepth ctx.scopeDepth : ctx.variables}
    setVar ctxVar ctx'

    e' <- visitExpr ctx' typeHint' astExpr
    e'' <- implicitCast ctx' e' explicitType

    pure (H.SRecLet name uid e'', sr)
  A.SExpr astExpr -> do
    ctx <- getVar ctxVar
    e' <- visitExpr ctx typeHint (astExpr, sr)
    pure (H.SExpr e', sr)
  A.SWhen astCondExpr astThenExpr -> do
    ctx <- getVar ctxVar
    condExpr@(_, shouldBeBool, _) <- visitExpr ctx boolHint astCondExpr
    unless (shouldBeBool == boolType)
      $ throw astCondExpr ("Condition type must be Bool, got " <> typeToText shouldBeBool)

    thenExpr <- visitExpr ctx TUnknown astThenExpr

    pure (H.SWhen condExpr thenExpr, sr)
  A.SAssign n@(name, nameSr) rhs -> do
    ctx <- getVar ctxVar
    var <- case findLocalVarByName ctx name of
      Just x -> pure x
      _ -> throw nameSr $ "No such variable: " <> un name
    unless var.isMutable $ throw nameSr "Cannot assign to immutable variable"

    rhs' <- visitExpr ctx (typeToPType var.typ) rhs

    rhs'' <- implicitCast ctx rhs' var.typ

    when (var.closureDepth < ctx.closureDepth) $ do
      let l = H.TLifetime var.closureDepth var.scopeDepth
      addEffect $ H.TNamed (TFqn "#builtins/:MutVarEff") [l]

    pure (H.SAssign var.uid n rhs'', sr)
  A.SForEach {destr, inExpr, bodyExpr} -> do
    ctx <- getVar ctxVar

    inExpr'@(_, inType, _) <- visitExpr ctx TUnknown inExpr

    iterInnerType <- case inType of
      H.TNamed (TFqn "#builtins/:Iter") [t] -> pure t
      _ -> throw inExpr $ "Expected Iter type, got " <> typeToText inType

    let varType = iterInnerType

    ctxVar' <- newVar ctx
    destr' <- visitDestructure ctxVar' varType destr
    ctx' <- getVar ctxVar'

    label <- mkLocalVarUid

    bodyExpr'@(_, bodyType, _) <- visitExpr ctx' {inLoop = Just label} unitHint bodyExpr

    unless (bodyType == unitType || bodyType == unreachableType)
      $ addError
        SevWarning
        bodyExpr
        ("Value of type " <> typeToText bodyType <> " produced by foreach loop body is discarded")

    let s' =
          H.SForEach
            { destr = destr',
              inExpr = inExpr',
              bodyExpr = bodyExpr',
              label
            }

    pure (s', sr)
  A.SLoop e -> do
    ctx <- getVar ctxVar
    label <- mkLocalVarUid
    e' <- visitExpr (ctx {inLoop = Just label}) TUnknown e
    pure (H.SLoop e' label, sr)
