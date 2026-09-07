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
visitExpr :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
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

visitELitInt :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitELitInt _ typeHint (theExpr, sr) = case theExpr of
  A.ELitInt i -> do
    case typeHint of
      TNamedP (TFqn "#builtins/:I32") _
        | i >= -2147483648 && i <= 2147483647 ->
            pure ((H.ELitInt32 $ fromIntegral i, i32Type, sr), def)
      TNamedP (TFqn "#builtins/:Real") _
        | i >= -9007199254740992 && i <= 9007199254740992 ->
            pure ((H.ELitFloat $ tShow i, realType, sr), def)
      _ ->
        pure ((H.ELitInt i, intType, sr), def)
  _ -> undefined

visitELitFloat :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitELitFloat _ _ (theExpr, sr) = case theExpr of
  A.ELitFloat f ->
    pure ((H.ELitFloat f, realType, sr), def)
  _ -> undefined

visitELitBool :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitELitBool _ _ (theExpr, sr) = case theExpr of
  A.ELitBool b ->
    pure ((H.ELitBool b, boolType, sr), def)
  _ -> undefined

visitELitString :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitELitString _ _ (theExpr, sr) = case theExpr of
  A.ELitString s ->
    pure ((H.ELitString s, stringType, sr), def)
  _ -> undefined

visitELitList :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitELitList ctx typeHint (theExpr, sr) = case theExpr of
  A.ELitList es -> do
    case head es of
      Just e0 -> do
        let e0Hint = case typeHint of
              TNamedP (TFqn "#builtins/:Vec") [t] -> t
              _ -> TUnknown
        (e0'@(_, t, _), effs1) <- visitExpr ctx e0Hint e0
        let hint = typeToPType t
        tail' <- forM (tail es) $ \e -> do
          (e', ef) <- visitExpr ctx hint e
          e'' <- implicitCast ctx e' t
          pure (e'', ef)

        let t' = H.TNamed (TFqn "#builtins/:Vec") [t]
        pure ((H.ELitList $ e0' : (fst <$> tail'), t', sr), effs1 <> mconcat (snd <$> tail'))
      _ -> do
        t <- case pTypeToType typeHint of
          Just x@(H.TNamed (TFqn "#builtins/:Vec") [_]) -> pure x
          _ -> throw sr "Unable to deduce type of empty list"

        pure ((H.ELitList [], t, sr), def)
  _ -> undefined

visitEVar :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
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
          pure ((H.EGlobal fqn ts (isGenericOverEffect vDef.genParams) whs', t, sr), def)

    case qualMaybe of
      Just _ -> findGlobal
      _ -> case findLocalVarByName ctx name of
        Just v -> do
          unless (null genArgs) $ throw sr "Local variables cannot be generic"
          pure ((H.EVar v.uid (un name), v.typ, sr), def)
        _ -> findGlobal
  _ -> undefined

visitEClosure :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEClosure ctx typeHint (theExpr, sr) = case theExpr of
  A.EClosure params astExpr -> do
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

    let closureDepth = ctx.closureDepth + 1

    ctxVar <- newVar $ ctx {closureDepth, inLoop = ctx.inLoop} -- inLoop is to disambiguate the record update :/
    params' <- forM (zip params paramsTypes) $ \((d, _), t) -> visitDestructure ctxVar t d
    ctx' <- getVar ctxVar

    (e@(_, retType, _), ef) <- visitExpr ctx' retTypeHint astExpr <&> first (`implicitCastHint` retTypeHint)
    assertM $ flip all ef $ \case H.TNamed {} -> True; _ -> False
    let efType = H.TEffect ef
    let fnType = H.TFunc paramsTypes retType efType

    pure ((H.EClosure params' e, fnType, sr), def)
  _ -> undefined

visitEFnCall :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEFnCall ctx typeHint (theExpr, sr) = case theExpr of
  A.EFnCall astCalleeExpr astArgsExprs -> do
    calleeExprOrHint <- case fst astCalleeExpr of
      A.EVar qualMaybe name [] -> do
        let findGlobal = do
              (fqn, vDef) <- lookupGlobalVDef ctx qualMaybe name sr

              let gp = vDef.genParams
              if null gp
                then pure $ Left ((H.EGlobal fqn [] False def, vDef.type', sr), def)
                else do
                  let paramHints = replicate (length astArgsExprs) TUnknown
                  gpHints <- inferGenericArgsHints [] vDef.genParams (TFuncP paramHints typeHint TUnknown) vDef.type' sr
                  let gps' = vDef.genParams <&> (.fqn)
                  pure $ Right $ genericTypeToPType (zip gps' gpHints) vDef.type'

        case qualMaybe of
          Just _ -> findGlobal
          _ -> case findLocalVarByName ctx name of
            Just v ->
              pure $ Left ((H.EVar v.uid (un name), v.typ, sr), def)
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
              pure $ Left ((H.EDataCons dcInfo, genericType, sr), def)
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
      Left ((_, H.TFunc ps _ _, _), _) ->
        unless (length ps == length astArgsExprs) $ throw sr "Wrong number of arguments to function"
      -- Will be checked later
      _ -> pure ()

    let paramsHints =
          let x = case calleeExprOrHint of
                Left ((_, H.TFunc ps _ _, _), _) -> typeToPType <$> ps
                Right (TFuncP ps _ _) -> ps
                _ -> []
           in x <> replicate (max 0 $ length astArgsExprs - length x) TUnknown

    argsExprs <- forM (zip astArgsExprs paramsHints) $ \(e, h) -> visitExpr ctx h e

    calleeExpr <- case calleeExprOrHint of
      Left e -> pure e
      Right _ -> do
        let paramsHints' = argsExprs <&> (fst >>> snd3 >>> typeToPType)
        visitExpr ctx (TFuncP paramsHints' typeHint TUnknown) astCalleeExpr

    (argsExprs', retType, fnEffs) <- case snd3 $ fst calleeExpr of
      H.TFunc ps r ef -> do
        unless (length ps == length astArgsExprs) $ throw sr "Wrong number of arguments to function"
        as <- forM (zip ps argsExprs) $ \(ex, (argExpr, efs)) ->
          implicitCast ctx argExpr ex <&> (,efs)
        pure (as, r, case ef of H.TEffect x -> x; _ -> undefined)
      _ -> throw astCalleeExpr "Type is not a function"

    let effs = mconcat $ snd calleeExpr : fnEffs : (snd <$> argsExprs')
    let effs' = flip filter effs $ \case
          H.TNamed (TFqn "#builtins/:MutatesVars") [H.TLifetime l] ->
            l < ctx.closureDepth
          _ -> True

    assertM $ flip all effs' $ \case H.TNamed {} -> True; _ -> False

    pure ((H.EFnCall (H.CalleeExpr $ fst calleeExpr) (fst <$> argsExprs'), retType, sr), effs')
  _ -> undefined

visitEDoBlock :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEDoBlock ctx typeHint (theExpr, sr) = case theExpr of
  A.EDoBlock ss eMaybe -> do
    ctxVar <- newVar ctx
    ss' <- forM ss $ \s -> do
      visitStmt ctxVar TUnknown s
    ctx' <- getVar ctxVar
    e <- forM eMaybe $ visitExpr ctx' typeHint
    let (t, exprEffs) = case e of
          Just ((_, t', _), es) -> (t', es)
          _ -> (unitType, def)
    let effs = mconcat $ exprEffs : (snd <$> ss')
    pure ((H.EDoBlock (ss' <&> fst) (e <&> fst), t, sr), effs)
  _ -> undefined

visitEIf :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEIf ctx typeHint (theExpr, sr) = case theExpr of
  A.EIf astCondExpr astThenExpr astElseExpr -> do
    (condExpr@(_, shouldBeBool, _), ef0) <- visitExpr ctx boolHint astCondExpr
    unless (shouldBeBool == boolType)
      $ throw astCondExpr
      $ "Condition type must be Bool, got "
      <> typeToText shouldBeBool
    (thenExpr@(_, t0, _), ef1) <- visitExpr ctx typeHint astThenExpr
    (elseExpr@(_, t1, _), ef2) <- visitExpr ctx typeHint astElseExpr
    let t = if t0 == unreachableType then t1 else t0
    thenExpr'@(_, t0', _) <- implicitCast ctx thenExpr t
    elseExpr'@(_, t1', _) <- implicitCast ctx elseExpr t

    unless (t0' == t1')
      $ throw
        sr
        ("If-else branch types do not match\nGot " <> typeToText t0 <> " and " <> typeToText t1)
    pure ((H.EIf condExpr thenExpr' elseExpr', t, sr), ef0 <> ef1 <> ef2)
  _ -> undefined

visitETuple :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitETuple ctx typeHint (theExpr, sr) = case theExpr of
  A.ETuple es -> do
    let hints = case typeHint of
          TTupleP xs -> xs
          _ -> List2 TUnknown TUnknown $ replicate (length es - 2) TUnknown
    es' <- forM (zipList2 es hints) $ \(e, h) -> visitExpr ctx h e
    let t = H.TTuple $ (fst >>> snd3) <$> es'
    let e = H.ETuple $ fst <$> es'
    pure ((e, t, sr), mconcat $ snd <$> toList es')
  _ -> undefined

visitEAnd :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEAnd ctx _ (theExpr, sr) = case theExpr of
  A.EAnd lhs rhs -> do
    (lhs', eff1) <- visitExpr ctx boolHint lhs
    lhs'' <- implicitCast ctx lhs' boolType
    (rhs', eff2) <- visitExpr ctx boolHint rhs
    rhs'' <- implicitCast ctx rhs' boolType

    pure ((H.EAnd lhs'' rhs'', boolType, sr), eff1 <> eff2)
  _ -> undefined

visitEOr :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEOr ctx _ (theExpr, sr) = case theExpr of
  A.EOr lhs rhs -> do
    (lhs', eff1) <- visitExpr ctx boolHint lhs
    lhs'' <- implicitCast ctx lhs' boolType
    (rhs', eff2) <- visitExpr ctx boolHint rhs
    rhs'' <- implicitCast ctx rhs' boolType

    pure ((H.EOr lhs'' rhs'', boolType, sr), eff1 <> eff2)
  _ -> undefined

visitEMatch :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEMatch ctx typeHint (theExpr, sr) = case theExpr of
  A.EMatch caseExpr bs -> do
    (caseExpr'@(_, exprType, _), ef0) <- visitExpr ctx TUnknown caseExpr
    -- TODO Ensure branch patterns are complete
    finalType <- newVar Nothing
    bs' <- forM bs $ \b -> do
      ctxVar <- newVar ctx
      p' <- visitPattern ctxVar exprType b.pattern
      ctx' <- getVar ctxVar
      guard <- forM b.guard $ visitExpr ctx' boolHint
      tMaybe <- getVar finalType
      let hint = case tMaybe of Just x -> typeToPType x; _ -> typeHint
      (e'@(_, t, _), ef1) <- visitExpr ctx' hint b.expr
      e'' <- case tMaybe of
        Just ex'' -> do
          implicitCast ctx' e' ex''
        _ -> do
          unless (t == unreachableType) $ setVar finalType $ Just t
          pure e'
      pure (H.MatchBranch p' (fst <$> guard) e'', case guard of Just (_, ef) -> ef <> ef1; _ -> ef1)

    let effs = mconcat $ ef0 : (snd <$> toList bs')
    t <- getVar finalType <&> fromMaybe unreachableType
    pure ((H.EMatch caseExpr' $ bs' <&> fst, t, sr), effs)
  _ -> undefined

visitEDataCons :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
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
    pure (e, def)
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

visitEMemberCall :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEMemberCall ctx typeHint (theExpr, sr) = case theExpr of
  A.EMemberCall astLhsExpr name astExtraArgsExprs -> do
    (lhs, lhsEff) <- visitExpr ctx TUnknown astLhsExpr

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
              let extraParamsHints' = extraArgsExprs <&> (fst >>> snd3 >>> typeToPType)
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
        as <- forM (zip (tail ps) extraArgsExprs) $ \(ex, (argExpr, efs)) ->
          implicitCast ctx argExpr ex <&> (,efs)
        pure (lhs, as, r, case ef of H.TEffect x -> x; _ -> undefined)
      _ -> throw astLhsExpr "Type is not a function"

    let effs = mconcat $ lhsEff : fnEffs : (snd <$> extraArgsExprs')
    let effs' = flip filter effs $ \case
          H.TNamed (TFqn "#builtins/:MutatesVars") [H.TLifetime l] ->
            l < ctx.closureDepth
          _ -> True

    assertM $ flip all effs' $ \case H.TNamed {} -> True; _ -> False

    pure ((H.EFnCall calleeExpr (lhs' : (fst <$> extraArgsExprs')), retType, sr), effs')
  _ -> undefined

visitETry :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitETry ctx typeHint (theExpr, sr) = case theExpr of
  A.ETry tryExpr catches finallyMaybe -> do
    (tryExpr', tryEffects) <- visitExpr ctx typeHint tryExpr
    let tryType = snd3 tryExpr'
    let catchHint = typeToPType tryType
    remainingEffects <- newVar tryEffects
    catches' <- forM catches $ \(destrMaybe, varSr, e) -> case destrMaybe of
      Nothing -> do
        setVar remainingEffects def
        e' <- visitExpr ctx catchHint e
        pure ((H.DIgnore, anyType, varSr), e')
      Just (astTypeExpr, destr) -> do
        exType <- visitTypeExpr ctx astTypeExpr

        ctxVar <- newVar ctx
        destr' <- visitDestructure ctxVar exType destr
        ctx' <- getVar ctxVar

        (e', effs) <- visitExpr ctx' catchHint e
        e'' <- implicitCast ctx' e' tryType
        remaining <- getVar remainingEffects
        let remaining' = HS.delete (H.TNamed (TFqn "#builtins/:Throws") [exType]) remaining
        setVar remainingEffects remaining'
        pure (destr', (e'', effs))
    finallyMaybe' <- forM finallyMaybe $ \e -> do
      e'@((_, t, _), _) <- visitExpr ctx unitHint e
      unless (t == unitType) $ throw e "Finally block/expression may not produce a value"
      pure e'
    let finallyEffects = fromMaybe def $ finallyMaybe' <&> snd
    effs <-
      getVar remainingEffects
        <&> \effs -> mconcat $ effs : finallyEffects : (toList catches' <&> (\(_, (_, es)) -> es))
    let catches'' = catches' <&> \(d, (e, _)) -> (d, e)
    pure ((H.ETry tryExpr' catches'' (finallyMaybe' <&> fst), tryType, sr), effs)
  _ -> undefined

visitEThrow :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEThrow ctx typeHint (theExpr, sr) = case theExpr of
  A.EThrow e -> do
    (e'@(_, exType, _), effs1) <- visitExpr ctx TUnknown e
    ex <- case pTypeToType typeHint of
      Just x -> pure x
      _ -> throw sr "Unable to deduce type"
    let exEf = H.TNamed (TFqn "#builtins/:Throws") [exType]
    pure ((H.EThrow e', ex, sr), HS.insert exEf effs1)
  _ -> undefined

visitEYield :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEYield ctx _ (theExpr, sr) = case theExpr of
  A.EYield e -> do
    typeHint <- case ctx.iteratorYieldType of
      Just t -> pure $ typeToPType t
      _ -> throw sr "Yield is only valid within iterators"
    (e', effs1) <- visitExpr ctx typeHint e
    pure ((H.EYield e', unitType, sr), effs1)
  _ -> undefined

visitEIndex :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEIndex ctx _ (theExpr, sr) = case theExpr of
  A.EIndex e i' -> do
    i <- if i' < 0 || i' >= 1000 then throw sr "Index out of range" else pure $ fromIntegral i'
    (e'@(_, t, _), ef) <- visitExpr ctx TUnknown e
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
    pure ((if length ts == 1 then H.ENewtypeAccess e' else H.EIndex e' i, t', sr), ef)
  _ -> undefined

visitEFieldAccess :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEFieldAccess ctx _ (theExpr, sr) = case theExpr of
  A.EFieldAccess e fieldName -> do
    (e'@(_, recordType, _), eff) <- visitExpr ctx TUnknown e
    (dataTypeDef, (_, genArgs)) <- getDataDefType (snd e) recordType
    fields <- case dataTypeDef.dataCons of
      List1 (H.DataCons _ (H.RecordFields fs)) [] -> do
        let gpMap = zip (dataTypeDef.t1.genParams <&> (.fqn)) genArgs
        pure $ fs <&> second (substituteGenerics gpMap)
      _ -> throw fieldName $ "Cannot access field '" <> un (fst fieldName) <> "' in value with non-record type"

    fieldType <- case lookup (fst fieldName) $ toList fields of
      Just x -> pure x
      _ -> throw fieldName $ "No such field: " <> un (fst fieldName)

    pure ((H.EFieldAccess e' fieldName, fieldType, sr), eff)
  _ -> undefined

visitERecordInit :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
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
      (e', efs) <- visitExpr ctx hint e
      e'' <- implicitCast ctx e' expectedType
      pure (e'', efs)

    let fieldExprs = fieldValuesAndEffects <&> fst
    let effs = mconcat $ snd <$> toList fieldValuesAndEffects

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
    pure ((e, recordType, sr), effs)
  _ -> undefined

visitEBreak :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEBreak ctx _ (theExpr, sr) = case theExpr of
  A.EBreak -> do
    lbl <- case ctx.inLoop of
      Just x -> pure x
      _ -> throw sr "Break expression is only valid within loops"
    pure ((H.EBreak lbl, unreachableType, sr), def)
  _ -> undefined

visitEContinue :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEContinue ctx _ (theExpr, sr) = case theExpr of
  A.EContinue -> do
    lbl <- case ctx.inLoop of
      Just x -> pure x
      _ -> throw sr "Continue expression is only valid within loops"
    pure ((H.EContinue lbl, unreachableType, sr), def)
  _ -> undefined

visitEUpdate :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEUpdate ctx _ (theExpr, sr) = case theExpr of
  A.EUpdate e setters -> do
    (e'@(_, lhsType, _), effs) <- visitExpr ctx TUnknown e

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
              (e'', efs) <- visitExpr ctx (typeToPType t) $ snd $ setters !! i
              e''' <- implicitCast ctx e'' t
              modVar setterExprs $ updateAt i $ const $ Just (e''', efs)
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
    let setterExprList = fst <$> setterExprs'
    pure ((H.EUpdate e' setterExprList updatePart, lhsType, sr), mconcat $ effs : (snd <$> setterExprs'))
  _ -> undefined

visitEExplicitType :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEExplicitType ctx _ (theExpr, _) = case theExpr of
  A.EExplicitType e t -> do
    t' <- visitTypeExpr ctx t
    (e', ef) <- visitExpr ctx (typeToPType t') e
    e'' <- implicitCast ctx e' t'
    pure (e'', ef)
  _ -> undefined

visitEAs :: forall m. (MonadTc m) => Ctx -> PType -> A.Expr -> m (H.Expr, HashSet H.Type)
visitEAs ctx _ (theExpr, sr) = case theExpr of
  A.EAs e t -> do
    toType <- visitTypeExpr ctx t
    (e'@(_, actType, _), ef) <- visitExpr ctx TUnknown e
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
    pure (e'', ef)
  _ -> undefined

getTDef :: (MonadTc m, HasCallStack) => SrcRange -> H.Type -> m H.TDef
getTDef sr t = case t of
  H.TNamed fqn _ -> do
    let pkg = tFqnToPkg fqn
    -- Look up the type definition
    pkg' <- getDepOrThisPkg pkg
    getTDefMaybe pkg' fqn <&> must
  _ -> throw sr "Not a named type"

visitStmt :: (MonadTc m) => Var m Ctx -> PType -> A.Stmt -> m (H.Stmt, HashSet H.Type)
visitStmt ctxVar typeHint (astStmt, sr) = case astStmt of
  A.SLet destr astTypeExprMaybe astExpr -> do
    ctx <- getVar ctxVar

    typeMaybe <- forM astTypeExprMaybe $ visitTypeExpr ctx
    let typeHint' = case typeMaybe of Just x -> typeToPType x; _ -> TUnknown

    (e', efs) <- visitExpr ctx typeHint' astExpr
    e''@(_, t, _) <- case typeMaybe of Just x -> implicitCast ctx e' x; _ -> pure e'

    d <- visitDestructure ctxVar t destr
    pure ((H.SLet d e'', sr), efs)
  A.SRecLet name astTypeExpr astExpr -> do
    ctx <- getVar ctxVar

    explicitType <- visitTypeExpr ctx astTypeExpr
    let typeHint' = typeToPType explicitType

    uid <- mkLocalVarUid
    let ctx' = ctx {variables = Variable False name uid explicitType ctx.closureDepth : ctx.variables}
    setVar ctxVar ctx'

    (e', efs) <- visitExpr ctx' typeHint' astExpr
    e'' <- implicitCast ctx' e' explicitType

    pure ((H.SRecLet name uid e'', sr), efs)
  A.SExpr astExpr -> do
    ctx <- getVar ctxVar
    (e', ef) <- visitExpr ctx typeHint (astExpr, sr)
    pure ((H.SExpr e', sr), ef)
  A.SWhen astCondExpr astThenExpr -> do
    ctx <- getVar ctxVar
    (condExpr@(_, shouldBeBool, _), ef0) <- visitExpr ctx boolHint astCondExpr
    unless (shouldBeBool == boolType)
      $ throw astCondExpr ("Condition type must be Bool, got " <> typeToText shouldBeBool)

    (thenExpr, ef1) <- visitExpr ctx TUnknown astThenExpr

    pure ((H.SWhen condExpr thenExpr, sr), ef0 <> ef1)
  A.SAssign n@(name, nameSr) rhs -> do
    ctx <- getVar ctxVar
    var <- case findLocalVarByName ctx name of
      Just x -> pure x
      _ -> throw nameSr $ "No such variable: " <> un name
    unless var.isMutable $ throw nameSr "Cannot assign to immutable variable"

    (rhs', rhsEffs) <- visitExpr ctx (typeToPType var.typ) rhs

    rhs'' <- implicitCast ctx rhs' var.typ

    let effs =
          if var.closureDepth < ctx.closureDepth
            then
              let l = H.TLifetime var.closureDepth
                  mutEff = H.TNamed (TFqn "#builtins/:MutatesVars") [l]
               in HS.insert mutEff rhsEffs
            else
              rhsEffs

    pure ((H.SAssign var.uid n rhs'', sr), effs)
  A.SForEach {destr, inExpr, bodyExpr} -> do
    ctx <- getVar ctxVar

    (inExpr'@(_, inType, _), effs1) <- visitExpr ctx TUnknown inExpr

    iterInnerType <- case inType of
      H.TNamed (TFqn "#builtins/:Iter") [t] -> pure t
      _ -> throw inExpr $ "Expected Iter type, got " <> typeToText inType

    let varType = iterInnerType

    ctxVar' <- newVar ctx
    destr' <- visitDestructure ctxVar' varType destr
    ctx' <- getVar ctxVar'

    label <- mkLocalVarUid

    (bodyExpr'@(_, bodyType, _), effs2) <- visitExpr ctx' {inLoop = Just label} unitHint bodyExpr

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

    pure ((s', sr), effs1 <> effs2)
  A.SLoop e -> do
    ctx <- getVar ctxVar
    label <- mkLocalVarUid
    (e', ef) <- visitExpr (ctx {inLoop = Just label}) TUnknown e
    pure ((H.SLoop e' label, sr), ef)
