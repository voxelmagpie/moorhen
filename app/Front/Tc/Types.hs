-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Types where

import Control.Monad (forM, unless, void, when)
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Maybe (isNothing)
import Data.Text qualified as T
import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.HirFns (typeToText)
import Front.Tc.Context
import Front.Tc.Error (MonadTcError (throw))
import Front.Tc.Generics
import Front.Tc.Inputs
import Front.Tc.Names
import Front.Tc.PType
import Front.Tc.State
import {-# SOURCE #-} Front.Tc.Traits (findTraitImpls')
import Front.TypeKind (TypeKind (EffectType, MonoType))
import GHC.Stack (HasCallStack)
import MhPrelude
import Names
import SrcLoc (SrcRange)

-- Creates an error message comparing expected vs actual types
mkExActTypeError :: H.Type -> H.Type -> Text
mkExActTypeError ex act = "Expected " <> typeToText ex <> ", got " <> typeToText act

implicitCast :: (MonadTc m) => Ctx -> H.Expr -> H.Type -> m H.Expr
implicitCast ctx e@(_, from, sr) to = do
  let errMsg = "Incompatible types\nExpected " <> typeToText to <> ", got " <> typeToText from
  if from == to
    then pure e
    else case (from, to) of
      (H.TFunc ps r ef, H.TFunc ps' r' ef') | ps == ps' && r == r' && ef `effectsSubsetOf` ef' -> do
        pure (H.EImplicitCast e, to, sr)
      (H.TNamed (TFqn "#builtins/:Unreachable") _, _) ->
        pure (H.EImplicitCast e, to, sr)
      (H.TNamed (TFqn "#builtins/:I32") _, H.TNamed (TFqn "#builtins/:Int") _) ->
        pure (H.ESignExtendInt e, to, sr)
      (H.TNamed (TFqn "#builtins/:I32") _, H.TNamed (TFqn "#builtins/:Real") _) ->
        pure (H.EIntToF64 e, to, sr)
      (H.TNamed (TFqn "#builtins/:Int") _, H.TNamed (TFqn "#builtins/:Real") _) ->
        pure (H.EIntToF64 e, to, sr)
      (_, H.TNamed toFqn toGenArgs) -> do
        let pkg = tFqnToPkg toFqn
        pkg' <- getDepOrThisPkg pkg
        tDef <- getTDefMaybe pkg' toFqn <&> must
        when (tDef.tDefType /= H.IsTrait') $ throw sr errMsg
        let whs = [(from, List1 (toFqn, toGenArgs) [])]
        xs <- findTraitImpls' ctx whs sr
        pure (H.ECastToTraitType e (snd $ (xs !! 0) !! 0), to, sr)
      _ -> throw sr errMsg

implicitCastHint :: H.Expr -> PType -> H.Expr
implicitCastHint e@(_, from, sr) to = case (from, to) of
  (H.TNamed (TFqn "#builtins/:Unreachable") _, _) ->
    case pTypeToType to of
      Just t -> (H.EImplicitCast e, t, sr)
      _ -> e
  (H.TNamed (TFqn "#builtins/:I32") _, TNamedP x@(TFqn "#builtins/:Int") _) ->
    (H.ESignExtendInt e, H.TNamed x [], sr)
  (H.TNamed (TFqn "#builtins/:I32") _, TNamedP x@(TFqn "#builtins/:Real") _) ->
    (H.EIntToF64 e, H.TNamed x [], sr)
  (H.TNamed (TFqn "#builtins/:Int") _, TNamedP x@(TFqn "#builtins/:Real") _) ->
    (H.EIntToF64 e, H.TNamed x [], sr)
  _ -> e

effectsSubsetOf :: H.Type -> H.Type -> Bool
effectsSubsetOf l r =
  let l' = case l of H.TEffect x -> x; _ -> HS.singleton l
      r' = case r of H.TEffect x -> x; _ -> HS.singleton r
   in l' `HS.isSubsetOf` r'

-- True if the type contains the effect anywhere, e.g. in a function within a record
typeContainsMutVarsEffect :: H.Type -> Bool
typeContainsMutVarsEffect = \case
  H.TFunc ps r ef -> do
    let ps'' = any typeContainsMutVarsEffect ps
    let r'' = typeContainsMutVarsEffect r
    let ef'' = typeContainsMutVarsEffect ef
    ps'' || r'' || ef''
  H.TTuple ts ->
    any typeContainsMutVarsEffect ts
  H.TNamed fqn _ | un fqn == "#builtins/:MutatesVars" -> True
  H.TNamed _ gArgs ->
    any typeContainsMutVarsEffect gArgs
  H.TEffect efs -> any typeContainsMutVarsEffect efs
  H.TLifetime _ -> False

-- Visits a type definition (first phase), handles type aliases
visitTDef :: (MonadTc m) => Ctx -> A.TDef -> m (TFqn, H.TDef)
visitTDef outerCtx astTDef = do
  assertM $ isNothing outerCtx.block
  assertM $ null outerCtx.genParams

  let name = fst astTDef.name
  let isBuiltin = astTDef.tDef == A.BuiltinTypeDecl
  let fqn = TFqn $ un outerCtx.namespace <> ":" <> un name
  (_, thisPkg) <- getThisPkg

  getTDefMaybe thisPkg fqn >>= \case
    Just x ->
      pure (fqn, x)
    _ -> do
      gps <- mkGenParams (Fqn $ un fqn) astTDef.genParams

      d <- case astTDef.tDef of
        A.TypeAliasDecl astType -> do
          let ctx =
                outerCtx
                  { fqn = Just $ Right fqn,
                    genParams = gps,
                    tNameToGp = HM.fromList $ zip ((snd >>> fst) <$> astTDef.genParams) gps,
                    thisDefType = Nothing
                  }
          t <- visitTypeExpr ctx astType
          let k = case t of H.TEffect {} -> EffectType; _ -> MonoType
          pure $ H.TDef astTDef.name fqn gps t k H.IsAlias
        _ -> do
          when isBuiltin $ do
            let knownTypes = ["Real", "I32", "Int", "Bool", "Unit", "String", "Lazy", "Any", "Vec", "Unreachable"]
            let nsPrefix = "#builtins/:"
            unless (nsPrefix `T.isPrefixOf` un fqn && T.drop (T.length nsPrefix) (un fqn) `elem` knownTypes)
              $ throw astTDef.name
              $ "Unknown builtin type: "
              <> un name

          let t = H.TNamed fqn $ gps <&> (.type')
          let k = if astTDef.isEffect then EffectType else MonoType
          let isTrait = case astTDef.tDef of A.Trait {} -> True; _ -> False
          let typ = if isBuiltin then H.IsBuiltin else if isTrait then H.IsTrait' else H.IsDataDef
          pure $ H.TDef astTDef.name fqn gps t k typ

      addTDef fqn d
      pure (fqn, d)

-- Visits a type definition (second phase)
-- Processes data constructors and builds complete type definition
-- Handles builtin types and regular type declarations, not type aliases or impl blocks
visitDataTypeDef :: (MonadTc m) => Ctx -> A.TDef -> m (TFqn, H.DataTypeDef)
visitDataTypeDef outerCtx astTDef = do
  (fqn, tDef) <- visitTDef outerCtx astTDef
  (_, thisPkg) <- getThisPkg
  getDataTypeDefMaybe thisPkg fqn >>= \case
    Just d ->
      pure (fqn, d)
    _ -> do
      let ctx =
            outerCtx
              { fqn = Just $ Right fqn,
                genParams = tDef.genParams,
                tNameToGp = HM.fromList $ zip ((snd >>> fst) <$> astTDef.genParams) tDef.genParams,
                thisDefType = Just tDef.selfType
              }
      d <- case astTDef.tDef of
        A.TypeAliasDecl _ ->
          error "Aliases handled in visitTDef"
        A.TypeDecl astDataCons _ -> do
          conss <- forM astDataCons $ \(A.DataCons dConsName fieldsOrRecord) -> case fieldsOrRecord of
            A.RecordFields fields -> do
              types <- forM fields $ \((n, _), t) -> (n,) <$> visitTypeExpr ctx t
              pure $ H.DataCons dConsName $ H.RecordFields types
            A.TupleFields fields -> do
              types <- forM fields $ \t -> visitTypeExpr ctx t
              pure $ H.DataCons dConsName $ H.TupleFields types
          let typeIsEnum dataCons = flip all dataCons $ \case H.DataCons _ (H.TupleFields []) -> True; _ -> False
          pure $ H.DataTypeDef tDef conss $ typeIsEnum conss
        A.BuiltinTypeDecl -> undefined
        A.Module {} -> undefined
        A.Trait {} -> undefined
      addDataTypeDef fqn d
      pure (fqn, d)

-- Converts AST type expressions to HIR types
visitTypeExpr :: (MonadTc m) => Ctx -> A.TypeExpr -> m H.Type
visitTypeExpr ctx (astTypeExpr, sr) = case astTypeExpr of
  A.TFunc ps r astEffects -> do
    ps' <- forM ps $ visitTypeExpr ctx
    r' <- visitTypeExpr ctx r
    e <- visitTypeExpr ctx (A.TEffect astEffects, sr)
    pure $ H.TFunc ps' r' e
  A.TUnit -> do
    (thisPkgName, _) <- getThisPkg
    when (un thisPkgName == "#builtins") $ do
      void $ visitTypeExpr ctx (A.TNamed (TName "Unit", sr) [], sr)
    pure $ H.TNamed (TFqn "#builtins/:Unit") []
  A.TTuple ts -> do
    ts' <- forM ts $ visitTypeExpr ctx
    pure $ H.TTuple ts'
  A.TEffect astEffects -> do
    es <- forM astEffects $ \e -> do
      t <- visitTypeExpr ctx e
      verifyEffectAndConvertToList t >>= \case
        Just x -> pure x
        _ -> throw sr $ "Type is not an effect: " <> typeToText t
    pure $ H.TEffect $ HS.fromList $ concat es
  A.TNamed (TName "Self", _) genArgs -> do
    unless (null genArgs) $ throw sr "Self type does not take generic arguments"
    case ctx.block of
      Just (_, selfType) -> pure selfType
      _ -> throw sr "Self type is only valid within impl or trait blocks"
  A.TNamed name genArgs -> do
    genArgs' <- forM genArgs $ visitTypeExpr ctx
    lookupTypeName ctx name >>= \case
      NlAstNamespace {} ->
        throw sr "Expected type, got namespace"
      NlNamespace {} ->
        throw sr "Expected type, got namespace"
      NlGenericType t -> do
        unless (null genArgs)
          $ throw sr "Cannot apply generics to type (higher-kinded types are not supported)"
        pure t
      NlAstTypeDef outerCtx astTDef -> do
        case astTDef.tDef of
          A.TypeAliasDecl {} -> pure ()
          A.TypeDecl {} -> pure ()
          A.BuiltinTypeDecl {} -> pure ()
          A.Trait {} -> pure ()
          A.Module {} -> throw sr "Expected type, got module"
        (tFqn, tDef) <- visitTDef outerCtx astTDef
        unless (length tDef.genParams == length genArgs')
          $ throw sr "Wrong number of generic arguments for type"
        checkGenArgKinds $ zip tDef.genParams $ zip genArgs' $ snd <$> genArgs
        if tDef.tDefType == H.IsAlias
          then do
            let gps = tDef.genParams <&> (.fqn)
            pure $ substituteGenerics (zip gps genArgs') tDef.selfType
          else
            pure $ H.TNamed tFqn genArgs'
      NlTypeDef pkgName (H.TNameExport {fqn, typ}) -> do
        case typ of
          H.IsTypeDef -> pure ()
          H.IsTrait _ -> pure ()
          H.IsModule _ -> throw sr "Expected type, got module"
        pkg <- getDepPkg pkgName
        tDef <- getTDefMaybe pkg fqn <&> must
        unless (length tDef.genParams == length genArgs')
          $ throw sr "Wrong number of generic arguments for type"
        checkGenArgKinds $ zip tDef.genParams $ zip genArgs' $ snd <$> genArgs
        if tDef.tDefType == H.IsAlias
          then do
            let gps = tDef.genParams <&> (.fqn)
            pure $ substituteGenerics (zip gps genArgs') tDef.selfType
          else
            pure $ H.TNamed fqn genArgs'
  A.TLifetime name -> do
    case findLocalVarByName ctx name of
      Just var -> do
        pure $ H.TLifetime var.closureDepth
      _ -> throw sr $ "No such local variable: " <> un name

verifyEffectAndConvertToList :: (MonadTc m, HasCallStack) => H.Type -> m (Maybe [H.Type])
verifyEffectAndConvertToList t = case t of
  H.TEffect e -> do
    xs <- forM (toList e) verifyEffectAndConvertToList
    pure $ sequence xs <&> concat
  H.TNamed fqn' _ -> do
    let pkg = tFqnToPkg fqn'
    pkg' <- getDepOrThisPkg pkg
    tDef <- getTDefMaybe pkg' fqn' <&> must
    pure $ if tDef.typeKind == EffectType then Just [t] else Nothing
  _ -> pure Nothing

getTDef2 :: (MonadTc m, HasCallStack) => Ctx -> SrcRange -> H.Type -> m (H.DataTypeDef, (TFqn, [H.Type]))
getTDef2 ctx sr t = case t of
  H.TNamed fqn genArgs -> do
    let pkg = tFqnToPkg fqn
    -- Look up the type definition
    (thisPkg, _) <- getThisPkg
    pkg' <- getDepOrThisPkg pkg
    tDef <- getTDefMaybe pkg' fqn <&> must
    assertM $ tDef.typeKind == MonoType
    when (tDef.tDefType /= H.IsDataDef) $ throw sr $ un (tFqnToName fqn) <> " is not a data type"
    dataTypeDef <-
      if thisPkg == pkg
        then do
          let ns = tFqnToNamespace fqn
          let astAndImports@(ast, _) = must $ HM.lookup ns ctx.tcIn.allAsts
          let ctx' = mkFileCtx ns astAndImports ctx.tcIn
          let astTDef = must $ HM.lookup (fst tDef.name) ast.tDefs
          visitDataTypeDef ctx' astTDef <&> snd
        else
          getDataTypeDefMaybe pkg' fqn <&> must
    pure (dataTypeDef, (fqn, genArgs))
  _ -> throw sr "Not a named type"

findDConsInType :: (MonadTc m) => TNameL -> H.DataTypeDef -> m (H.DataCons, Int)
findDConsInType (name, nameSr) dataTypeDef =
  case findWithIndex (\(H.DataCons (n, _) _) -> n == name) $ toList dataTypeDef.dataCons of
    Just y -> pure y
    _ -> throw nameSr $ "No such data constructor '" <> un name <> "' in type " <> un (fst dataTypeDef.t1.name)

getDataConsFromType :: (MonadTc m) => Ctx -> H.Type -> TNameL -> m (H.DataConsInfo, H.Type, H.Fields)
getDataConsFromType ctx t name@(_, nameSr) = do
  (dataTypeDef, (_, genArgs')) <- getTDef2 ctx nameSr t
  (H.DataCons _ dcContents, dcIdx) <- findDConsInType name dataTypeDef
  let gpMap = zip dataTypeDef.t1.genParams genArgs' <&> \(gp, a) -> (gp.fqn, a)
  let tFqn = dataTypeDef.t1.fqn
  let dcFieldTypes = mkDConsFieldTypes dcContents gpMap
  let isProduct = length dataTypeDef.dataCons == 1
  let isFn = case dcContents of H.TupleFields xs -> notNull xs; H.RecordFields {} -> False
  pure (H.DataConsInfo tFqn (fst name) dcIdx isFn isProduct dataTypeDef.isEnumType, t, dcFieldTypes)

mkDConsFieldTypes :: H.Fields -> [(TFqn, H.Type)] -> H.Fields
mkDConsFieldTypes dcContents gpMap =
  case dcContents of
    H.TupleFields xs -> H.TupleFields $ xs <&> substituteGenerics gpMap
    H.RecordFields xs -> H.RecordFields $ xs <&> second (substituteGenerics gpMap)

getDataCons' :: (MonadTc m) => Ctx -> PType -> TNameL -> (TFqn -> H.DataTypeDef -> m a) -> m a
getDataCons' ctx hint name@(_, nameSr) f = do
  let h = case hint of TFuncP {ret} -> ret; _ -> hint
  case h of
    TNamedP fqn _ -> do
      let pkgName = tFqnToPkg fqn
      (thisPkg, thisPkg') <- getThisPkg
      pkg <- if thisPkg == pkgName then pure thisPkg' else getDepPkg pkgName
      tDef <- getTDefMaybe pkg fqn <&> must
      when (tDef.tDefType /= H.IsDataDef) $ throw nameSr $ un (tFqnToName fqn) <> " is not a data type"
      dataTypeDef <- getDataTypeDefMaybe pkg fqn <&> must
      f fqn dataTypeDef
    _ -> do
      -- Try looking up the type name instead
      lookupTypeName ctx name >>= \case
        NlAstNamespace {} -> throw nameSr "Expected type, got namespace"
        NlNamespace {} -> throw nameSr "Expected type, got namespace"
        NlGenericType _ -> throw nameSr "Cannot initialise generic types"
        NlAstTypeDef outerCtx astTDef -> do
          case astTDef.tDef of
            A.BuiltinTypeDecl -> throw nameSr "Builtin types cannot be initialised in this way"
            _ -> pure ()
          (tFqn, dataTypeDef) <- visitDataTypeDef outerCtx astTDef
          f tFqn dataTypeDef
        NlTypeDef pkgName (H.TNameExport {fqn, typ}) -> do
          unless (typ == H.IsTypeDef) $ throw nameSr "Not a type"
          pkg <- getDepPkg pkgName
          tDef <- getTDefMaybe pkg fqn <&> must
          when (tDef.tDefType == H.IsBuiltin) $ throw nameSr "Builtin types cannot be initialised in this way"
          dataTypeDef <- getDataTypeDefMaybe pkg fqn <&> must
          f fqn dataTypeDef

-- Resolves a data constructor by name
-- Infers generic arguments and returns constructor info, type, and field types
getDataCons :: (MonadTc m) => Ctx -> PType -> TNameL -> [A.TypeExpr] -> m (H.DataConsInfo, H.Type, H.Fields)
getDataCons ctx hint name@(_, nameSr) astGenArgs = do
  getDataCons' ctx hint name $ \tFqn dataTypeDef -> do
    (H.DataCons _ dcContents, dcIdx) <- findDConsInType name dataTypeDef
    let gps = dataTypeDef.t1.genParams
    (t, gpMap) <- case astGenArgs of
      [] -> do
        let gps' = gps <&> (.fqn)
        let genericType = case dcContents of
              H.TupleFields xs | notNull xs -> H.TFunc xs dataTypeDef.t1.selfType (H.TEffect def)
              _ -> dataTypeDef.t1.selfType
        gpTypes <- inferGenericArgs [] gps hint genericType nameSr
        let t = substituteGenerics (zip gps' gpTypes) dataTypeDef.t1.selfType
        pure (t, zip gps' gpTypes)
      _ -> do
        -- TODO Merge this with the code for vname lookup?
        unless (length astGenArgs == length gps) $ throw nameSr "Wrong number of generic arguments"
        genArgs' <- forM astGenArgs $ visitTypeExpr ctx
        checkGenArgKinds $ zip gps $ zip genArgs' $ snd <$> astGenArgs
        let gpMap = zip gps genArgs' <&> \(gp, a) -> (gp.fqn, a)
        let t = substituteGenerics gpMap dataTypeDef.t1.selfType
        pure (t, gpMap)
    let dcFieldTypes = mkDConsFieldTypes dcContents gpMap
    let isProduct = length dataTypeDef.dataCons == 1
    let isFn = case dcContents of H.TupleFields xs -> notNull xs; H.RecordFields {} -> False
    pure (H.DataConsInfo tFqn (fst name) dcIdx isFn isProduct dataTypeDef.isEnumType, t, dcFieldTypes)
