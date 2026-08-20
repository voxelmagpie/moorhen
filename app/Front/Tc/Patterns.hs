-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Patterns where

import Control.Monad (forM, unless, when)
import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.Tc.Context
import Front.Tc.Error (MonadTcError (throw))
import Front.Tc.Generics (substituteGenerics)
import Front.Tc.State
import Front.Tc.Types
import MhPrelude
import Vars

-- Type checks a pattern in a case expression
-- Handles variable binding, wildcards, and data constructor patterns
-- Updates context with new variable bindings
visitPattern :: forall m. (MonadTc m) => Var m Ctx -> H.Type -> A.Pattern -> m H.Pattern
visitPattern ctxVar t (astPat, sr) = do
  case astPat of
    A.PIgnore -> pure (H.PIgnore, t, sr)
    A.PName name -> do
      uid <- mkLocalVarUid
      modVar ctxVar $ \ctx -> ctx {variables = Variable False (name, sr) uid t ctx.closureDepth : ctx.variables}
      pure (H.PName name uid, t, sr)
    A.PTuple ps -> do
      ts <- case t of
        H.TTuple ts | length ts == length ps -> pure ts
        H.TTuple _ -> throw sr "Wrong number of tuple elements"
        _ -> throw sr "Not a tuple"
      ps' <- forM (zip (toList ps) (toList ts)) $ \(p, t') -> visitPattern ctxVar t' p
      pure (H.PTuple (must $ listToList2 ps'), t, sr)
    A.PDataCons name ps -> do
      ctx <- getVar ctxVar
      (dcInfo, dataType, dcFieldTypes') <- getDataConsFromType ctx t name

      unless (t == dataType)
        $ throw sr
        $ "Pattern does not match case expr type\n"
        <> mkExActTypeError t dataType
      dcFieldTypes <- case dcFieldTypes' of
        H.TupleFields xs -> pure xs
        H.RecordFields _ -> throw sr "Expected tuple-like data constructor fields, got record"
      unless (length dcFieldTypes == length ps) $ throw sr "Wrong number of fields for data constructor"

      ps' <- forM (zip (toList ps) (toList dcFieldTypes)) $ \(p, t') -> visitPattern ctxVar t' p
      pure (H.PDataCons dcInfo ps', t, sr)
    A.PRecord name ps -> do
      ctx <- getVar ctxVar
      (dcInfo, dataType, dcFieldTypes') <- getDataConsFromType ctx t name
      unless (t == dataType)
        $ throw sr
        $ "Pattern does not match case expr type\n"
        <> mkExActTypeError t dataType
      dcFieldTypes <- case dcFieldTypes' of
        H.RecordFields xs -> pure xs
        H.TupleFields _ -> throw sr "Expected record data constructor fields, got list"

      ps' <- forM ps $ \((fieldName, fieldNameSr), astPtn) -> do
        fieldType <- case lookup fieldName $ toList dcFieldTypes of
          Just x -> pure x
          _ -> throw fieldNameSr $ "No such field: " <> un fieldName
        pure (astPtn, fieldType)
      ps'' <- forM ps' $ \(p, t') -> visitPattern ctxVar t' p
      pure (H.PRecord dcInfo $ zip (ps <&> (fst . fst)) ps'', t, sr)

visitDestructure :: (MonadTc m) => Var m Ctx -> H.Type -> A.Destructure -> m H.Destructure
visitDestructure ctxVar t (destr, sr) = case destr of
  A.DIgnore -> do
    pure (H.DIgnore, t, sr)
  A.DName name mut -> do
    uid <- mkLocalVarUid
    ctx <- getVar ctxVar
    setVar ctxVar $ ctx {variables = Variable mut (name, sr) uid t ctx.closureDepth : ctx.variables}
    pure (H.DName name uid mut, t, sr)
  A.DAs name mut d -> do
    uid <- mkLocalVarUid
    modVar ctxVar $ \ctx -> ctx {variables = Variable mut name uid t ctx.closureDepth : ctx.variables}
    d' <- visitDestructure ctxVar t d
    pure (H.DAs name uid mut d', t, sr)
  A.DTupleLike ds -> case t of
    H.TTuple ts -> do
      when (length ds /= length ts) $ throw sr "Wrong number of tuple elements"
      ds' <- forM (zipList2 ts (must $ listToList2 $ toList ds)) $ uncurry $ visitDestructure ctxVar
      pure (H.DTuple ds', t, sr)
    _ -> do
      ctx <- getVar ctxVar
      (dataTypeDef, (tFqn, genArgs)) <- getDataDefType ctx.tcIn sr t
      (name, ts) <- case dataTypeDef.dataCons of
        List1 (H.DataCons (name, _) (H.TupleFields xs)) []
          | notNull xs -> do
              let gpMap = zip dataTypeDef.t1.genParams genArgs <&> first (.fqn)
              let ts = xs <&> substituteGenerics gpMap
              pure (name, must $ listToList1 ts)
        _ -> throw sr "Expected a type of form data X(A, B, ...)"
      ds' <- forM (zipList1 ts ds) $ uncurry $ visitDestructure ctxVar
      let dCons = H.DataConsInfo tFqn name 0 True True dataTypeDef.isEnumType
      pure (H.DDataCons dCons ds', t, sr)
  A.DRecord fields -> do
    ctx <- getVar ctxVar
    (dataTypeDef, (tFqn, genArgs)) <- getDataDefType ctx.tcIn sr t
    (dConsName, dConsFields) <- case dataTypeDef.dataCons of
      List1 (H.DataCons (name, _) (H.RecordFields xs)) [] -> do
        let gpMap = zip dataTypeDef.t1.genParams genArgs <&> first (.fqn)
        let ts = xs <&> second (substituteGenerics gpMap)
        pure (name, toList ts)
      _ -> throw sr "Expected a record"

    fields' <- forM fields $ \((fieldName, nameSr), d) -> do
      fieldType <- case lookup fieldName dConsFields of
        Just x -> pure x
        _ -> throw nameSr $ "No such field '" <> un fieldName <> "'"
      d' <- visitDestructure ctxVar fieldType d
      pure (fieldName, d')

    let dCons = H.DataConsInfo tFqn dConsName 0 False True dataTypeDef.isEnumType
    pure (H.DRecord dCons fields', t, sr)
