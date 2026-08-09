-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Generics where

import Control.Monad (forM, forM_, unless)
import Data.HashSet qualified as HS
import Data.List (elemIndex)
import Data.Maybe (isJust)
import Front.Hir qualified as H
import Front.HirFns (typeToText)
import Front.Tc.Error (MonadTcError (throw))
import Front.Tc.PType
import Front.Tc.Show (pTypeToText)
import Front.Tc.State
import Front.TypeKind
import MhPrelude
import Names
import SrcLoc (SrcRange)
import Vars

mkGenParams :: (MonadTc m) => Fqn -> [(TypeKind, TNameL)] -> m [H.GenParam]
mkGenParams typeFqn gArgs = forM gArgs $ \(k, n@(TName n', sr)) -> do
  let fqn = TFqn $ un typeFqn <> "$" <> n'
  let t = H.TNamed fqn []
  addTDef fqn $ H.TDef n fqn [] t False k True False
  pure $ H.GenParam fqn sr t k

-- Replaces generic type parameters with concrete types throughout a type
substituteGenerics :: [(TFqn, H.Type)] -> H.Type -> H.Type
substituteGenerics [] t = t
substituteGenerics gParams genType =
  let f = substituteGenerics gParams
   in case genType of
        H.TFunc ps r e -> H.TFunc (ps <&> f) (f r) (f e)
        H.TTuple ts -> H.TTuple $ ts <&> f
        H.TNamed fqn gArgs -> case lookup fqn gParams of
          Nothing -> H.TNamed fqn $ gArgs <&> f
          Just t -> assert (null gArgs) t
        H.TEffect es ->
          H.TEffect
            $ HS.fromList
            $ flip concatMap (toList es)
            $ \e -> case f e of e'@(H.TNamed {}) -> [e']; H.TEffect xs -> toList xs; _ -> undefined
        H.TLifetime _ -> genType

-- Converts a concrete type to a partial type, substituting in hints for generic parameters
genericTypeToPType :: [(TFqn, PType)] -> H.Type -> PType
genericTypeToPType gParams t =
  let f = genericTypeToPType gParams
   in case t of
        H.TFunc ps r e -> TFuncP (ps <&> f) (f r) (f e)
        H.TTuple ts -> TTupleP $ ts <&> f
        H.TNamed fqn gArgs -> case lookup fqn gParams of
          Nothing -> TNamedP fqn $ gArgs <&> f
          Just x -> x
        H.TEffect es -> TEffectP $ HS.fromList $ f <$> toList es
        H.TLifetime _ -> TUnknown

tryCheckGenArgKinds :: (MonadTc m) => [(H.GenParam, (H.Type, SrcRange))] -> m (Either (Text, SrcRange) ())
tryCheckGenArgKinds xs = do
  errMaybe <- newVar Nothing
  forM_ xs $ \(gp, (t, sr)) -> do
    let shouldBe k =
          if gp.kind == k
            then pure ()
            else do
              isErr <- getVar errMaybe <&> isJust
              unless isErr
                $ setVar errMaybe
                $ Just ("Expected type kind " <> tShow gp.kind <> ", got " <> tShow k, sr)
    case t of
      H.TEffect {} -> shouldBe EffectType
      H.TLifetime _ -> shouldBe AbstractType
      H.TFunc {} -> shouldBe MonoType
      H.TTuple {} -> shouldBe MonoType
      H.TNamed fqn _ -> do
        let pkg = tFqnToPkg fqn
        (thisPkg, thisPkg') <- getThisPkg
        pkg' <- if thisPkg == pkg then pure thisPkg' else getDepPkg pkg
        tDef <- getTDefMaybe pkg' fqn <&> must
        shouldBe tDef.typeKind
  getVar errMaybe <&> \case Just e -> Left e; _ -> Right ()

checkGenArgKinds :: (MonadTc m) => [(H.GenParam, (H.Type, SrcRange))] -> m ()
checkGenArgKinds xs =
  tryCheckGenArgKinds xs >>= \case
    Left (e, sr) -> throw sr e
    _ -> pure ()

inferGenericArgs ::
  (MonadTc m) =>
  [TFqn] ->
  [H.GenParam] ->
  PType ->
  H.Type ->
  SrcRange ->
  m [H.Type]
inferGenericArgs ignored gps hint t sr = do
  xs <- tryInferGenericArgs ignored gps hint t sr
  case xs of Right x -> pure x; Left e -> throw sr e

tryInferGenericArgs ::
  (MonadTc m) =>
  [TFqn] ->
  [H.GenParam] ->
  PType ->
  H.Type ->
  SrcRange ->
  m (Either Text [H.Type])
tryInferGenericArgs ignored gps hint t sr = do
  errOrHints <- tryInferGenericArgsHints ignored gps hint t sr
  case errOrHints of
    Left e -> pure $ Left e
    Right hints ->
      case forM hints pTypeToType of
        Just x -> do
          tryCheckGenArgKinds (zip gps x <&> \(p, t') -> (p, (t', sr))) <&> \case
            Left (e, _) -> Left e
            Right _ -> Right x
        _ ->
          pure
            $ Left
            $ "Unable to infer generic type "
            <> typeToText t
            <> " from partial type information "
            <> pTypeToText hint

inferGenericArgsHints ::
  (MonadVars m, MonadTcError m) =>
  [TFqn] ->
  [H.GenParam] ->
  PType ->
  H.Type ->
  SrcRange ->
  m [PType]
inferGenericArgsHints ignored gps hint t sr = do
  xs <- tryInferGenericArgsHints ignored gps hint t sr
  case xs of Right x -> pure x; Left e -> throw sr e

-- Infers concrete types for generic parameters by comparing a partial type hint with a concrete type structure
-- Returns inferred types or throws if inference fails
tryInferGenericArgsHints ::
  (MonadVars m) =>
  [TFqn] ->
  [H.GenParam] ->
  PType ->
  H.Type ->
  SrcRange ->
  m (Either Text [PType])
tryInferGenericArgsHints ignored gps hint t sr = do
  r <- newVar $ replicate (length gps) TUnknown
  errFlag <- newVar Nothing
  tryInferGenericArgsHints' errFlag ignored (gps <&> (.fqn)) r sr hint t
  errFlag' <- getVar errFlag
  case errFlag' of
    Just x -> pure $ Left x
    _ -> Right <$> getVar r

tryInferGenericArgsHints' ::
  (MonadVars m) =>
  Var m (Maybe Text) ->
  [TFqn] ->
  [TFqn] ->
  Var m [PType] ->
  SrcRange ->
  PType ->
  H.Type ->
  m ()
tryInferGenericArgsHints' errFlag ignored gps gpTypes sr hint t = case (hint, t) of
  (TFuncP ps r e, H.TFunc ps' r' e') -> do
    forM_ (zip ps ps') $ uncurry $ tryInferGenericArgsHints' errFlag ignored gps gpTypes sr
    tryInferGenericArgsHints' errFlag ignored gps gpTypes sr r r'
    tryInferGenericArgsHints' errFlag ignored gps gpTypes sr e e'
  (TTupleP ts, H.TTuple ts') ->
    forM_ (zipList2 ts ts') $ uncurry $ tryInferGenericArgsHints' errFlag ignored gps gpTypes sr
  (_, H.TNamed (TFqn "#builtins/:Unreachable") _) -> pure ()
  (_, H.TNamed (TFqn "#builtins/:Any") _) -> pure ()
  (_, H.TNamed fqn []) | fqn `elem` ignored -> pure ()
  (_, H.TNamed fqn []) | fqn `elem` gps -> do
    let idx = must $ elemIndex fqn gps
    modVar gpTypes $ \xs -> take idx xs <> [hint <> xs !! idx] <> drop (idx + 1) xs
  (TNamedP fqn as, H.TNamed fqn' as')
    | fqn == fqn' ->
        forM_ (zip as as') $ uncurry $ tryInferGenericArgsHints' errFlag ignored gps gpTypes sr
  (TEffectP es, H.TEffect es')
    | HS.size es == 1 && HS.size es' == 1 ->
        tryInferGenericArgsHints' errFlag ignored gps gpTypes sr (must $ head $ toList es) (must $ head $ toList es')
  (TEffectP es, H.TEffect es')
    | HS.size es == 0 && HS.size es' == 1 ->
        tryInferGenericArgsHints' errFlag ignored gps gpTypes sr hint (must $ head $ toList es')
  (TEffectP _, H.TEffect _) -> pure ()
  (TUnknown, _) -> pure ()
  _ ->
    setVar errFlag
      $ Just
      $ "Incorrect type while inferring generic type "
      <> typeToText t
      <> " from partial type information "
      <> pTypeToText hint
