-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.PType where

import Data.HashSet qualified as HS
import Front.Hir
import Front.Hir qualified as H
import MhPrelude
import Names

-- Partial Type
data PType
  = TUnknown
  | TFuncP {params :: [PType], ret :: PType, eff :: PType}
  | TTupleP (List2 PType)
  | TNamedP TFqn [PType]
  | TEffectP (HashSet PType)
  | TLifetimeP Int
  deriving (Show, Generic, Eq, Hashable)

typeToPType :: Type -> PType
typeToPType = \case
  TFunc ps r e -> TFuncP (typeToPType <$> ps) (typeToPType r) (typeToPType e)
  TTuple ts -> TTupleP $ typeToPType <$> ts
  TNamed f ts -> TNamedP f (typeToPType <$> ts)
  TEffect es -> TEffectP $ HS.fromList $ typeToPType <$> toList es
  TLifetime x -> TLifetimeP x

pTypeToType :: PType -> Maybe H.Type
pTypeToType = \case
  TUnknown -> Nothing
  TFuncP ps r e -> do
    ps' <- mapM pTypeToType ps
    r' <- pTypeToType r
    e' <- pTypeToType e
    pure $ TFunc ps' r' e'
  TTupleP ts -> mapM pTypeToType ts <&> TTuple
  TNamedP fqn ts -> mapM pTypeToType ts <&> TNamed fqn
  TEffectP es -> mapM pTypeToType (toList es) <&> (HS.fromList >>> TEffect)
  TLifetimeP x -> pure $ H.TLifetime x

instance Semigroup PType where
  TUnknown <> x = x
  x <> TUnknown = x
  TTupleP xs <> TTupleP ys = TTupleP $ zipList2 xs ys <&> uncurry (<>)
  TFuncP ps r e <> TFuncP ps' r' e' =
    TFuncP
      (zip ps ps' <&> uncurry (<>))
      (r <> r')
      (e <> e')
  TNamedP fqn xs <> TNamedP fqn' ys
    | fqn == fqn' =
        TNamedP fqn $ zip xs ys <&> uncurry (<>)
  TEffectP xs <> TEffectP ys | null xs && null ys = TEffectP def
  TEffectP xs <> TEffectP ys
    | length xs == 1 && length ys == 1 =
        TEffectP $ HS.singleton $ must (head $ toList xs) <> must (head $ toList ys)
  _ <> _ = TUnknown

instance Monoid PType where
  mempty = TUnknown
