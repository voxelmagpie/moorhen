-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.HirFns where

import Control.Monad (forM)
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.HashTable.IO qualified as HT
import Data.Text qualified as T
import Front.Hir
import Front.TypeKind (TypeKind (AbstractType, EffectType, MonoType))
import MhPrelude
import Names
import TypeString

isGenericOverEffect :: [GenParam] -> Bool
isGenericOverEffect genParams = flip any genParams $ \gp -> gp.kind == EffectType

showHir :: Hir -> IO Text
showHir ir = do
  x' <- HT.toList ir.exports
  x <- forM x' $ \(ns, (vs, ts, _)) -> do
    vs' <- HT.toList vs
    ts' <- HT.toList ts
    pure (ns, (vs', ts'))
  ir' <- Hir' x <$> HT.toList ir.vDefs <*> HT.toList ir.vDefExpr <*> HT.toList ir.tDefs1 <*> HT.toList ir.dataTypeDefs
  pure $ tShow ir'

typeToText' :: Bool -> Type -> Text
typeToText' shorten =
  let f = typeToText' shorten
   in \case
        TFunc ps r e ->
          T.concat
            [ if length ps > 1 then "\\ " else "\\",
              T.intercalate ", " $ f <$> toList ps,
              " -> ",
              f r,
              " ",
              case e of TEffect {} -> ""; _ -> "@",
              f e
            ]
        TTuple ts -> "(" <> T.intercalate ", " (f <$> toList ts) <> ")"
        TNamed fqn [] -> if shorten then shortenFqn $ un fqn else un fqn
        TNamed fqn args -> (if shorten then shortenFqn (un fqn) else un fqn) <> "[" <> T.intercalate ", " (f <$> args) <> "]"
        TEffect es | HS.size es == 1 -> "@" <> T.concat (f <$> toList es)
        TEffect es -> "@(" <> T.intercalate "," (f <$> toList es) <> ")"
        TLifetime l -> "'" <> tShow l

typeToText :: Type -> Text
typeToText = typeToText' True

typeToTextFull :: Type -> TypeString
typeToTextFull = TypeString . typeToText' False

getTypeKind :: Type -> TypeKind
getTypeKind = \case
  TFunc {} -> MonoType
  TTuple {} -> MonoType
  TNamed {} -> MonoType
  TEffect {} -> EffectType
  TLifetime {} -> AbstractType

addTraitToWhereClauses :: Type -> TraitRef -> WhereClauses -> WhereClauses
addTraitToWhereClauses t r (WhereClauses xs) =
  case findWithIndex (\(t', _) -> t' == t) xs of
    Nothing -> WhereClauses $ (t, List1 r []) : xs
    Just ((_, traits), i)
      | r `elem` traits -> WhereClauses xs
      | otherwise -> WhereClauses $ updateAt i (second (list1Cons r)) xs

traitsListFromList :: [TraitRef] -> TraitsList
traitsListFromList = TraitsList . HM.fromList

traitRefToText :: TraitRef -> Text
traitRefToText (fqn, gArgs) =
  let name = un $ tFqnToName fqn
   in if null gArgs then name else name <> "[" <> T.intercalate ", " gArgs' <> "]"
  where
    gArgs' = gArgs <&> typeToText
