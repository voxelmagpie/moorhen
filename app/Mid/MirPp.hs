-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

-- MIR pretty printing functions
module Mid.MirPp where

import Data.HashTable.IO qualified as HT
import Data.List (sortOn)
import Data.Text qualified as T
import MhPrelude
import Mid.Mir
import Names (TextL)
import Strings

-- Pretty printing functions

ppMir :: Mir -> IO Text
ppMir mir = do
  vDefs <- HT.toList mir.vDefs
  pure $ T.concat $ un mir.name : "\n\n" : (sortOn (fst >>> un) vDefs <&> (snd >>> ppVDef))

ppVDef :: VDef -> Text
ppVDef v = T.concat [if v.isIterator then "iterator " else "let ", un v.fqn, " : ", ppType v.type', rhs, "\n\n"]
  where
    rhs = case v.exprMaybe of
      Just e -> " =\n\t" <> ppExpr e
      Nothing -> case v.value of
        Just c -> " =\n\t" <> ppConst c
        Nothing -> "" -- No value, e.g. a builtin or a definition with no body

ppType :: Type -> Text
ppType = \case
  TFunc ps r ef ia -> T.concat ["(\\", T.intercalate ", " (ppType <$> ps), " -> ", ppType r, ppEffects ef, if ia then " async" else "", ")"]
  TProduct ts -> "(" <> T.intercalate ", " (ppType <$> toList ts) <> ")"
  TSum ts -> T.concat ["(", T.intercalate " | " (ppType <$> toList ts), ")"]
  TInt -> "Int"
  TI32 -> "I32"
  TReal -> "Real"
  TUnit -> "()"
  TString -> "String"
  TVec t -> "Vec[" <> ppType t <> "]"
  TBool -> "Bool"
  TLazy t -> "Lazy[" <> ppType t <> "]"
  TAny -> "Any"
  TRecursive t -> "Rec[" <> ppType t <> "]"
  TIter t -> "Iter[" <> ppType t <> "]"

ppEffects :: Effects -> Text
ppEffects e
  | e.pure && e.noThrow = ""
  | otherwise = "@" <> T.intercalate ", " (["impure" | not e.pure] <> ["throws" | not e.noThrow])

ppConst :: Const -> Text
ppConst = \case
  CInt n -> tShow n
  CI32 n -> tShow n <> "_i32"
  CFloat t -> t
  CBool b -> tShow b
  CString s -> "\"" <> T.pack (filterString $ T.unpack s) <> "\""
  CVec cs -> "[" <> T.intercalate ", " (ppConst <$> cs) <> "]"
  CFn fqn -> un fqn

ppFn :: Fn -> Text
ppFn fn = T.concat ["\\", paramsStr, " -> ", bodyStr]
  where
    paramsStr = T.intercalate ", " $ fn.params <&> \(uid, n, t, _) -> ppVarWithNameL uid n <> " : " <> ppType t
    bodyStr = ppExpr fn.expr

ppExpr :: Expr -> Text
ppExpr (e, _) = case e of
  ELoadConst c -> ppConst c
  EVec es -> "[" <> T.intercalate ", " (ppExpr <$> es) <> "]"
  EVar uid n -> ppVarWithName uid n
  EGlobal fqn -> un fqn
  EClosure fn -> ppFn fn
  EFnCall f args ia _ -> ppExpr f <> "(" <> T.intercalate ", " (ppExpr <$> args) <> ")" <> if ia then " async" else ""
  EDoBlock stmts eMaybe -> T.concat ["{ ", T.concat (stmts <&> \s -> ppStmt s <> "; "), eMaybeStr, "}"]
    where
      eMaybeStr = case eMaybe of
        Just e' -> ppExpr e' <> " "
        Nothing -> ""
  EIf c t f _ -> T.concat ["(if ", ppExpr c, " then ", ppExpr t, " else ", ppExpr f, ")"]
  EProduct es -> "(" <> T.intercalate ", " (ppExpr <$> toList es) <> ")"
  ESum _ i e' -> "sum<" <> tShow i <> ">(" <> ppExpr e' <> ")"
  EUnreachable msg -> "unreachable(" <> tShow msg <> ")"
  EAnd a b -> "(" <> ppExpr a <> " and " <> ppExpr b <> ")"
  EOr a b -> "(" <> ppExpr a <> " or " <> ppExpr b <> ")"
  ETry {tryExpr, catch, finally} ->
    T.concat ["try ", ppExpr tryExpr, " ", catchesStr, finallyStr]
    where
      catchesStr = T.unwords $ toList catch <&> \(ts, uid, _, e') -> T.concat ["catch ", un ts, " ", ppVar uid, " -> ", ppExpr e']
      finallyStr = maybe "" (\e' -> " finally " <> ppExpr e') finally
  EThrow e' ts -> "throw " <> ppExpr e' <> " : " <> un ts
  EYield e' -> "yield " <> ppExpr e'
  EIndex e' i n -> ppExpr e' <> (case n of Just n' -> "." <> un n'; _ -> "." <> tShow i)
  ESumTypeActiveIndex e' -> "sumIndex(" <> ppExpr e' <> ")"
  ESumTypeGet e' -> "sumGet(" <> ppExpr e' <> ")"
  EBreak uid -> "break :" <> ppVar uid
  EContinue uid -> "continue :" <> ppVar uid
  EUnreachableCast e' _ -> "unreachableCast(" <> ppExpr e' <> ")"
  EAddFnEffects e' _ -> "addFnEffects(" <> ppExpr e' <> ")"
  ESignExtendInt e' -> "signExtend(" <> ppExpr e' <> ")"
  EIntToF64 e' -> "intToF64(" <> ppExpr e' <> ")"
  ECastNumber e' t -> "cast(" <> ppExpr e' <> " - to - " <> ppType t <> ")"

ppStmt :: Stmt -> Text
ppStmt (s, _) = case s of
  SLet uid nameMaybe mut e' -> T.concat ["let ", if mut then "mut " else "", ppVarWithNameL uid nameMaybe, " = ", ppExpr e']
  SRecLet uid nameMaybe e' -> T.concat ["let rec ", ppVarWithNameL uid nameMaybe, " = ", ppExpr e']
  SLetUninit uid t -> T.concat ["let uninit ", ppVar uid, " : ", ppType t]
  SExpr e' -> ppExpr e'
  SAssign uid nameMaybe e' -> T.concat [ppVarWithNameL uid nameMaybe, " = ", ppExpr e']
  SLoop e' label -> T.concat [ppVar label, ": loop { ", ppExpr e', " } "]
  SForEach {iterExpr, elemUid, elemNameMaybe, label, bodyExpr} ->
    T.concat [ppVar label, ": for ", ppVarWithNameL elemUid elemNameMaybe, " in ", ppExpr iterExpr, " { ", ppExpr bodyExpr, " }"]

ppVar :: LocalVarUid -> Text
ppVar uid = "$" <> tShow (un uid)

ppVarWithNameL :: LocalVarUid -> Maybe TextL -> Text
ppVarWithNameL uid nameMaybe = ppVarWithName uid (nameMaybe <&> fst)

ppVarWithName :: LocalVarUid -> Maybe Text -> Text
ppVarWithName uid nameMaybe = "$" <> tShow (un uid) <> maybe "" (\n -> " /* " <> n <> " */") nameMaybe
