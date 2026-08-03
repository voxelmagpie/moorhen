-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{- HLINT ignore "Use maybe" -}

-- AST Pretty printing functions
module Front.AstPp where

import Data.HashMap.Strict qualified as HM
import Data.Maybe (fromMaybe)
import Data.Text (intercalate, unlines, unwords)
import Data.Text qualified as T
import Front.Ast
import Front.TypeKind
import MhPrelude
import Names

-- Pretty printing functions

prettyPrint :: Ast -> Text
prettyPrint ast = T.concat [unlines $ prettyPrintVDef <$> HM.elems ast.vDefs, "\n", unlines $ prettyPrintTDef <$> HM.elems ast.tDefs, "\n"]

prettyPrintVDef :: VDef -> Text
prettyPrintVDef vDef =
  T.concat ["let ", prettyPrintGenParams vDef.genParams, un $ fst vDef.name, case vDef.op of Just (o, _) -> " " <> un o; _ -> "", t, wh, case vDef.expr of Just e -> " = " <> prettyPrintExpr e; _ -> ""]
  where
    t = case vDef.typeExpr of
      Just x -> " : " <> prettyPrintType x
      Nothing -> ""
    wh = prettyPrintWheres vDef.whereClauses

prettyPrintWheres :: WhereClauses -> Text
prettyPrintWheres =
  \case
    [] -> ""
    xs -> " where " <> T.intercalate "," (xs <&> mkWh)
  where
    mkWh (l, r) = prettyPrintType l <> " : " <> prettyPrintType r

prettyPrintGenParams :: [(TypeKind, TNameL)] -> Text
prettyPrintGenParams gp = if null gp then "" else T.concat ["[", intercalate ", " ((\(k, (n, _)) -> prettyPrintTypeKind k <> un n) <$> gp), "] "]

prettyPrintTypeKind :: TypeKind -> Text
prettyPrintTypeKind = \case MonoType -> ""; EffectType -> "@"; AbstractType -> "'"

prettyPrintTDef :: TDef -> Text
prettyPrintTDef tDef =
  let genericStr = prettyPrintGenParams tDef.genParams
   in case tDef.tDef of
        TypeAliasDecl t -> T.concat ["type ", genericStr, un $ fst tDef.name, " = ", prettyPrintType t]
        TypeDecl cons ds -> T.concat ["data ", genericStr, un $ fst tDef.name, " = ", intercalate " | " (prettyPrintDataCons <$> toList cons), ds']
          where
            ds' = if null ds then "" else "\n\tderiving " <> T.intercalate "," (ds <&> \x -> "\"" <> fst x <> "\"")
        BuiltinTypeDecl -> T.concat ["builtin ", genericStr, un $ fst tDef.name]
        Module t defs sigList wh -> T.concat ["mod ", genericStr, un $ fst tDef.name, " for ", prettyPrintType t, sigList', prettyPrintWheres wh, "\n", defs', "\n"]
          where
            defs' = T.unlines $ toList defs.vDefsOrdered <&> (prettyPrintVDef >>> ("\t" <>))
            sigList' = if null sigList then "" else " : " <> T.intercalate ", " (prettyPrintType <$> sigList)
        Trait defs sigList wh -> T.concat ["trait ", genericStr, un $ fst tDef.name, sigList', prettyPrintWheres wh, "\n", defs', "\n"]
          where
            defs' = T.unlines $ toList defs.vDefsOrdered <&> (prettyPrintVDef >>> ("\t" <>))
            sigList' = if null sigList then "" else " : " <> T.intercalate ", " (prettyPrintType <$> sigList)

prettyPrintDataCons :: DataCons -> Text
prettyPrintDataCons (DataCons name contents) = unwords [un (fst name), prettyPrintDataConsContents contents]

prettyPrintDataConsContents :: Fields -> Text
prettyPrintDataConsContents (TupleFields names) = unwords $ prettyPrintType <$> names
prettyPrintDataConsContents (RecordFields record) = T.concat ["{", intercalate ", " $ toList record <&> \((name, _), t) -> un name <> " : " <> prettyPrintType t, "}"]

prettyPrintType :: TypeExpr -> Text
prettyPrintType (TUnit, _) = "()"
prettyPrintType (TTuple types, _) = T.concat ["(", intercalate ", " (prettyPrintType <$> toList types), ")"]
prettyPrintType (TFunc args ret ef, _) = T.concat ["(\\", intercalate ", " (prettyPrintType <$> args), " -> ", prettyPrintType ret, ef', ")"]
  where
    ef' = case ef of
      [] -> ""
      ts -> "@(" <> T.intercalate ", " (ts <&> prettyPrintType) <> ")"
prettyPrintType (TNamed name [], _) = un $ fst name
prettyPrintType (TNamed name params, _) = T.concat [un $ fst name, "[", intercalate ", " (prettyPrintType <$> params), "]"]
prettyPrintType (TEffect ef, _) = case ef of
  [] -> "@()"
  ts -> "@(" <> T.intercalate ", " (ts <&> prettyPrintType) <> ")"
prettyPrintType (TLifetime n, _) = "'" <> un n

prettyPrintVarDecl :: Destructure -> Maybe TypeExpr -> Text
prettyPrintVarDecl d t = prettyPrintDestructure d <> (case t of Just t' -> " : " <> prettyPrintType t'; _ -> "")

prettyPrintExpr :: Expr -> Text
prettyPrintExpr (ELitInt n, _) = tShow n
prettyPrintExpr (ELitFloat t, _) = t
prettyPrintExpr (ELitBool b, _) = tShow b
prettyPrintExpr (ELitString s, _) = T.concat ["\"", T.map (\c -> if c >= ' ' then c else '?') s, "\""]
prettyPrintExpr (EVar name [], _) = un name
prettyPrintExpr (EVar name gArgs, _) = un name <> "[" <> T.intercalate ", " (prettyPrintType <$> gArgs) <> "]"
prettyPrintExpr (EClosure params body, _) = T.concat ["\\", intercalate ", " (params <&> uncurry prettyPrintVarDecl), " -> ", prettyPrintExpr body]
prettyPrintExpr (EFnCall f args, _) = T.concat [prettyPrintExpr f, "(", argsStr, ")"]
  where
    argsStr = if null args then "" else T.intercalate ", " $ prettyPrintExpr <$> args
prettyPrintExpr (EDoBlock [] (Just e), _) = prettyPrintExpr e
prettyPrintExpr (EDoBlock [] Nothing, _) = "{}"
prettyPrintExpr (EDoBlock stmts eMaybe, _) = T.concat ["{ ", T.concat $ toList stmts <&> \s -> prettyPrintStmt s <> " ; ", case eMaybe of Just x -> prettyPrintExpr x <> " "; _ -> "", "}"]
prettyPrintExpr (EIf cond t f, _) = T.concat ["(if ", prettyPrintExpr cond, " then ", prettyPrintExpr t, " else ", prettyPrintExpr f, ")"]
prettyPrintExpr (ETuple es, _) = T.concat ["(", intercalate ", " (prettyPrintExpr <$> toList es), ")"]
prettyPrintExpr (EAnd l r, _) = T.concat ["(", prettyPrintExpr l, " and ", prettyPrintExpr r, ")"]
prettyPrintExpr (EOr l r, _) = T.concat ["(", prettyPrintExpr l, " or ", prettyPrintExpr r, ")"]
prettyPrintExpr (EMatch e ps, _) = "case " <> prettyPrintExpr e <> " of " <> T.intercalate ", " (prettyPrintPatternBranch <$> toList ps)
prettyPrintExpr (EDataCons name [], _) = un (fst name)
prettyPrintExpr (EDataCons name gArgs, _) = un (fst name) <> "[" <> T.intercalate ", " (prettyPrintType <$> gArgs) <> "]"
prettyPrintExpr (EMemberCall lhs (name, _) args, _) = T.concat [prettyPrintExpr lhs, ".", getName name, "(", argsStr, ")"]
  where
    getName = \case Left x -> un x; Right x -> un x
    argsStr = if null args then "" else T.intercalate ", " $ prettyPrintExpr <$> args
prettyPrintExpr (ETry e cs fin, _) = T.concat ["try ", prettyPrintExpr e, cs', fin']
  where
    cs' =
      T.unwords $ toList cs <&> \(x, _, e') ->
        " catch " <> case x of
          Just (t, d) -> prettyPrintType t <> " " <> prettyPrintDestructure d
          _ -> "_" <> " -> " <> prettyPrintExpr e'
    fin' = fromMaybe "" $ fin <&> \f -> " finally " <> prettyPrintExpr f
prettyPrintExpr (EThrow e, _) = "throw " <> prettyPrintExpr e
prettyPrintExpr (ELitList es, _) = "[" <> T.intercalate ", " (prettyPrintExpr <$> es) <> "]"
prettyPrintExpr (EIndex e i, _) = prettyPrintExpr e <> "." <> tShow i
prettyPrintExpr (EFieldAccess e (f, _), _) = prettyPrintExpr e <> "." <> un f
prettyPrintExpr (ERecordInit t fs, _) = prettyPrintType t <> "{ " <> T.intercalate ", " (ppField <$> toList fs) <> " }"
  where
    ppField :: (VNameL, Maybe Expr) -> Text
    ppField ((n, _), Nothing) = un n
    ppField ((n, _), Just e') = un n <> " : " <> prettyPrintExpr e'
prettyPrintExpr (EBreak, _) = "break"
prettyPrintExpr (EContinue, _) = "continue"
prettyPrintExpr (EUpdate e setters, _) = prettyPrintExpr e <> "{ " <> T.intercalate ", " (setters <&> f) <> " }"
  where
    f (chain, e') = T.concat (toList chain <&> (fst >>> g >>> ("." <>))) <> " = " <> prettyPrintExpr e'
    g = \case
      AccessorChainName n -> un n
      AccessorChainIndex i -> tShow i
prettyPrintExpr (EExplicitType e t, _) = prettyPrintExpr e <> " : " <> prettyPrintType t
prettyPrintExpr (EAs e t, _) = prettyPrintExpr e <> " as " <> prettyPrintType t

prettyPrintPatternBranch :: MatchBranch -> Text
prettyPrintPatternBranch b = prettyPrintPattern b.pattern <> g <> " -> " <> prettyPrintExpr b.expr
  where
    g = case b.guard of Just x -> " | " <> prettyPrintExpr x; _ -> ""

prettyPrintPattern :: Pattern -> Text
prettyPrintPattern (PIgnore, _) = "_"
prettyPrintPattern (PName n, _) = un n
prettyPrintPattern (PTuple ps, _) = T.concat ["(", intercalate ", " (prettyPrintPattern <$> toList ps), ")"]
prettyPrintPattern (PDataCons (n, _) ps, _) = un n <> "(" <> T.intercalate ", " (prettyPrintPattern <$> ps) <> ")"
prettyPrintPattern (PRecord (n', _) fields, _) = T.concat [un n', "{", intercalate ", " $ fields <&> \((n, _), p) -> un n <> " = " <> prettyPrintPattern p, "}"]

prettyPrintStmt :: Stmt -> Text
prettyPrintStmt (SLet destr typ expr, _) =
  T.concat ["let ", prettyPrintDestructure destr, case typ of Just x -> " : " <> prettyPrintType x; _ -> "", " = ", prettyPrintExpr expr]
prettyPrintStmt (SRecLet name typ expr, _) =
  T.concat ["let rec ", un $ fst name, " :: ", prettyPrintType typ, " = ", prettyPrintExpr expr]
prettyPrintStmt (SExpr expr, sr) = prettyPrintExpr (expr, sr)
prettyPrintStmt (SWhen condExpr thenExpr, _) = T.concat ["when ", prettyPrintExpr condExpr, " do ", prettyPrintExpr thenExpr]
prettyPrintStmt (SAssign (lhs, _) rhs, _) = T.concat ["set ", un lhs, " = ", prettyPrintExpr rhs]
prettyPrintStmt (SForEach {destr, inExpr, bodyExpr}, _) = T.concat ["foreach ", prettyPrintDestructure destr, " in ", prettyPrintExpr inExpr, " do ", prettyPrintExpr bodyExpr]
prettyPrintStmt (SLoop e, _) = T.concat ["loop ", prettyPrintExpr e]

prettyPrintDestructure :: Destructure -> Text
prettyPrintDestructure (DIgnore, _) = "_"
prettyPrintDestructure (DName n False, _) = un n
prettyPrintDestructure (DName n True, _) = "mut " <> un n
prettyPrintDestructure (DTuple ps, _) = T.concat ["(", intercalate ", " (prettyPrintDestructure <$> toList ps), ")"]
prettyPrintDestructure (DDataCons ps, _) = ".(" <> T.intercalate ", " (prettyPrintDestructure <$> toList ps) <> ")"
prettyPrintDestructure (DRecord fields, _) = T.concat [".", "{", intercalate ", " $ fields <&> \((n, _), p) -> un n <> " = " <> prettyPrintDestructure p, "}"]
prettyPrintDestructure (DAs (name, _) mut d, _) = T.concat [if mut then "mut " else "", un name, "@", prettyPrintDestructure d]
