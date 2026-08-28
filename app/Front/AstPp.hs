-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{- HLINT ignore "Use maybe" -}

-- AST Pretty printing functions
module Front.AstPp where

import Data.HashMap.Strict qualified as HM
import Data.List (sortOn)
import Data.Maybe (fromMaybe)
import Data.Text (intercalate, unlines, unwords)
import Data.Text qualified as T
import Front.Ast
import Front.TypeKind
import MhPrelude
import Names

-- Pretty printing functions

ppAst :: Ast -> Text
ppAst ast =
  let vDefs = sortOn ((.name) >>> fst >>> un) (HM.elems ast.vDefs)
      tDefs = sortOn ((.name) >>> fst >>> un) (HM.elems ast.tDefs)
   in T.concat [unlines $ ppVDef <$> vDefs, "\n", unlines $ ppTDef <$> tDefs, "\n"]

ppVDef :: VDef -> Text
ppVDef vDef =
  T.concat ["let ", ppGenParams vDef.genParams, un $ fst vDef.name, case vDef.op of Just (o, _) -> " " <> un o; _ -> "", t, wh, case vDef.expr of Just e -> " = " <> ppExpr e; _ -> ""]
  where
    t = case vDef.typeExpr of
      Just x -> " : " <> ppType x
      Nothing -> ""
    wh = ppWheres vDef.whereClauses

ppWheres :: WhereClauses -> Text
ppWheres =
  \case
    [] -> ""
    xs -> " where " <> T.intercalate "," (xs <&> mkWh)
  where
    mkWh (l, r) = ppType l <> " : " <> ppType r

ppGenParams :: [(TypeKind, TNameL)] -> Text
ppGenParams gp = if null gp then "" else T.concat ["[", intercalate ", " ((\(k, (n, _)) -> ppTypeKind k <> un n) <$> gp), "] "]

ppTypeKind :: TypeKind -> Text
ppTypeKind = \case MonoType -> ""; EffectType -> "@"; AbstractType -> "'"

ppTDef :: TDef -> Text
ppTDef tDef =
  let genericStr = ppGenParams tDef.genParams
   in case tDef.tDef of
        TypeAliasDecl t -> T.concat ["type ", genericStr, un $ fst tDef.name, " = ", ppType t]
        TypeDecl cons ds -> T.concat ["data ", genericStr, un $ fst tDef.name, " = ", intercalate " | " (ppDataCons <$> toList cons), ds']
          where
            ds' = if null ds then "" else "\n\tderiving " <> T.intercalate "," (ds <&> \x -> "\"" <> fst x <> "\"")
        BuiltinTypeDecl -> T.concat ["builtin ", genericStr, un $ fst tDef.name]
        Module t defs sigList wh assocTypes -> T.concat ["mod ", genericStr, un $ fst tDef.name, " for ", ppType t, sigList', ppWheres wh, "\n", assocTypes', defs', "\n"]
          where
            defs' = T.unlines $ toList defs.vDefsOrdered <&> (ppVDef >>> ("\t" <>))
            sigList' = if null sigList then "" else " : " <> T.intercalate ", " (ppType <$> sigList)
            assocTypes' = T.unlines $ sortOn (un . fst) (HM.toList assocTypes) <&> \(n, (_, t')) -> "\ttype " <> un n <> " = " <> ppType t'
        Trait defs sigList wh assocTypes -> T.concat ["trait ", genericStr, un $ fst tDef.name, sigList', ppWheres wh, "\n", assocTypes', defs', "\n"]
          where
            defs' = T.unlines $ toList defs.vDefsOrdered <&> (ppVDef >>> ("\t" <>))
            sigList' = if null sigList then "" else " : " <> T.intercalate ", " (ppType <$> sigList)
            assocTypes' = T.unlines $ sortOn un (HM.keys assocTypes) <&> \n -> "\ttype " <> un n

ppDataCons :: DataCons -> Text
ppDataCons (DataCons name contents) = unwords [un (fst name), ppDataConsContents contents]

ppDataConsContents :: Fields -> Text
ppDataConsContents (TupleFields names) = unwords $ ppType <$> names
ppDataConsContents (RecordFields record) = T.concat ["{", intercalate ", " $ toList record <&> \((name, _), t) -> un name <> " : " <> ppType t, "}"]

ppType :: TypeExpr -> Text
ppType (TUnit, _) = "()"
ppType (TTuple types, _) = T.concat ["(", intercalate ", " (ppType <$> toList types), ")"]
ppType (TFunc args ret ef, _) = T.concat ["(\\", intercalate ", " (ppType <$> args), " -> ", ppType ret, ef', ")"]
  where
    ef' = case ef of
      [] -> ""
      ts -> "@(" <> T.intercalate ", " (ts <&> ppType) <> ")"
ppType (TNamed qualMaybe name params, _) =
  T.concat
    [ maybe "" (fst >>> un >>> (<> ".")) qualMaybe,
      un $ fst name,
      if null params then "" else T.concat ["[", intercalate ", " (ppType <$> params), "]"]
    ]
ppType (TEffect ef, _) = case ef of
  [] -> "@()"
  ts -> "@(" <> T.intercalate ", " (ts <&> ppType) <> ")"
ppType (TLifetime n, _) = "'" <> un n

ppVarDecl :: Destructure -> Maybe TypeExpr -> Text
ppVarDecl d t = ppDestructure d <> (case t of Just t' -> " : " <> ppType t'; _ -> "")

ppExpr :: Expr -> Text
ppExpr (ELitInt n, _) = tShow n
ppExpr (ELitFloat t, _) = t
ppExpr (ELitBool b, _) = tShow b
ppExpr (ELitString s, _) = T.concat ["\"", T.map (\c -> if c >= ' ' then c else '?') s, "\""]
ppExpr (EVar qualMaybe name gArgs, _) =
  T.concat
    [ maybe "" (fst >>> un >>> (<> ".")) qualMaybe,
      un name,
      if null gArgs then "" else T.concat ["[", intercalate ", " (ppType <$> gArgs), "]"]
    ]
ppExpr (EClosure params body, _) = T.concat ["\\", intercalate ", " (params <&> uncurry ppVarDecl), " -> ", ppExpr body]
ppExpr (EFnCall f args, _) = T.concat [ppExpr f, "(", argsStr, ")"]
  where
    argsStr = if null args then "" else T.intercalate ", " $ ppExpr <$> args
ppExpr (EDoBlock [] (Just e), _) = ppExpr e
ppExpr (EDoBlock [] Nothing, _) = "{}"
ppExpr (EDoBlock stmts eMaybe, _) = T.concat ["{ ", T.concat $ toList stmts <&> \s -> ppStmt s <> " ; ", case eMaybe of Just x -> ppExpr x <> " "; _ -> "", "}"]
ppExpr (EIf cond t f, _) = T.concat ["(if ", ppExpr cond, " then ", ppExpr t, " else ", ppExpr f, ")"]
ppExpr (ETuple es, _) = T.concat ["(", intercalate ", " (ppExpr <$> toList es), ")"]
ppExpr (EAnd l r, _) = T.concat ["(", ppExpr l, " and ", ppExpr r, ")"]
ppExpr (EOr l r, _) = T.concat ["(", ppExpr l, " or ", ppExpr r, ")"]
ppExpr (EMatch e ps, _) = "case " <> ppExpr e <> " of " <> T.intercalate ", " (ppPatternBranch <$> toList ps)
ppExpr (EDataCons qualMaybe name gArgs, _) =
  T.concat
    [ maybe "" (fst >>> un >>> (<> ".")) qualMaybe,
      un $ fst name,
      if null gArgs then "" else T.concat ["[", intercalate ", " (ppType <$> gArgs), "]"]
    ]
ppExpr (EMemberCall lhs (name, _) args, _) = T.concat [ppExpr lhs, ".", getName name, "(", argsStr, ")"]
  where
    getName = \case Left x -> un x; Right x -> un x
    argsStr = if null args then "" else T.intercalate ", " $ ppExpr <$> args
ppExpr (ETry e cs fin, _) = T.concat ["try ", ppExpr e, cs', fin']
  where
    cs' =
      T.unwords $ toList cs <&> \(x, _, e') ->
        " catch " <> case x of
          Just (t, d) -> ppType t <> " " <> ppDestructure d
          _ -> "_" <> " -> " <> ppExpr e'
    fin' = fromMaybe "" $ fin <&> \f -> " finally " <> ppExpr f
ppExpr (EThrow e, _) = "throw " <> ppExpr e
ppExpr (ELitList es, _) = "[" <> T.intercalate ", " (ppExpr <$> es) <> "]"
ppExpr (EIndex e i, _) = ppExpr e <> "." <> tShow i
ppExpr (EFieldAccess e (f, _), _) = ppExpr e <> "." <> un f
ppExpr (ERecordInit t fs, _) = ppType t <> "{ " <> T.intercalate ", " (ppField <$> toList fs) <> " }"
  where
    ppField :: (VNameL, Maybe Expr) -> Text
    ppField ((n, _), Nothing) = un n
    ppField ((n, _), Just e') = un n <> " : " <> ppExpr e'
ppExpr (EBreak, _) = "break"
ppExpr (EContinue, _) = "continue"
ppExpr (EUpdate e setters, _) = ppExpr e <> "{ " <> T.intercalate ", " (setters <&> f) <> " }"
  where
    f (chain, e') = T.concat (toList chain <&> (fst >>> g >>> ("." <>))) <> " = " <> ppExpr e'
    g = \case
      AccessorChainName n -> un n
      AccessorChainIndex i -> tShow i
ppExpr (EExplicitType e t, _) = ppExpr e <> " : " <> ppType t
ppExpr (EAs e t, _) = ppExpr e <> " as " <> ppType t

ppPatternBranch :: MatchBranch -> Text
ppPatternBranch b = ppPattern b.pattern <> g <> " -> " <> ppExpr b.expr
  where
    g = case b.guard of Just x -> " | " <> ppExpr x; _ -> ""

ppPattern :: Pattern -> Text
ppPattern (PIgnore, _) = "_"
ppPattern (PName n, _) = un n
ppPattern (PTuple ps, _) = T.concat ["(", intercalate ", " (ppPattern <$> toList ps), ")"]
ppPattern (PDataCons (n, _) ps, _) = un n <> "(" <> T.intercalate ", " (ppPattern <$> ps) <> ")"
ppPattern (PRecord (n', _) fields, _) = T.concat [un n', "{", intercalate ", " $ fields <&> \((n, _), p) -> un n <> " = " <> ppPattern p, "}"]

ppStmt :: Stmt -> Text
ppStmt (SLet destr typ expr, _) =
  T.concat ["let ", ppDestructure destr, case typ of Just x -> " : " <> ppType x; _ -> "", " = ", ppExpr expr]
ppStmt (SRecLet name typ expr, _) =
  T.concat ["let rec ", un $ fst name, " :: ", ppType typ, " = ", ppExpr expr]
ppStmt (SExpr expr, sr) = ppExpr (expr, sr)
ppStmt (SWhen condExpr thenExpr, _) = T.concat ["when ", ppExpr condExpr, " do ", ppExpr thenExpr]
ppStmt (SAssign (lhs, _) rhs, _) = T.concat ["set ", un lhs, " = ", ppExpr rhs]
ppStmt (SForEach {destr, inExpr, bodyExpr}, _) = T.concat ["foreach ", ppDestructure destr, " in ", ppExpr inExpr, " do ", ppExpr bodyExpr]
ppStmt (SLoop e, _) = T.concat ["loop ", ppExpr e]

ppDestructure :: Destructure -> Text
ppDestructure (DIgnore, _) = "_"
ppDestructure (DName n False, _) = un n
ppDestructure (DName n True, _) = "mut " <> un n
ppDestructure (DTupleLike ps, _) = T.concat ["(", intercalate ", " (ppDestructure <$> toList ps), ")"]
ppDestructure (DRecord fields, _) = T.concat [".", "{", intercalate ", " $ fields <&> \((n, _), p) -> un n <> " = " <> ppDestructure p, "}"]
ppDestructure (DAs (name, _) mut d, _) = T.concat [if mut then "mut " else "", un name, "@", ppDestructure d]
