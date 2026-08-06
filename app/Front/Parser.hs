-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
--
-- ImplicitParams allows passing state around similar to the ReaderT IO pattern
{-# LANGUAGE ImplicitParams #-}

module Front.Parser (parseMoorhenAst, parseMoorhenExpr) where

import Control.Exception (throwIO)
import Control.Exception qualified as CEx
import Control.Monad (forM_, unless, void, when)
import Data.Functor (($>))
import Data.HashMap.Strict qualified as HM
import Data.Int (Int64)
import Data.List (foldl1, isPrefixOf)
import Data.List qualified as List
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Text qualified as T
import Error
import Front.Ast qualified as A
import Front.Tokens
import Front.TypeKind (TypeKind (AbstractType, EffectType, MonoType))
import GHC.Stack (HasCallStack)
import MhPrelude hiding (and, or, (*>), (<*))
import Names
import SrcLoc
import Vars

data Pred
  = PredTk Token
  | PredVName
  | PredUnderscore
  | PredTName
  | PredSym Text
  | PredKw Keyword
  | PredInt
  | PredNot Pred
  | PredMany [Pred]
  | PredOneOf [Pred]
  | PredAlways

throw :: (HasCallStack, HasSrcRange r) => r -> Text -> IO a
throw sr msg = do
  assertM $ not $ T.null msg
  -- error $ T.unpack msg <> "\nat " <> show (srcRangeOf sr sr)
  throwIO $ Error ErrParser SevError (srcRangeOf sr sr) msg

parseMoorhenAst :: FilePath -> [TokenL] -> IO (Either Error A.Ast)
parseMoorhenAst _path tokens = do
  ts <- newVar tokens
  let ?tokens = ts
  CEx.try ast

parseMoorhenExpr :: FilePath -> [TokenL] -> IO (Either Error A.Expr)
parseMoorhenExpr _path tokens = do
  ts <- newVar tokens
  let ?tokens = ts
  CEx.try $ expr False

ast :: (Args) => IO A.Ast
ast = do
  imports <- many (PredKw KwImport) import'

  a <- newVar $ A.Ast {imports, vDefs = def, tDefs = def}
  _ <- many (PredTk Newline) newline

  let go = do
        ts <- getVar ?tokens
        case ts of
          [] -> pure ()
          _ -> do
            oneOf
              [ (PredKw KwLet, valDefTopLevel a),
                (PredOneOf $ (PredTk . Kw <$> [KwBuiltin, KwData, KwType, KwMod, KwTrait]) <> [PredSym "#"], typeDef a)
              ]
            _ <- many1 (PredTk Newline) newline
            go

  go
  getVar a

import' :: (Args) => IO A.Import
import' = do
  _ <- kw KwImport
  (path, sr) <- stringLit
  qual <- optWithPrefixTk (Kw KwAs) tName
  names <-
    oneOf
      [ (PredMany [PredSym "(", PredSym ".."], (symbol "(" >> symbol ".." >> symbol ")") $> AllNames),
        ( PredSym "(",
          do
            namesTextL <- symbol "(" *> list (PredNot $ PredSym ")") anyName (PredSym ",") <* symbol ")"
            pure $ VisibleNames $ first Name <$> namesTextL
        ),
        ( PredSym "~",
          do
            _ <- symbol "~" >> symbol "("
            namesTextL <- list (PredNot $ PredSym ")") anyName (PredSym ",") <* symbol ")"
            pure $ HiddenNames $ first Name <$> namesTextL
        ),
        (PredAlways, pure NoNames)
      ]
  _ <- many1 (PredTk Newline) newline
  pure $ A.Import {path, sr, qual, names}

valDefTopLevel :: (Args) => Var IO A.Ast -> IO ()
valDefTopLevel a = do
  a' <- getVar a
  let idx = length a'.vDefs
  x <- letDef
  vDefs <- hmTryInsert (snd x.name) (fst x.name) (x {A.idx}) a'.vDefs
  setVar a $ a' {A.vDefs}

letDef :: (Args) => IO A.VDef
letDef = do
  (_, letSr) <- kw KwLet
  name <- vName
  op <- anyOpMaybe

  let paramsInline = do
        (_, paramsSr0) <- symbol "("
        xs <- list (PredNot $ PredSym ")") param (PredSym ",")
        (_, paramsSr1) <- symbol ")"
        pure (xs, srcRangeOf paramsSr0 paramsSr1)

  peekToken >>= \case
    Just (Indent, _) -> do
      _ <- indent
      gps <- parseGenParamsMultilineMaybe
      peekToken >>= \case
        Just (Symbol "(", _) -> do
          params <-
            oneOf
              [ ( PredMany [PredSym "(", PredTk Indent],
                  do
                    (_, paramsSr0) <- symbol "("
                    _ <- indent
                    xs <- many1 (PredNot $ PredTk Outdent) $ param <* optCommaNewline
                    (_, paramsSr1) <- (outdent >> newline) *> symbol ")" <* newline
                    pure (toList xs, srcRangeOf paramsSr0 paramsSr1)
                ),
                (PredSym "(", paramsInline <* newline)
              ]

          retTypeExprMaybe <- optWithPrefixTk (Symbol ":") $ typeExprInd <* newline
          (effs, _) <- effectsNewlineMaybe
          whereClauses <-
            fromMaybe [] <$> optWithPrefixTk (Kw KwWhere) ((toList <$> list1 whereClause (PredSym ",")) <* newline)
          _ <- outdent

          exprMaybe <-
            opt
              (PredMany [PredTk Newline, PredSym "->"])
              ((newline >> symbol "->") *> indBlockExpr)

          mkFnVDef letSr name op gps params retTypeExprMaybe whereClauses effs exprMaybe
        _ -> do
          typeExpr' <- optWithPrefixTk (Symbol ":") $ typeExprInd <* newline
          whereClauses <- opt (PredKw KwWhere) (kw KwWhere *> list1 whereClause (PredSym ",") <* newline)
          _ <- outdent
          exprMaybe <-
            opt (PredMany [PredTk Newline, PredSym "="]) $ (newline >> symbol "=") *> indBlockExpr
          pure
            $ A.VDef
              { A.name,
                A.op,
                A.genParams = gps,
                A.whereClauses = maybe [] toList whereClauses,
                A.typeExpr = typeExpr',
                A.expr = exprMaybe,
                A.idx = -1
              }
    _ -> do
      genParams <- parseGenParamsMaybe
      peekToken >>= \case
        Just (Symbol "(", _) -> do
          params <- paramsInline
          retTypeExprMaybe <- optWithPrefixTk (Symbol ":") typeExpr
          (effs, _) <- effectsMaybe
          whereClauses <- maybe [] toList <$> opt (PredKw KwWhere) (kw KwWhere *> list1 whereClause (PredSym ","))
          exprMaybe <-
            peekToken >>= \case
              Just (Symbol "->", _) -> symbol "->" *> (Just <$> expr False)
              Just (Indent, _) -> (Just <$> indBlockExpr)
              _ -> pure Nothing
          mkFnVDef letSr name op genParams params retTypeExprMaybe whereClauses effs exprMaybe
        _ -> do
          typeExpr' <- optWithPrefixTk (Symbol ":") typeExpr
          whereClauses <- opt (PredKw KwWhere) (kw KwWhere *> list1 whereClause (PredSym ","))
          exprMaybe <- optWithPrefixTk (Symbol "=") (indBlockOrExpr True)

          pure
            $ A.VDef
              { A.name,
                A.op,
                A.genParams,
                A.whereClauses = maybe [] toList whereClauses,
                A.typeExpr = typeExpr',
                A.expr = exprMaybe,
                A.idx = -1
              }

param :: (Args) => IO (A.Destructure, Maybe A.TypeExpr)
param = do
  oneOf
    [ ( destructurePredicate,
        do
          d <- destructure
          t <- optWithPrefixTk (Symbol ":") typeExpr
          pure (d, t)
      ),
      ( PredAlways,
        do
          t <- typeExpr
          pure ((A.DIgnore, def), Just t)
      )
    ]

paramTyped :: (Args) => IO (A.Destructure, A.TypeExpr)
paramTyped = do
  oneOf
    [ ( destructurePredicate,
        do
          d <- destructure
          t <- symbol ":" *> typeExpr
          pure (d, t)
      ),
      ( PredAlways,
        do
          t <- typeExpr
          pure ((A.DIgnore, def), t)
      )
    ]

mkFnVDef ::
  SrcRange ->
  VNameL ->
  Maybe OpNameL ->
  [(TypeKind, TNameL)] ->
  ([(A.Destructure, Maybe A.TypeExpr)], SrcRange) ->
  Maybe A.TypeExpr ->
  [(A.TypeExpr, A.TypeExpr)] ->
  [A.TypeExpr] ->
  Maybe A.Expr ->
  IO A.VDef
mkFnVDef kwSr name op genParams (params, paramsSr) retTypeMaybe whereClauses effs exprMaybe = do
  -- Check params are consistent: either all have types or all don't
  let allHaveTypes = all (\(_, t) -> isJust t) params
      allNameOnly = all (\(_, t) -> isNothing t) params && null effs && isNothing retTypeMaybe
  unless (allHaveTypes || allNameOnly)
    $ throw (srcRangeOf kwSr paramsSr) "Parameters must be either all typed or all untyped"

  -- Build the closure expression if we have an expression
  let closureExpr' = case exprMaybe of
        Just body ->
          -- Build closure from params and body
          Just (A.EClosure (params <&> second (const Nothing)) body, snd body)
        Nothing -> Nothing

  -- Build the type expression only if all parameters have types
  let typeExprMaybe =
        if allHaveTypes
          then
            let paramTypes = (snd >>> must) <$> params
                retType = fromMaybe (A.TUnit, srcRangeOf kwSr name) retTypeMaybe
                sr = kwSr `srcRangeOf` name `srcRangeOf` paramsSr `srcRangeOf` retTypeMaybe `srcRangeOf` effs
             in Just (A.TFunc paramTypes retType effs, sr)
          else Nothing

  -- Build the VDef
  pure
    A.VDef
      { name,
        op,
        genParams,
        whereClauses,
        typeExpr = typeExprMaybe,
        expr = closureExpr',
        idx = -1
      }

destructurePredicate :: Pred
destructurePredicate =
  let p = PredOneOf [PredVName, PredSym ".", PredUnderscore]
   in PredOneOf [p, PredMany [PredSym "(", p]]

destructure :: (Args) => IO A.Destructure
destructure =
  oneOf
    [ ( PredUnderscore,
        do
          (_, sr) <- anyToken
          pure (A.DIgnore, sr)
      ),
      (PredSym "(", tupleDestructure),
      ( PredKw KwMut,
        do
          _ <- kw KwMut
          name <- vName
          -- Check for mutable as-pattern: mut name@...
          peekToken >>= \case
            Just (Symbol "@", _) -> do
              _ <- anyToken
              d <- destructure
              pure (A.DAs name True d, srcRangeOf name d)
            _ -> pure (A.DName (fst name) True, snd name)
      ),
      ( PredVName,
        do
          name <- vName
          -- Check if this is an as-pattern: name@...
          peekToken >>= \case
            Just (Symbol "@", _) -> do
              _ <- anyToken
              d <- destructure
              pure (A.DAs name False d, srcRangeOf name d)
            _ -> pure (A.DName (fst name) False, snd name)
      ),
      ( PredSym ".",
        do
          _ <- symbol "."
          oneOf
            [ (PredSym "(", dataConsTupleDestructure),
              (PredSym "{", dataConsRecordDestructure)
            ]
      )
    ]

tupleDestructure :: (Args) => IO A.Destructure
tupleDestructure = do
  (_, startSr) <- symbol "("
  d0 <- destructure <* symbol ","
  List1 d1 ds <- list1 destructure (PredSym ",")
  (_, endSr) <- symbol ")"
  pure (A.DTuple (List2 d0 d1 ds), srcRangeOf startSr endSr)

dataConsTupleDestructure :: (Args) => IO A.Destructure
dataConsTupleDestructure = do
  (_, startSr) <- symbol "("
  args <- list1 destructure (PredSym ",")
  (_, endSr) <- symbol ")"
  pure (A.DDataCons args, srcRangeOf startSr endSr)

dataConsRecordDestructure :: (Args) => IO A.Destructure
dataConsRecordDestructure = do
  (_, startSr) <- symbol "{"
  fields <- list (PredNot $ PredSym "}") recordFieldDestructure (PredSym ",")
  (_, endSr) <- symbol "}"
  pure (A.DRecord fields, srcRangeOf startSr endSr)

recordFieldDestructure :: (Args) => IO (VNameL, A.Destructure)
recordFieldDestructure =
  peekToken >>= \case
    Just (Kw KwMut, sr0) -> do
      _ <- anyToken
      fieldName <- vName
      -- Field with same name as variable
      pure (fieldName, (A.DName (fst fieldName) True, srcRangeOf sr0 fieldName))
    _ -> do
      fieldName <- vName
      peekToken >>= \case
        Just (Kw KwAs, _) -> do
          _ <- anyToken
          d <- destructure
          pure (fieldName, d)
        _ -> do
          -- Field with same name as variable
          pure (fieldName, (A.DName (fst fieldName) False, snd fieldName))

typeDef :: (Args) => Var IO A.Ast -> IO ()
typeDef astVar = do
  tDef <-
    oneOf
      [ (PredKw KwBuiltin, builtin),
        (PredKw KwType, typeAlias),
        (PredSym "#", dataDef),
        (PredKw KwData, dataDef),
        (PredKw KwMod, modDef),
        (PredKw KwTrait, traitDef)
      ]

  do
    ast' <- getVar astVar
    tDefs' <- hmTryInsert (snd tDef.name) (fst tDef.name) tDef ast'.tDefs
    setVar astVar $ ast' {A.tDefs = tDefs'}

builtin :: (Args) => IO A.TDef
builtin = do
  _ <- kw KwBuiltin
  isEffect <- optSymbol "@" <&> isJust
  name <- tName
  genParams <- parseGenParamsMaybe
  let tDef = A.TDef {name, genParams, isEffect, tDef = A.BuiltinTypeDecl}
  pure tDef

typeAlias :: (Args) => IO A.TDef
typeAlias = do
  _ <- kw KwType
  name <- tName
  genParams <- parseGenParamsMaybe
  _ <- symbol "="
  e <- typeExpr
  let tDef = A.TDef {name, genParams, isEffect = False, tDef = A.TypeAliasDecl e}
  pure tDef

dataDef :: (Args) => IO A.TDef
dataDef = do
  derives <- opt (PredSym "#") $ do
    _ <- symbol "#" >> exactVName "deriving" >> symbol "("
    xs <- list (PredNot $ PredSym ")") stringLit (PredSym ",")
    _ <- symbol ")" >> newline
    pure xs

  _ <- kw KwData
  isEffect <- optSymbol "@" <&> isJust
  name <- tName
  genParams <- parseGenParamsMaybe

  let dConsList = symbol "=" *> list1 dataCons (PredSym "|")

  let dConsListPrefixOpDCons = many1 PredTName (dataConsInd <* newline)
  let dConsListPrefixOp = (symbol "=" >> symbol "|" >> indent) *> dConsListPrefixOpDCons <* outdent

  let non = pure $ List1 (A.DataCons name (A.TupleFields [])) []
  dCons <-
    oneOf
      [ (PredOneOf [PredSym "(", PredSym "{"], fieldsIndNonEmpty <&> \x -> List1 (A.DataCons name x) []),
        (PredMany [PredSym "=", PredSym "|"], dConsListPrefixOp),
        (PredSym "=", dConsList),
        (PredNot (PredOneOf [PredSym "=", PredSym "(", PredSym "{"]), non)
      ]

  let d = A.TDef {name, genParams, isEffect, tDef = A.TypeDecl dCons (fromMaybe [] derives)}

  pure d

dataCons :: (Args) => IO A.DataCons
dataCons =
  A.DataCons
    <$> tName
    <*> oneOf
      [ (PredSym "{", dataConsFieldsNonEmpty),
        (PredSym "(", dataConsFieldsNonEmpty),
        (PredAlways, pure (A.TupleFields []))
      ]

dataConsFieldsNonEmpty :: (Args) => IO A.Fields
dataConsFieldsNonEmpty = do
  let recordFields = do
        _ <- symbol "{"
        fields <- list1 recordField (PredSym ",")
        _ <- symbol "}"
        pure $ A.RecordFields fields

  let tupleFields = do
        _ <- symbol "("
        fields <- toList <$> list1 typeExpr (PredSym ",")
        _ <- symbol ")"
        pure $ A.TupleFields fields

  oneOf [(PredSym "{", recordFields), (PredSym "(", tupleFields)]

dataConsInd :: (Args) => IO A.DataCons
dataConsInd = do
  A.DataCons
    <$> tName
    <*> oneOf
      [ (PredMany [PredOneOf [PredSym "(", PredSym "{"], PredTk Indent], fieldsIndNonEmpty),
        (PredSym "{", dataConsFieldsNonEmpty),
        (PredSym "(", dataConsFieldsNonEmpty),
        (PredAlways, pure (A.TupleFields []))
      ]

indBlockOf :: (Args) => IO a -> IO (List1 a)
indBlockOf p = do
  _ <- indent
  xs <- many1 (PredNot $ PredTk Outdent) $ p <* newline
  _ <- outdent
  pure xs

indBlockOfEnclosed :: (Args) => IO b -> IO a -> IO c -> IO (List1 a)
indBlockOfEnclosed pre p suffix = do
  _ <- pre
  xs <- indBlockOf p
  _ <- newline
  _ <- suffix
  pure xs

fieldsIndNonEmpty :: (Args) => IO A.Fields
fieldsIndNonEmpty = do
  let indentedTupleFields =
        (toList >>> A.TupleFields)
          <$> indBlockOfEnclosed (symbol "(") (typeExpr <* optSymbol ",") (symbol ")")

  let indentedRecordFields =
        A.RecordFields
          <$> indBlockOfEnclosed (symbol "{") (recordField <* optSymbol ",") (symbol "}")

  oneOf
    [ (PredMany [PredSym "(", PredTk Indent], indentedTupleFields),
      (PredMany [PredSym "{", PredTk Indent], indentedRecordFields),
      (PredAlways, dataConsFieldsNonEmpty)
    ]

recordField :: (Args) => IO (VNameL, A.TypeExpr)
recordField = do
  name <- vName
  _ <- symbol ":"
  ty <- typeExpr
  pure (name, ty)

parseGenParamsMaybe :: (Args) => IO [(TypeKind, TNameL)]
parseGenParamsMaybe =
  peekToken >>= \case
    Just (Symbol "[", _) -> parseGenParams False
    _ -> pure []

parseGenParamsMultilineMaybe :: (Args) => IO [(TypeKind, TNameL)]
parseGenParamsMultilineMaybe =
  peekToken >>= \case
    Just (Symbol "[", _) -> parseGenParams True <* newline
    _ -> pure []

parseGenParams :: (Args) => Bool -> IO [(TypeKind, TNameL)]
parseGenParams isInd = do
  oneOf
    $ [ ( PredMany [PredSym "[", PredTk Indent],
          do
            _ <- anyToken >> anyToken
            gps <- many (PredNot $ PredTk Outdent) $ do
              gp <- genParam
              _ <- optCommaNewline
              pure gp
            _ <- outdent >> newline
            pure gps
        )
      | isInd
      ]
    <> [ ( PredSym "[",
           do
             _ <- anyToken
             gps <- list1 genParam (PredSym ",")
             _ <- symbol "]"
             pure $ toList gps
         )
       ]

genParam :: (Args) => IO (TypeKind, TNameL)
genParam = do
  let x0 = tName <&> (MonoType,)
  let x1 = symbol "@" >> tName <&> (EffectType,)
  let x2 = symbol "`" >> tName <&> (AbstractType,)

  oneOf [(PredSym "@", x1), (PredSym "`", x2), (PredTName, x0)]

hmTryInsert :: (Hashable k) => SrcRange -> k -> v -> HashMap k v -> IO (HashMap k v)
hmTryInsert sr key !val m = do
  when (isJust $ HM.lookup key m) $ throw sr "Duplicate name"
  pure $ HM.insert key val m

modDef :: (Args) => IO A.TDef
modDef = do
  _ <- kw KwMod
  name <- tName
  genParams <- parseGenParamsMaybe

  _ <- kw KwFor
  forTypeExpr <- typeExpr

  (traits, vDefsOrdered, nameMap, opMap, wh) <- parseTraitsWhsInner
  let vDefs = A.BlockInner {vDefsOrdered, nameMap, opMap}

  let tDef = A.TDef {name, genParams, isEffect = False, tDef = A.Module forTypeExpr vDefs traits wh}
  pure tDef

traitDef :: (Args) => IO A.TDef
traitDef = do
  _ <- kw KwTrait
  name <- tName
  genParams <- parseGenParamsMaybe

  (traits, vDefsOrdered, nameMap, opMap, wh) <- parseTraitsWhsInner
  let vDefs = A.BlockInner {vDefsOrdered, nameMap, opMap}

  let tDef = A.TDef {name, genParams, isEffect = False, tDef = A.Trait vDefs traits wh}
  pure tDef

parseTraitsWhsInner ::
  (Args) => IO ([A.TypeExpr], [A.VDef], HashMap VName A.VDef, HashMap OpName (List1 A.VDef), A.WhereClauses)
parseTraitsWhsInner = do
  traits <- opt (PredSym ":") (symbol ":" *> list1 typeExpr (PredSym ",")) <&> maybe [] toList

  wh' <- opt (PredKw KwWhere) (kw KwWhere *> list1 whereClause (PredSym ","))
  let wh = maybe [] toList wh'

  _ <- indent

  defs <- many (PredNot $ PredTk Outdent) (letDef <* newline)

  _ <- outdent

  namesMap <- newVar def
  opsMap <- newVar def
  vDefsRev <- newVar []
  forM_ (zip [0 ..] defs) $ \(idx, vDef'@(A.VDef {A.name = (name', sr), A.op = opMaybe})) -> do
    xs <- getVar namesMap
    when (name' `elem` HM.keys xs) $ throw sr "Duplicate name"
    let vDef = vDef' {A.idx}
    modVar namesMap $ HM.insert name' $ vDef
    modVar vDefsRev (vDef :)
    forM_ opMaybe $ \(op, _) ->
      modVar opsMap $ HM.insertWith (<>) op (List1 vDef [])

  namesMap' <- getVar namesMap
  opsList' <- getVar opsMap
  vDefsOrdered <- getVar vDefsRev <&> reverse
  pure (traits, vDefsOrdered, namesMap', opsList', wh)

whereClause :: (Args) => IO (A.TypeExpr, A.TypeExpr)
whereClause = do
  t1 <- typeExpr
  _ <- symbol ":"
  t2 <- typeExpr
  pure (t1, t2)

anyOpMaybe :: (Args) => IO (Maybe (OpName, SrcRange))
anyOpMaybe = do
  peekToken >>= \case
    Just (Symbol s, sr)
      | s `elem` allOps ->
          anyToken $> Just (OpName s, sr)
    _ -> pure Nothing

typeExpr :: (Args) => IO A.TypeExpr
typeExpr = do
  oneOf
    [ -- \ X, Y -> Z
      (PredSym "\\", fnTypeExpr),
      -- @(X, Y)
      (PredSym "@", effects <&> first A.TEffect),
      -- ()
      ( PredMany [PredSym "(", PredSym ")"],
        do
          (_, sr0) <- anyToken
          (_, sr1) <- anyToken
          pure (A.TUnit, srcRangeOf sr0 sr1)
      ),
      -- (X) or (X, Y)
      ( PredSym "(",
        do
          (_, sr0) <- anyToken
          t0 <- typeExpr
          peekToken >>= \case
            Just (Symbol ",", _) -> do
              _ <- anyToken
              List1 t1 ts <- list1 typeExpr (PredSym ",")
              (_, sr1) <- symbol ")"
              pure (A.TTuple (List2 t0 t1 ts), srcRangeOf sr0 sr1)
            _ -> do
              _ <- symbol ")"
              pure t0
      ),
      -- X $ Y[Z]
      ( PredMany [PredTName, PredSym "$"],
        do
          n <- tName
          _ <- symbol "$"
          e <- typeExpr
          pure (A.TNamed n [e], srcRangeOf n e)
      ),
      -- X[Y, Z]
      (PredTName, namedType),
      -- 'varName
      ( PredSym "'",
        do
          (_, sr0) <- anyToken
          (n, sr1) <- vName
          pure (A.TLifetime n, srcRangeOf sr0 sr1)
      )
    ]

namedType :: (Args) => IO A.TypeExpr
namedType = do
  n <- tName
  (gArgs, sr') <- genArgsMaybe
  pure (A.TNamed n gArgs, srcRangeOf n sr')

typeExprInd :: (Args) => IO A.TypeExpr
typeExprInd = oneOf [(PredMany [PredSym "\\", PredTk Indent], fnTypeExprInd), (PredAlways, typeExpr)]

genArgs :: (Args) => IOL [A.TypeExpr]
genArgs = do
  sr0 <- symbol "["
  xs <- list (PredNot $ PredSym "]") typeExpr (PredSym ",")
  sr1 <- symbol "]"
  pure (xs, srcRangeOf sr0 sr1)

genArgsMaybe :: (Args) => IOL [A.TypeExpr]
genArgsMaybe =
  fromMaybe ([], def) <$> opt (PredSym "[") genArgs

fnTypeExpr :: (Args) => IO A.TypeExpr
fnTypeExpr = do
  sr0 <- symbol "\\"
  params <- list (PredNot $ PredSym "->") typeExpr (PredSym ",")
  _ <- symbol "->"
  ret <- typeExpr
  (effs, sr1) <- effectsMaybe
  let sr = sr0 `srcRangeOf` ret `srcRangeOf` sr1
  pure (A.TFunc (toList params) ret effs, sr)

fnTypeExprInd :: (Args) => IO A.TypeExpr
fnTypeExprInd = do
  sr1 <- symbol "\\"
  _ <- indent
  params <- list (PredNot $ PredTk Outdent) typeExpr (PredSym ",")
  _ <- outdent >> newline
  _ <- symbol "->"
  _ <- indent
  ret <- typeExprInd <* newline
  (effs, _) <- effectsNewlineMaybe
  _ <- outdent
  let sr = srcRangeOf (srcRangeOf sr1 ret) (srcRangeOf effs effs)
  pure (A.TFunc (toList params) ret effs, sr)

effects :: (Args) => IOL [A.TypeExpr]
effects = do
  (_, sr0) <- symbol "@"
  let withParens = do
        _ <- symbol "("
        xs <- list (PredNot $ PredSym ")") typeExpr (PredSym ",")
        _ <- symbol ")"
        pure (xs, srcRangeOf sr0 xs)

  oneOf [(PredSym "(", withParens), (PredTName, namedType <&> \x -> ([x], srcRangeOf sr0 x))]

effectsMaybe :: (Args) => IOL [A.TypeExpr]
effectsMaybe = do
  peekToken >>= \case
    Just (Symbol "@", sr0) -> do
      (xs, sr1) <- effects
      pure (xs, srcRangeOf sr0 sr1)
    _ -> pure ([], def)

-- TODO Merge with effectsMaybe, take hasNewline parameter
effectsNewlineMaybe :: (Args) => IOL [A.TypeExpr]
effectsNewlineMaybe = do
  peekToken >>= \case
    Just (Symbol "@", sr0) -> do
      (xs, sr1) <- effects <* newline
      pure (xs, srcRangeOf sr0 sr1)
    _ -> pure ([], def)

optCommaNewline :: (Args) => IO ()
optCommaNewline = do
  _ <- optSymbol ","
  _ <- newline
  pure ()

mkDoBlockExprFromStmts :: SrcRange -> [A.Stmt] -> A.Expr
mkDoBlockExprFromStmts sr stmts =
  case stmts of
    [] -> (A.EDoBlock [] Nothing, sr)
    _ -> do
      case List.last stmts of
        (A.SExpr expr', sr') ->
          if length stmts == 1
            then
              (expr', sr)
            else
              (A.EDoBlock (List.init stmts) (Just (expr', sr')), sr)
        _ ->
          (A.EDoBlock stmts Nothing, sr)

allOps :: [Text]
allOps = ["+", "-", "*", "/", "%", "==", "!=", ">", "<", ">=", "<=", "!", "$", "^", "++", "~"]

indBlockExpr :: (Args) => IO A.Expr
indBlockExpr =
  do
    sr0 <- indent
    stmts <-
      many1 (PredNot $ PredTk Outdent)
        $ oneOf
          [ (PredKw KwLet, letStmt True <* newline),
            (PredKw KwSet, setStmt True <* newline),
            (PredKw KwForeach, foreachStmt True <* newline),
            (PredKw KwLoop, loopStmt True <* newline),
            (PredMany [PredOneOf $ allOps <&> PredSym, PredTk Indent], prefixOpStmt <* newline),
            (PredAlways, (expr True <&> first A.SExpr) <* newline)
          ]
    sr1 <- outdent
    pure $ mkDoBlockExprFromStmts (srcRangeOf sr0 sr1) (toList stmts)

prefixOpStmt :: (Args) => IO A.Stmt
prefixOpStmt = do
  (op, opSr) <- (anyToken <* indent) <&> \case (Symbol x, sr) -> (x, sr); _ -> undefined
  args <- many1 (PredNot $ PredTk Outdent) (expr True <* newline)
  _ <- outdent
  let foldedExpr = foldl1 (\acc arg -> (A.EMemberCall acc (Right (OpName op), opSr) [arg], srcRangeOf acc arg)) args
  pure (A.SExpr $ fst foldedExpr, srcRangeOf opSr (snd (lastList1 args)))

ifElseExpr :: (Args) => Bool -> IO A.Expr
ifElseExpr isInd = do
  peekToken >>= \case
    Just (Kw KwIf, _) -> ifElseExpr' isInd
    _ -> cmpOp isInd

ifElseExpr' :: (Args) => Bool -> IO A.Expr
ifElseExpr' isInd = do
  (_, sr0) <- kw KwIf
  cond <- expr False

  let unInd = do
        thenExpr <- kw KwThen *> expr False
        elseExpr <- kw KwElse *> ifElseExpr False
        pure (A.EIf cond thenExpr elseExpr, srcRangeOf sr0 elseExpr)

  let ind = do
        thenExpr <- indBlockExpr
        oneOf
          [ ( PredMany [PredTk Newline, PredKw KwElse],
              do
                _ <- anyToken >> anyToken
                elseExpr <- oneOf [(PredKw KwIf, ifElseExpr' True), (PredTk Indent, indBlockExpr)]
                pure (A.EIf cond thenExpr elseExpr, srcRangeOf sr0 elseExpr)
            ),
            (PredAlways, pure (A.EIf cond thenExpr (A.EDoBlock [] Nothing, sr0), sr0))
          ]

  oneOf $ [(PredKw KwThen, unInd)] <> [(PredTk Indent, ind) | isInd]

expr :: (Args) => Bool -> IO A.Expr
expr isInd = do
  peekToken >>= \case
    Just (Kw KwThrow, sr0) -> do
      _ <- anyToken
      e <- expr isInd
      pure (A.EThrow e, srcRangeOf sr0 e)
    _ -> andOrExpr isInd

andOrExpr :: (Args) => Bool -> IO A.Expr
andOrExpr isInd = do
  lhs <- closureExpr isInd
  let andOr f = do
        _ <- anyToken
        rhs <- andOrExpr False
        pure (f lhs rhs, srcRangeOf lhs rhs)

  peekToken >>= \case
    Just (Kw KwAnd, _) -> andOr A.EAnd
    Just (Kw KwOr, _) -> andOr A.EOr
    _ -> pure lhs

closureExpr :: (Args) => Bool -> IO A.Expr
closureExpr isInd =
  peekToken >>= \case
    Just (Symbol "\\", sr0) -> do
      _ <- anyToken
      -- TODO Multiline params if isInd
      params <- list (PredNot $ PredSym "->") param (PredSym ",")
      _ <- symbol "->"
      body <- indBlockOrExpr isInd
      pure (A.EClosure params body, srcRangeOf sr0 body)
    _ -> pipelineExpr isInd

pipelineExpr :: (Args) => Bool -> IO A.Expr
pipelineExpr isInd = do
  lhs <- ifElseExpr isInd
  peekToken >>= \case
    Just (Symbol "$", _) -> do
      _ <- anyToken
      rhs <- expr False
      pure (A.EFnCall lhs [rhs], srcRangeOf lhs rhs)
    _ -> pure lhs

cmpOp :: (Args) => Bool -> IO A.Expr
cmpOp isInd = do
  lhs <- concatOp isInd
  let ops = ["==", "!=", ">", "<", ">=", "<="]
  peekToken >>= \case
    Just (Symbol s, opSr) | s `elem` ops -> do
      _ <- anyToken
      y <- concatOp False
      pure (A.EMemberCall lhs (Right $ OpName s, opSr) [y], srcRangeOf lhs y)
    _ ->
      pure lhs

parseLeftAssocOp :: (Args) => Bool -> (Bool -> IO A.Expr) -> [Text] -> IO A.Expr
parseLeftAssocOp isInd innerParser validOps = do
  lhs <- innerParser isInd
  peekToken >>= \case
    Just (Symbol s, _) | s `elem` validOps -> do
      let opName = OpName s

      let go leftExpr = do
            peekToken >>= \case
              Just (Symbol s', sr) | s' `elem` validOps -> do
                _ <- anyToken
                rightExpr <- innerParser False
                go (A.EMemberCall leftExpr (Right opName, sr) [rightExpr], srcRangeOf leftExpr rightExpr)
              _ -> pure leftExpr

      go lhs
    _ -> pure lhs

concatOp :: (Args) => Bool -> IO A.Expr
concatOp isInd = parseLeftAssocOp isInd arithOp ["++"]

arithOp :: (Args) => Bool -> IO A.Expr
arithOp isInd = parseLeftAssocOp isInd expOp2 ["+", "-"]

expOp2 :: (Args) => Bool -> IO A.Expr
expOp2 isInd = parseLeftAssocOp isInd arithOp2 ["^"]

arithOp2 :: (Args) => Bool -> IO A.Expr
arithOp2 isInd = parseLeftAssocOp isInd atomExpr ["*", "/", "%"]

atomExpr :: (Args) => Bool -> IO A.Expr
atomExpr isInd = do
  base <- atomBase
  let go e = do
        next <- peekToken
        case next of
          Just (Symbol "(", _) -> do
            e' <- functionCallSuffix e
            go e'
          Just (Symbol ".", _) -> do
            e' <- memberAccessSuffix e
            go e'
          Just (Symbol ":", _) -> explicitTypeSuffix e
          Just (Kw KwAs, _) -> asSuffix e
          Just (Symbol "{", _) ->
            case e of
              (A.EDataCons nameL typeArgs, _) -> recordInitSuffix e nameL typeArgs
              _ -> recordUpdateSuffix e
          _ -> pure e
  go base
  where
    atomBase :: (Args) => IO A.Expr
    atomBase = do
      t <- peekToken
      case t of
        Just (IntLiteral x, sr) -> anyToken $> (A.ELitInt x, sr)
        Just (FloatLiteral x, sr) -> anyToken $> (A.ELitFloat x, sr)
        Just (StringLiteral x, sr) -> anyToken $> (A.ELitString x, sr)
        Just (Kw KwTrue, sr) -> anyToken $> (A.ELitBool True, sr)
        Just (Kw KwFalse, sr) -> anyToken $> (A.ELitBool False, sr)
        Just (Ident _, _) -> variableExpr
        Just (TypeName _, _) -> dataConsExpr
        Just (Symbol "{", _) -> doBlockExpr
        Just (Symbol "(", _) -> tupleOrParenExpr
        Just (Symbol "[", _) -> listExpr
        Just (Kw KwTry, _) -> tryExpr
        Just (Kw KwBreak, sr) -> anyToken $> (A.EBreak, sr)
        Just (Kw KwContinue, sr) -> anyToken $> (A.EContinue, sr)
        Just (Kw KwMatch, _) -> matchExpr isInd
        Just (Symbol "+", _) -> unaryOpExpr
        Just (Symbol "-", _) -> unaryOpExpr
        Just (Symbol "!", _) -> unaryOpExpr
        _ -> expectedXGotReadTok "expression"

    variableExpr :: (Args) => IO A.Expr
    variableExpr = do
      (name, nameSr) <- vName
      (typeArgs, genArgsSr) <- genArgsMaybe
      pure (A.EVar name typeArgs, srcRangeOf nameSr genArgsSr)

    dataConsExpr :: (Args) => IO A.Expr
    dataConsExpr = do
      nameL@(_, nameSr) <- tName
      (typeArgs, genArgsSr) <- genArgsMaybe
      pure (A.EDataCons nameL typeArgs, srcRangeOf nameSr genArgsSr)

    recordFieldInit :: (Args) => IO (VNameL, Maybe A.Expr)
    recordFieldInit = do
      n <- vName
      exprMaybe <- opt (PredSym "=") (symbol "=" *> expr False)
      pure (n, exprMaybe)

    tupleOrParenExpr :: (Args) => IO A.Expr
    tupleOrParenExpr = do
      (_, startSr) <- symbol "("

      let tupleOrExprInParens = do
            e0 <- expr False
            rest <- many (PredSym ",") (symbol "," *> expr False)
            (_, endSr) <- symbol ")"
            case rest of
              [] -> pure e0
              (e1 : es) -> pure (A.ETuple $ List2 e0 e1 es, srcRangeOf startSr endSr)

      let indentedTuple = do
            _ <- indent
            e0 <- expr True <* optCommaNewline
            List1 e1 es <- many1 (PredNot $ PredTk Outdent) (expr True <* optCommaNewline)
            (_, endSr) <- outdent >> newline >> symbol ")"
            pure (A.ETuple $ List2 e0 e1 es, srcRangeOf startSr endSr)

      let unitExpr = do
            (_, sr1) <- anyToken
            pure (A.EDoBlock [] Nothing, srcRangeOf startSr sr1)

      oneOf
        $ [(PredSym ")", unitExpr)]
        <> [(PredTk Indent, indentedTuple) | isInd]
        <> [(PredAlways, tupleOrExprInParens)]

    listExpr :: (Args) => IO A.Expr
    listExpr = do
      (_, startSr) <- symbol "["
      (elems, endSr) <-
        peekToken >>= \case
          Just (Indent, _) | isInd -> do
            _ <- indent
            elemsList <- many1 (PredNot $ PredTk Outdent) (expr True <* optCommaNewline)
            (_, endSr) <- (outdent >> newline) *> symbol "]"
            pure (toList elemsList, endSr)
          _ -> do
            elemsList <- list (PredNot $ PredSym "]") (expr False) (PredSym ",")
            (_, endSr') <- symbol "]"
            pure (elemsList, endSr')
      pure (A.ELitList elems, srcRangeOf startSr endSr)

    tryExpr :: (Args) => IO A.Expr
    tryExpr = do
      (_, startSr) <- kw KwTry
      (tryBody, catches, finallyMaybe) <-
        peekToken >>= \case
          Just (Indent, _) -> do
            tryBody <- indBlockExpr
            catch0 <- catchBlock
            catches' <- many (PredMany [PredTk Newline, PredKw KwCatch]) catchBlock
            finallyMaybe <- opt (PredMany [PredTk Newline, PredKw KwFinally]) $ do
              _ <- newline >> kw KwFinally
              indBlockExpr
            let catches = List1 catch0 catches'
            pure (tryBody, catches, finallyMaybe)
          _ -> do
            tryBody <- expr False
            catches <- many1 (PredKw KwCatch) catchExpr
            finallyMaybe <- optWithPrefixTk (Kw KwFinally) (expr False)
            pure (tryBody, catches, finallyMaybe)

      let sr = srcRangeOf startSr (case finallyMaybe of Nothing -> snd3 (lastList1 catches); Just e -> snd e)
      pure (A.ETry tryBody catches finallyMaybe, sr)

    catchVar :: (Args) => IO (Maybe (A.TypeExpr, A.Destructure))
    catchVar =
      peekToken >>= \case
        Just (Ident (VName "_"), _) -> anyToken $> Nothing
        _ -> do
          t <- typeExpr
          d <- destructure
          pure $ Just (t, d)

    catchBlock :: (Args) => IO A.CatchBlock
    catchBlock = do
      (_, sr0) <- newline >> kw KwCatch
      cv <- catchVar
      body <- indBlockExpr
      pure (cv, srcRangeOf sr0 body, body)

    catchExpr :: (Args) => IO A.CatchBlock
    catchExpr = do
      (_, sr0) <- kw KwCatch
      cv <- catchVar
      (_, sr) <- kw KwThen
      body <- expr False
      pure (cv, srcRangeOf sr0 sr, body)

    unaryOpExpr :: (Args) => IO A.Expr
    unaryOpExpr = do
      (opToken, opSr) <- anyToken
      case opToken of
        Symbol op | op `elem` ["+", "-", "!"] -> do
          operand <- atomExpr False
          pure (A.EMemberCall operand (Right $ OpName op, opSr) [], srcRangeOf opSr operand)
        _ -> expectedXGotTok opSr "unary operator" opToken

    parseFnCallSuffixArgs :: (Args) => IO ([A.Expr], SrcRange)
    parseFnCallSuffixArgs = do
      (_, sr0) <- anyToken
      args <-
        peekToken >>= \case
          Just (Indent, _) | isInd -> do
            _ <- anyToken
            toList <$> many1 (PredNot $ PredTk Outdent) (expr True <* newline) <* (outdent >> newline)
          _ ->
            list (PredNot $ PredSym ")") (expr False) (PredSym ",")
      (_, sr1) <- symbol ")"
      pure (args, srcRangeOf sr0 sr1)

    functionCallSuffix :: (Args) => A.Expr -> IO A.Expr
    functionCallSuffix e = do
      (args, sr) <- parseFnCallSuffixArgs
      pure (A.EFnCall e args, sr)

    memberAccessSuffix :: (Args) => A.Expr -> IO A.Expr
    memberAccessSuffix lhs = do
      _ <- symbol "."

      oneOf
        [ (PredInt, intLit <&> \(i, sr) -> (A.EIndex lhs $ fromIntegral i, srcRangeOf lhs sr)),
          ( PredVName,
            do
              (name, nameSr) <- vName

              peekToken >>= \case
                Just (Symbol "(", _) -> do
                  (args, sr) <- parseFnCallSuffixArgs
                  pure (A.EMemberCall lhs (Left name, nameSr) args, srcRangeOf lhs sr)
                _ -> pure (A.EFieldAccess lhs (name, nameSr), srcRangeOf lhs nameSr)
          )
        ]

    explicitTypeSuffix :: (Args) => A.Expr -> IO A.Expr
    explicitTypeSuffix e = do
      (_, sr0) <- symbol ":"
      ty@(_, sr1) <- typeExpr
      pure (A.EExplicitType e ty, srcRangeOf sr0 sr1)

    asSuffix :: A.Expr -> (Args) => IO A.Expr
    asSuffix e = do
      (_, sr0) <- kw KwAs
      ty@(_, sr1) <- typeExpr
      pure (A.EAs e ty, srcRangeOf sr0 sr1)

    recordInitSuffix :: (Args) => A.Expr -> TNameL -> [A.TypeExpr] -> IO A.Expr
    recordInitSuffix e nameL typeArgs = do
      _ <- anyToken -- consume the '{'
      (fields, endSr) <-
        -- Check if next token is Indent for indented syntax
        peekToken >>= \case
          Just (Indent, _) | isInd -> do
            _ <- indent
            fieldsList <- many1 (PredNot $ PredTk Outdent) (recordFieldInit <* optCommaNewline)
            (_, endSr) <- (outdent >> newline) *> symbol "}"
            pure (fieldsList, endSr)
          _ -> do
            -- Inline syntax
            fieldsList <- list1 recordFieldInit (PredSym ",")
            (_, endSr) <- symbol "}"
            pure (fieldsList, endSr)

      pure (A.ERecordInit (A.TNamed nameL typeArgs, snd e) fields, srcRangeOf e endSr)

    recordUpdateSuffix :: (Args) => A.Expr -> IO A.Expr
    recordUpdateSuffix e = do
      _ <- anyToken -- consume the '{'
      (fields, endSr) <-
        -- Check if next token is Indent for indented syntax
        peekToken >>= \case
          Just (Indent, _) | isInd -> do
            _ <- indent
            fieldsList <- many1 (PredNot $ PredTk Outdent) (updateField <* optCommaNewline)
            (_, endSr) <- (outdent >> newline) *> symbol "}"
            pure (toList fieldsList, endSr)
          _ -> do
            -- Inline syntax
            fieldsList <- list (PredNot $ PredSym "}") updateField (PredSym ",")
            (_, endSr) <- symbol "}"
            pure (toList fieldsList, endSr)
      mkUpdateExpr e fields (srcRangeOf e endSr)

    updateField :: (Args) => IO (List1 A.AccessorChainPart, A.Expr)
    updateField = do
      lhs <- updateFieldLHS
      -- TODO Have this be optional, default to EVar with same name as field (error if index field)
      _ <- symbol "="
      e <- expr False
      pure (lhs, e)

    updateFieldLHS :: (Args) => IO (List1 A.AccessorChainPart)
    updateFieldLHS = do
      p0 <- updateFieldPart
      ps <- many (PredSym ".") (symbol "." *> updateFieldPart)
      pure $ List1 p0 ps

    updateFieldPart :: (Args) => IO A.AccessorChainPart
    updateFieldPart =
      oneOf
        [ (PredVName, vName <&> first A.AccessorChainName),
          ( PredInt,
            intLit >>= \(i, sr) -> do
              when (i < 0) $ throw sr "Negative index"
              pure (A.AccessorChainIndex (fromIntegral i), sr)
          )
        ]

doBlockExpr :: (Args) => IO A.Expr
doBlockExpr =
  do
    (_, startSr) <- symbol "{"
    let stmt :: (Args) => IO A.Stmt
        stmt = do
          oneOf
            [ (PredKw KwLet, letStmt False),
              (PredKw KwSet, setStmt False),
              (PredKw KwForeach, foreachStmt False),
              (PredKw KwLoop, loopStmt False),
              (PredAlways, expr False <&> first A.SExpr)
            ]
    stmts <- list (PredNot $ PredSym "}") stmt (PredSym ";")
    (_, endSr) <- symbol "}"
    let sr = srcRangeOf startSr endSr
    pure $ mkDoBlockExprFromStmts sr stmts

indBlockOrExpr :: (Args) => Bool -> IO A.Expr
indBlockOrExpr isInd =
  if isInd
    then
      oneOf [(PredTk Indent, indBlockExpr), (PredAlways, expr False)]
    else expr False

letStmt :: (Args) => Bool -> IO A.Stmt
letStmt isInd = do
  (_, sr0) <- kw KwLet
  isRec <- peekToken >>= \case Just (Kw KwRec, _) -> anyToken $> True; _ -> pure False

  oneOf
    [ ( PredOneOf $ [PredMany [PredVName, PredSym "("]] <> [PredMany [PredVName, PredTk Indent, PredSym "("] | isInd],
        restOfFnStmt isInd sr0 isRec
      ),
      ( PredAlways,
        if isRec
          then do
            name <- vName
            t <- symbol ":" *> typeExpr
            e <- indBlockOrExpr isInd
            pure (A.SRecLet name t e, srcRangeOf name e)
          else do
            d <- destructure
            tMaybe <- optWithPrefixTk (Symbol ":") typeExpr
            _ <- symbol "="
            e <- indBlockOrExpr isInd
            pure (A.SLet d tMaybe e, srcRangeOf d e)
      )
    ]

restOfFnStmt :: (Args) => Bool -> SrcRange -> Bool -> IO A.Stmt
restOfFnStmt isInd sr0 isRec = do
  name <- vName

  isIndentedMode <- peekToken >>= \case Just (Indent, _) | isInd -> anyToken $> True; _ -> pure False

  -- Parse parameters: decide inline vs indented based on next token after '('
  (params, _) <- do
    (_, startSr) <- symbol "("
    peekToken >>= \case
      Just (Indent, _) | isIndentedMode -> do
        _ <- indent
        xs <- many1 (PredNot $ PredTk Outdent) $ paramTyped <* optCommaNewline
        (_, endSr) <- (outdent >> newline) *> symbol ")" <* newline
        pure (toList xs, srcRangeOf startSr endSr)
      _ -> do
        xs <- list (PredNot $ PredSym ")") paramTyped (PredSym ",")
        (_, endSr) <- symbol ")"
        when isIndentedMode $ void newline
        pure (xs, srcRangeOf startSr endSr)

  retTypeMaybe <- optWithPrefixTk (Symbol ":") $ if isIndentedMode then typeExprInd <* newline else typeExpr

  hasExplicitEffs <- peekToken <&> \case Just (Symbol "@", _) -> True; _ -> False
  (effs, effsSr) <- if isIndentedMode then effectsNewlineMaybe else effectsMaybe

  -- Parse body expression
  expr' <-
    if isIndentedMode
      then
        outdent >> newline >> symbol "->" >> indBlockExpr
      else
        oneOf $ [(PredSym "->", anyToken *> expr False)] <> [(PredTk Indent, indBlockExpr) | isInd]

  if isJust retTypeMaybe || hasExplicitEffs
    then do
      -- No types on closure parameters, type specifier on the let statement
      let r = case retTypeMaybe of Just x -> x; _ -> (A.TUnit, def)
      let e = (A.EClosure (params <&> second (const Nothing)) expr', srcRangeOf name expr')
      let t = (A.TFunc (params <&> snd) r effs, sr0 `srcRangeOf` params `srcRangeOf` r `srcRangeOf` effsSr)
      if isRec
        then
          pure (A.SRecLet name t e, srcRangeOf name e)
        else
          pure (A.SLet (A.DName (fst name) False, snd name) (Just t) e, srcRangeOf name e)
    else do
      -- Closure parameters have types, return type of closure & effects are inferred
      when isRec $ throw (srcRangeOf sr0 params) "Recursive function must have explicit return type"
      let e = (A.EClosure (params <&> second Just) expr', srcRangeOf name expr')
      pure (A.SLet (A.DName (fst name) False, snd name) Nothing e, srcRangeOf name e)

setStmt :: (Args) => Bool -> IO A.Stmt
setStmt isInd = do
  name <- kw KwSet *> vName
  e <- symbol "=" *> indBlockOrExpr isInd
  pure (A.SAssign name e, srcRangeOf name e)

foreachStmt :: (Args) => Bool -> IO A.Stmt
foreachStmt isInd = do
  d <- kw KwForeach *> destructure
  inExpr <- kw KwIn *> expr False
  body <- oneOf $ (PredKw KwThen, kw KwThen *> expr False) : [(PredTk Indent, indBlockExpr) | isInd]
  pure (A.SForEach d inExpr body, srcRangeOf d body)

loopStmt :: (Args) => Bool -> IO A.Stmt
loopStmt isInd = do
  _ <- kw KwLoop
  body <- oneOf $ (PredSym "{", doBlockExpr) : [(PredTk Indent, indBlockExpr) | isInd]
  pure (A.SLoop body, srcRangeOf body body)

matchExpr :: (Args) => Bool -> IO A.Expr
matchExpr isInd = do
  (_, startSr) <- kw KwMatch
  scrutinee <- expr False
  -- TODO Change src range to use sr of "}" or Outdent
  branches <-
    oneOf
      $ [(PredSym "{", symbol "{" *> list1 (patternBranch False) (PredSym ";") <* symbol "}")]
      <> [(PredTk Indent, indent *> many1 (PredNot $ PredTk Outdent) (patternBranch True <* newline) <* outdent) | isInd]
  pure (A.EMatch scrutinee branches, srcRangeOf startSr (snd (lastList1 branches).expr))

patternBranch :: (Args) => Bool -> IO A.MatchBranch
patternBranch isInd = do
  pat <- pattern'
  guardMaybe <- opt (PredSym "|") (symbol "|" *> expr False)
  body <- oneOf $ [(PredSym "->", symbol "->" *> expr False)] <> [(PredTk Indent, indBlockExpr) | isInd]
  pure $ A.MatchBranch {A.pattern = pat, A.guard = guardMaybe, A.expr = body}

pattern' :: (Args) => IO A.Pattern
pattern' =
  oneOf
    [ (PredUnderscore, exactVName "_" <&> first (const A.PIgnore)),
      (PredTName, dConsPattern),
      (PredVName, vName <&> first A.PName),
      (PredSym "(", tuplePattern)
    ]

dConsPattern :: (Args) => IO A.Pattern
dConsPattern = do
  name@(_, sr0) <- tName
  peekToken >>= \case
    Just (Symbol "(", _) -> do
      _ <- anyToken
      args <- list1 pattern' (PredSym ",")
      (_, sr1) <- symbol ")"
      pure (A.PDataCons name (toList args), srcRangeOf sr0 sr1)
    Just (Symbol "{", _) -> do
      (_, startSr) <- anyToken
      fields <- list (PredNot $ PredSym "}") recordFieldPattern (PredSym ",")
      (_, endSr) <- symbol "}"
      pure (A.PRecord name fields, srcRangeOf startSr endSr)
    _ -> pure (A.PDataCons name [], sr0)

recordFieldPattern :: (Args) => IO (VNameL, A.Pattern)
recordFieldPattern = do
  fieldName <- vName
  patternMaybe <- optWithPrefixTk (Kw KwAs) pattern'
  case patternMaybe of
    Nothing -> pure (fieldName, first A.PName fieldName)
    Just pat -> pure (fieldName, pat)

tuplePattern :: (Args) => IO A.Pattern
tuplePattern = do
  (_, startSr) <- symbol "("
  p0 <- pattern'
  List1 p1 ps <- many1 (PredSym ",") (symbol "," *> pattern')
  (_, endSr) <- symbol ")"
  pure (A.PTuple $ List2 p0 p1 ps, srcRangeOf startSr endSr)

isChainPrefixOf :: List1 A.AccessorChainPart -> List1 A.AccessorChainPart -> Bool
isChainPrefixOf xs ys = (toList xs <&> fst) `isPrefixOf` (toList ys <&> fst)

mkUpdateExpr :: A.Expr -> [(List1 A.AccessorChainPart, A.Expr)] -> SrcRange -> IO A.Expr
mkUpdateExpr e parts sr = do
  forM_ (zip [0 :: Int ..] parts) $ \(i, (p, _)) -> do
    forM_ (zip [0 :: Int ..] parts) $ \(i', (p', _)) -> do
      unless (i == i') $ do
        when (p `isChainPrefixOf` p')
          $ throw (srcRangeOf p p) "Field is set multiple times"
  pure (A.EUpdate e parts, sr)

--
-- Parser combinator
--

type IOL a = IO (a, SrcRange)

type Args = (?tokens :: Var IO [TokenL], HasCallStack)

peekToken :: (Args) => IO (Maybe TokenL)
peekToken = do
  ts <- getVar ?tokens
  pure $ head ts

anyToken :: (Args) => IO TokenL
anyToken = do
  ts <- getVar ?tokens
  case ts of
    (t : _) -> do
      modVar ?tokens tail
      pure t
    _ -> throw (def :: SrcRange) "Unexpected end of file"

curLoc :: (Args) => IO SrcRange
curLoc = do
  t <- peekToken
  case t of
    Just (_, sr) -> pure sr
    _ -> pure def

kw :: (Args) => Keyword -> IOL Keyword
kw k = do
  (t, sr) <- anyToken
  case t of
    Kw x | x == k -> pure (x, sr)
    _ -> expectedXGotTok sr ("keyword '" <> kwToText k <> "'") t

expectedXGotTok :: (HasSrcRange r, Args, HasCallStack) => r -> Text -> Token -> IO a
expectedXGotTok sr ex t = throw sr $ "Expected " <> ex <> ", got " <> prettyPrintToken t

expectedXGotReadTok :: (Args, HasCallStack) => Text -> IO a
expectedXGotReadTok ex = do
  (got, sr) <-
    peekToken <&> \case
      Just (t, sr') -> (prettyPrintToken t, sr')
      _ -> ("{EOF}", def)
  throw sr $ "Expected " <> ex <> ", got " <> got

intLit :: (Args) => IOL Int64
intLit = do
  (t, sr) <- anyToken
  case t of
    IntLiteral i -> pure (i, sr)
    _ -> expectedXGotTok sr "integer" t

vName :: (Args) => IOL VName
vName = do
  (t, sr) <- anyToken
  case t of
    Ident i -> pure (i, sr)
    _ -> expectedXGotTok sr "value name" t

exactVName :: (Args) => Text -> IOL Text
exactVName name = do
  (t, sr) <- anyToken
  case t of
    Ident i | un i == name -> pure (name, sr)
    _ -> expectedXGotTok sr ("'" <> name <> "'") t

tName :: (Args) => IOL TName
tName = do
  (t, sr) <- anyToken
  case t of
    TypeName i -> pure (i, sr)
    _ -> expectedXGotTok sr "type name" t

anyName :: (Args) => IOL Text
anyName = do
  (t, sr) <- anyToken
  case t of
    Ident i -> pure (un i, sr)
    TypeName i -> pure (un i, sr)
    _ -> expectedXGotTok sr "name" t

symbol :: (Args) => Text -> IOL Text
symbol c = do
  (t, sr) <- anyToken
  unless (t == Symbol c) $ expectedXGotTok sr ("'" <> c <> "'") t
  pure (c, sr)

stringLit :: (Args) => IOL Text
stringLit = do
  (t, sr) <- anyToken
  case t of
    StringLiteral s -> pure (s, sr)
    _ -> expectedXGotTok sr "string literal" t

indent :: (Args) => IO SrcRange
indent = do
  (t, sr) <- anyToken
  unless (t == Indent) $ expectedXGotTok sr "indent" t
  pure sr

outdent :: (Args) => IO SrcRange
outdent = do
  (t, sr) <- anyToken
  unless (t == Outdent) $ expectedXGotTok sr "outdent" t
  pure sr

newline :: (Args) => IO SrcRange
newline = do
  (t, sr) <- anyToken
  unless (t == Newline) $ expectedXGotTok sr "newline" t
  pure sr

many :: (Args) => Pred -> IO a -> IO [a]
many pr p = do
  let go acc = do
        predMatch pr >>= \case
          False -> pure acc
          True -> do
            x <- p
            go (x : acc)
  go [] <&> reverse

many1 :: (Args) => Pred -> IO a -> IO (List1 a)
many1 pr p = do
  x <- p
  xs <- many pr p
  pure $ List1 x xs

list :: (Args) => Pred -> IO a -> Pred -> IO [a]
list startPred p sep =
  predMatch startPred >>= \case
    False -> pure []
    True -> do
      x <- p
      let go acc =
            predMatch sep >>= \case
              False -> pure acc
              True -> do
                consumePred sep
                y <- p
                go $ y : acc
      go [x] <&> reverse

list1 :: (Args) => IO a -> Pred -> IO (List1 a)
list1 p sep = do
  x0 <- p
  let go acc =
        predMatch sep >>= \case
          False -> pure acc
          True -> do
            consumePred sep
            x <- p
            go $ x : acc

  xs <- go [] <&> reverse
  pure $ List1 x0 xs

(<*) :: IO a -> IO b -> IO a
x <* y = do
  x' <- x
  _ <- y
  pure x'

(*>) :: IO a -> IO b -> IO b
x *> y = do
  _ <- x
  y

-- This is used instead of pattern matching on peekToken when there is no fallthrough case
-- A list of valid next tokens is added to the error message
oneOf :: (Args) => [(Pred, IO a)] -> IO a
oneOf xs = do
  let go :: (Args) => [(Pred, IO a)] -> IO (Maybe a)
      go [] = pure Nothing
      go ((pr, y) : ys) = do
        predMatch pr >>= \case
          True -> y <&> Just
          False -> do
            go ys

  go xs >>= \case
    Just x -> pure x
    _ -> do
      loc <- curLoc

      let f = \case
            PredTk t -> prettyPrintToken t
            PredVName -> "{valueName}"
            PredUnderscore -> "_"
            PredTName -> "{TypeName}"
            PredSym s -> s
            PredKw k -> kwToText k
            PredInt -> "{integer}"
            PredNot p -> "not " <> f p
            PredMany ps -> T.intercalate " " (f <$> ps)
            PredOneOf ps -> T.intercalate ", " (f <$> ps)
            PredAlways -> "{any}"

      let exs = xs <&> (fst >>> f >>> ("\t" <>))

      got <-
        peekToken <&> \case
          Just (t, _) -> prettyPrintToken t
          _ -> "{EOF}"

      let err = "Expected one of:\n" <> T.intercalate "\n" exs <> "\nGot: " <> got
      throw loc err

opt :: (Args) => Pred -> IO a -> IO (Maybe a)
opt pr p =
  predMatch pr >>= \case
    True -> Just <$> p
    False -> pure Nothing

optSymbol :: (Args) => Text -> IO (Maybe (Text, SrcRange))
optSymbol s = opt (PredTk $ Symbol s) $ symbol s

optWithPrefixTk :: (Args) => Token -> IO a -> IO (Maybe a)
optWithPrefixTk t p = do
  peekToken >>= \case
    Just (t', _) | t == t' -> anyToken >> Just <$> p
    _ -> pure Nothing

predMatch :: (Args) => Pred -> IO Bool
predMatch p' = do
  let go :: (Args) => [TokenL] -> Pred -> IO Bool
      go ts = \case
        PredTk t ->
          case ts of
            ((t', _) : _) | t' == t -> pure True
            _ -> pure False
        PredVName ->
          case ts of
            ((Ident _, _) : _) -> pure True
            _ -> pure False
        PredUnderscore ->
          case ts of
            ((Ident (VName "_"), _) : _) -> pure True
            _ -> pure False
        PredTName ->
          case ts of
            ((TypeName _, _) : _) -> pure True
            _ -> pure False
        PredSym s ->
          case ts of
            ((Symbol s', _) : _) | s == s' -> pure True
            _ -> pure False
        PredKw x ->
          case ts of
            ((Kw x', _) : _) | x == x' -> pure True
            _ -> pure False
        PredInt ->
          case ts of
            ((IntLiteral _, _) : _) -> pure True
            _ -> pure False
        PredNot p -> not <$> go ts p
        PredMany [] -> pure True
        PredMany (p : ps) -> do
          x <- go ts p
          if x then go (tail ts) (PredMany ps) else pure False
        PredOneOf ps -> anyM (go ts) ps
        PredAlways -> pure True

  ts <- getVar ?tokens
  go ts p'

-- Assumes the predicate has already been matched
consumePred :: (Args) => Pred -> IO ()
consumePred = \case
  PredTk _ -> void anyToken
  PredVName -> void anyToken
  PredUnderscore -> void anyToken
  PredTName -> void anyToken
  PredSym _ -> void anyToken
  PredKw _ -> void anyToken
  PredInt -> void anyToken
  PredNot _ -> pure ()
  PredMany [] -> pure ()
  PredMany (_ : ps) -> void anyToken >> consumePred (PredMany ps)
  PredOneOf ps -> do
    let go [] = pure ()
        go (p : ps') = do
          matches <- predMatch p
          if matches
            then consumePred p
            else go ps'
    go ps
  PredAlways -> pure ()
