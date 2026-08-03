-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

{- HLINT ignore "Use head" -}
-- Transpiles MIR to JavaScript
module Back.MirToJs (toJs, JsOutput (..), filterFqn) where

import Control.Monad (forM, forM_, unless, void, when)
import Control.Monad.Reader (MonadIO (liftIO), ReaderT (runReaderT), asks)
import Control.Monad.ST (runST)
import Data.Bits (Bits (shiftL, shiftR), (.&.), (.|.))
import Data.Char (chr, intToDigit, ord)
import Data.Functor (($>))
import Data.HashMap.Strict qualified as HM
import Data.HashTable.IO qualified as HT
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Kind qualified as K
import Data.List (elemIndex)
import Data.Maybe (catMaybes, isJust, isNothing)
import Data.STRef (modifySTRef', newSTRef, readSTRef)
import Data.Text qualified as T
import GHC.Stack (HasCallStack)
import MhPrelude
import Mid.Mir (Mir)
import Mid.Mir qualified as M
import Names
import SrcLoc
import Vars

data JsOutput = JsOutput
  { js :: Text, -- {fileNameNoExt}.mjs, builtins.mjs needs to be appended to this when writing the file
    sourceMap :: Text, -- {fileNameNoExt}.map, optional
    fileNameNoExt :: Text
  }

unitExpr :: M.Expr'
unitExpr = M.EDoBlock [] Nothing

newtype ConstUid = ConstUid Int
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

class (MonadVars m) => MonadTr m where
  type Pkg m :: K.Type
  getPkg :: PkgName -> m (Pkg m)
  allPkgs :: m [(PkgName, Pkg m)]
  getVDefs :: Pkg m -> m [(VFqn, M.VDef)]
  getVDef :: VFqn -> m M.VDef
  resetFnState :: m ()
  mkTmpVarName :: m Text
  addFilePath :: FilePath -> m Int
  getFilePaths :: m [FilePath]
  addName :: Text -> m Int
  getNames :: m [Text]
  getSourceMaps :: m [Text]
  getAndSetSourceIndex :: Int -> m Int
  getAndSetLineNumber :: Int -> m Int
  getAndSetNameIdx :: Int -> m Int
  setFile :: FilePath -> m ()
  getCurrentFileIdx :: m Int
  getConstUid :: M.Const -> m ConstUid
  getAllConsts :: m [(ConstUid, M.Const)]
  addLine' :: Text -> Text -> m ()
  getLines :: m [Text]

toJs :: HashMap PkgName Mir -> FilePath -> Text -> IO JsOutput
toJs mir sourceRootRel fileName = do
  s <- State mir <$> newIORef 0 <*> newIORef [] <*> newIORef [] <*> newIORef [] <*> newIORef [] <*> newIORef 0 <*> newIORef 0 <*> newIORef 0 <*> newIORef (-99) <*> HT.new <*> HT.new <*> newIORef 0
  flip runReaderT s $ trPkg sourceRootRel fileName

constToText :: M.Const -> Text
constToText = \case
  M.CInt i -> tShow i
  M.CI32 i -> tShow i <> "|0"
  M.CFloat x -> x
  M.CBool x -> if x then "true" else "false"
  M.CString x -> "\"" <> T.pack (reverse $ filterString "" $ T.unpack x) <> "\""
    where
      filterString :: String -> String -> String
      filterString result [] = result
      filterString result (c : cs) = case c of
        '\n' -> filterString ('n' : '\\' : result) cs
        '"' -> filterString ('"' : '\\' : result) cs
        '\\' -> filterString ('\\' : '\\' : result) cs
        '\f' -> filterString ('f' : '\\' : result) cs
        '\r' -> filterString ('r' : '\\' : result) cs
        '\t' -> filterString ('t' : '\\' : result) cs
        '\v' -> filterString ('v' : '\\' : result) cs
        '\0' -> filterString ('0' : '\\' : result) cs
        _
          | c < ' ' || ord c == 0x7f ->
              let hex = ord c
                  h1 = intToDigit (hex `shiftR` 4)
                  h2 = intToDigit (hex .&. 0xF)
               in filterString (h2 : h1 : 'x' : '\\' : result) cs
        _ -> filterString (c : result) cs
  M.CFn fqn ->
    filterFqn (un fqn)
  M.CVec es -> do
    let es' = es <&> constToText
    -- TODO This is wrong. We want to refer to the inner constants by their id
    T.concat ["[", T.intercalate ", " es', "]"]

trPkg :: (MonadTr m) => FilePath -> Text -> m JsOutput
trPkg sourceRootRel fileName = do
  allPkgs' <- allPkgs

  forM_ allPkgs' $ \(_pkgName, pkg) -> do
    vDefs <- getVDefs pkg
    forM_ vDefs $ \(vFqn, vDef) ->
      forM_ vDef.exprMaybe $ \vDefExpr'@(vDefExpr, sr) -> do
        setFile $ filePath $ snd vDef.name
        let name' = filterFqn (un vFqn)
        addLine [("// " <> un vFqn, snd vDef.name, Nothing)]
        case vDefExpr of
          M.EClosure fnId -> do
            resetFnState
            trClosure fnId sr (Just name') (Just $ fst vDef.name)
          _ -> do
            case vDef.value of
              Just v -> do
                e <- trConst v
                addLine
                  [ ("const ", snd vDef.name, Nothing),
                    (name', snd vDef.name, Just $ fst vDef.name),
                    (T.concat [" = ", e, ";"], sr, Nothing)
                  ]
              _ -> do
                resetFnState
                addLine
                  [ ("let ", snd vDef.name, Nothing),
                    (name', snd vDef.name, Just $ fst vDef.name),
                    (" = [false, function() {", sr, Nothing)
                  ]
                e'' <- trExpr vDefExpr'
                unless (e'' == "undefined")
                  $ addLine [(T.concat ["return ", e'', ";"], sr, Nothing)]
                addLine [("}];", sr, Nothing)]
        addLine [("", sr, Nothing)]

  allConsts <- getAllConsts
  allConsts' <- forM allConsts $ \(uid, constVal) ->
    if isSmallConst constVal
      then pure Nothing
      else
        pure $ Just $ T.concat ["const $c", tShow (un uid), " = ", constToText constVal, ";\n"]

  lines' <- getLines <&> T.unlines

  let js =
        T.concat
          [ "//# sourceMappingURL=",
            fileName,
            ".mjs.map\n",
            "\"use strict\";\n",
            "\n\n",
            lines',
            T.concat $ catMaybes allConsts'
          ]

  let extraLinesBefore = 4

  allFiles <- getFilePaths

  mapLines <- getSourceMaps
  let mappings = T.intercalate ";" mapLines
  names <- getNames

  let sourceMap =
        T.unlines
          [ "{",
            "\t\"version\": 3,",
            "\t\"file\": \"" <> fileName <> ".mjs\",",
            "\t\"sourceRoot\": \"" <> T.pack sourceRootRel <> "\",",
            "\t\"sources\": [" <> T.intercalate ", " ((\f -> "\"" <> T.pack f <> "\"") <$> allFiles) <> "],",
            "\t\"names\": [" <> T.intercalate ", " ((\f -> "\"" <> f <> "\"") <$> names) <> "],",
            "\t\"mappings\": \"" <> T.replicate extraLinesBefore ";" <> mappings <> "\"",
            "}"
          ]

  pure $ JsOutput js sourceMap fileName

isSmallConst :: M.Const -> Bool
isSmallConst = \case
  M.CInt x | x >= -9999 || x <= 99999 -> True
  M.CI32 x | x >= -9999 || x <= 99999 -> True
  M.CFloat t | T.length t <= 5 -> True
  M.CBool {} -> True
  M.CString t | T.length t == 0 -> True
  M.CFn {} -> True
  _ -> False

uidToText :: M.LocalVarUid -> Text
uidToText = un >>> tShow >>> ("x" <>)

trClosure :: (MonadTr m) => M.Fn -> SrcRange -> Maybe Text -> Maybe Text -> m ()
trClosure fn sr cloName cloMhName = do
  let params = T.intercalate "," $ fn.params <&> \(uid, _, _, _) -> uidToText uid

  let asyncKw = if fn.isAsync then "async " else ""
  let nameComment = case cloMhName of Just n -> " // " <> n; _ -> ""
  let retKw = if isNothing cloName then "return " else ""
  addLine
    $ [(retKw <> asyncKw <> "function ", sr, Nothing)]
    <> (case cloName of Just n -> [(n, sr, cloMhName)]; _ -> [])
    <> [(T.concat ["(", params, ") {", nameComment], sr, Nothing)]

  case fn.expr of
    (M.EClosure fn', sr') -> do
      trClosure fn' sr' Nothing Nothing
    _ -> do
      e'' <- trExpr fn.expr
      unless (e'' == "undefined")
        $ addLine [(T.concat ["return ", e'', ";"], sr, Nothing)]

  addLine [("}", sr, Nothing)]

inlinableFunctionOperators :: HashMap VFqn Text
inlinableFunctionOperators =
  HM.fromList
    $ (\(a, b) -> (VFqn $ "#builtins/:" <> a, " " <> b <> " "))
    <$> [ ("RealBuiltins.add", "+"),
          ("RealBuiltins.sub", "-"),
          ("RealBuiltins.mul", "*"),
          ("RealBuiltins.div", "/"),
          ("RealBuiltins.rem", "%"),
          ("RealEq.eq", "=="),
          ("RealEq.neq", "!="),
          ("RealBuiltins.gt", ">"),
          ("RealBuiltins.gte", ">="),
          ("RealBuiltins.lt", "<"),
          ("RealBuiltins.lte", "<="),
          ("IntBuiltins.add", "+"),
          ("IntBuiltins.sub", "-"),
          ("IntBuiltins.mul", "*"),
          ("IntBuiltins.div", "/"),
          ("IntBuiltins.rem", "%"),
          ("IntEq.eq", "=="),
          ("IntEq.neq", "!="),
          ("I32Eq.eq", "=="),
          ("I32Builtins.neq", "!="),
          ("I32Builtins.bAnd", "&"),
          ("I32Builtins.bOr", "|"),
          ("I32Builtins.bXor", "^"),
          ("IntBuiltins.gt", ">"),
          ("IntBuiltins.gte", ">="),
          ("IntBuiltins.lt", "<"),
          ("IntBuiltins.lte", "<="),
          ("BoolEq.eq", "=="),
          ("BoolEq.neq", "!="),
          ("StringEq.eq", "=="),
          ("StringEq.neq", "!=")
        ]

inlinableUnaryFunctionOperators :: HashMap VFqn Text
inlinableUnaryFunctionOperators =
  HM.fromList
    $ first (\a -> VFqn $ "#builtins/:" <> a)
    <$> [ ("RealBuiltins.neg", "-"),
          ("RealBuiltins.noOp", "+"),
          ("IntBuiltins.neg", "-"),
          ("IntBuiltins.noOp", "+"),
          ("BoolBuiltins.not", "!"),
          ("I32Builtins.bNot", "~")
        ]

trConst :: (MonadTr m) => M.Const -> m Text
trConst c =
  if isSmallConst c
    then pure $ constToText c
    else do
      uid <- getConstUid c
      pure $ "$c" <> tShow (un uid)

trExpr :: (MonadTr m) => M.Expr -> m Text
trExpr (e, sr) = case e of
  M.ELoadConst c -> trConst c
  M.EMkVec es -> buildJsListFromExprs sr es
  M.EVar uid -> pure $ uidToText uid
  M.EGlobal fqn -> do
    vDef <- getVDef fqn
    let fqn' = filterFqn $ un fqn
    let isClosure = \case M.EClosure {} -> True; _ -> False
    case (vDef.exprMaybe, vDef.value) of
      (Just (e', _), Nothing) | not $ isClosure e' -> do
        -- Evaluate thunk
        tmp <- mkTmpVarName
        addLine [(T.concat ["const " <> tmp <> " = $0builtins$1$2LazyFns$3eval(", fqn', ");"], sr, Nothing)]
        pure tmp
      _ -> pure fqn'
  M.EFnCall (M.EGlobal (VFqn "#builtins/:lazy"), _) argsExprs _ _retType -> do
    tmp <- mkTmpVarName
    e' <- trExpr $ must $ head argsExprs
    addLine [("const " <> tmp <> " = [false, " <> e' <> "];", sr, Nothing)]
    pure tmp
  M.EFnCall (M.EGlobal fqn, _) argsExprs _ _retType
    | isJust $ HM.lookup fqn inlinableUnaryFunctionOperators -> do
        let op = must $ HM.lookup fqn inlinableUnaryFunctionOperators
        assertM $ length argsExprs == 1
        arg <- trExpr $ must $ head argsExprs
        pure $ op <> arg
  M.EFnCall (M.EGlobal fqn, _) argsExprs _ _retType
    | isJust $ HM.lookup fqn inlinableFunctionOperators -> do
        let op = must $ HM.lookup fqn inlinableFunctionOperators
        assertM $ length argsExprs == 2
        args <- forM argsExprs trExpr
        pure $ "(" <> T.intercalate op args <> ")"
  M.EFnCall callee es fnIsAsync retType -> do
    callee' <- trExpr callee
    es' <- forM (toList es) trExpr
    tmp <- mkTmpVarName
    let awaitKw = if fnIsAsync then "await " else ""
    let call = T.concat [awaitKw, callee', "(", T.intercalate ", " es', ")"]
    if retType == M.TUnit
      then do
        addLine [(call <> ";", sr, Nothing)]
        pure "undefined"
      else do
        addLine [(T.concat ["const ", tmp, " = ", call, ";"], sr, Nothing)]
        pure tmp
  M.EIf condExpr thenExpr elseExpr t -> do
    tmp <-
      if t == M.TUnit
        then
          pure "undefined"
        else do
          tmp <- mkTmpVarName
          addLine [(T.concat ["let ", tmp, ";"], sr, Nothing)]
          pure tmp
    condExpr' <- trExpr condExpr
    addLine [(T.concat ["if (", condExpr', ") {"], sr, Nothing)]
    thenExpr' <- trExpr thenExpr
    unless (tmp == "undefined") $ addLine [(T.concat [tmp, " = ", thenExpr', ";"], sr, Nothing)]
    when (fst elseExpr /= unitExpr) $ do
      addLine [(T.concat ["} else {"], sr, Nothing)]
      elseExpr' <- trExpr elseExpr
      unless (tmp == "undefined") $ addLine [(T.concat [tmp, " = ", elseExpr', ";"], sr, Nothing)]
    addLine [("}", sr, Nothing)]
    pure tmp
  M.EDoBlock [] Nothing -> pure "undefined"
  M.EDoBlock [] (Just e') -> trExpr e'
  M.EDoBlock ss eMaybe -> do
    tmp <- mkTmpVarName
    when (isJust eMaybe) $ addLine [(T.concat ["let ", tmp, ";"], sr, Nothing)]
    addLine [("{", sr, Nothing)]
    forM_ ss trStmt
    forM_ eMaybe $ \e' -> do
      e'' <- trExpr e'
      addLine [(T.concat [tmp, " = ", e'', ";"], sr, Nothing)]
    addLine [("}", sr, Nothing)]
    pure $ if isJust eMaybe then tmp else "undefined"
  M.EClosure fnId -> do
    cloName <- mkTmpVarName
    trClosure fnId sr (Just cloName) Nothing
    pure cloName
  M.EThrow e' typStr -> do
    e'' <- trExpr e'
    addLine [("throw new MhEx(\"" <> un typStr <> "\", " <> e'' <> ");", sr, Nothing)]
    pure "undefined"
  M.ETry tryExpr catches finallyMaybe -> do
    tmp <- mkTmpVarName
    addLine [(T.concat ["let ", tmp, ";"], sr, Nothing)]
    addLine [("try {", sr, Nothing)]
    tryVal <- trExpr tryExpr
    addLine [(tmp <> " = " <> tryVal <> ";", sr, Nothing)]
    addLine [("}", sr, Nothing)]
    addLine [("catch (e) { if (e instanceof MhEx) {", sr, Nothing)]
    forM_ (zip (toList catches) [0 :: Int ..]) $ \((typStr, uid, sr', e'), i) -> do
      let elseMaybe = if i == 0 then "" else "else "
      addLine [(elseMaybe <> "if (" <> "e.type == \"" <> un typStr <> "\"" <> ") {", sr', Nothing)]
      addLine [("let " <> uidToText uid <> " = e.value;", sr', Nothing)]
      e'' <- trExpr e'
      addLine [(T.concat [tmp, " = ", e'', ";"], sr', Nothing)]
      addLine [("}", sr, Nothing)]
    addLine [("} else { throw e; }}", sr, Nothing)]
    forM_ finallyMaybe $ \fin -> do
      addLine [("finally {", sr, Nothing)]
      _ <- trExpr fin
      addLine [("}", sr, Nothing)]

    pure tmp
  M.EAnd lhs rhs -> do
    tmp <- mkTmpVarName
    addLine [(T.concat ["let ", tmp, ";"], sr, Nothing)]
    lhs' <- trExpr lhs
    addLine [("if (" <> lhs' <> ") {", sr, Nothing)]
    rhs' <- trExpr rhs
    addLine [(tmp <> " = " <> rhs' <> ";", sr, Nothing)]
    addLine [("} else { " <> tmp <> " = false; }", sr, Nothing)]
    pure tmp
  M.EOr lhs rhs -> do
    tmp <- mkTmpVarName
    addLine [(T.concat ["let ", tmp, ";"], sr, Nothing)]
    lhs' <- trExpr lhs
    addLine [("if (!(" <> lhs' <> ")) {", sr, Nothing)]
    rhs' <- trExpr rhs
    addLine [(tmp <> " = " <> rhs' <> ";", sr, Nothing)]
    addLine [("} else { " <> tmp <> " = true; }", sr, Nothing)]
    pure tmp
  M.EProduct es -> buildJsListFromExprs sr $ toList es
  M.EIndex e' i _ -> do
    e'' <- trExpr e'
    pure $ T.concat [e'', "[", tShow i, "]"]
  M.EBreak lbl -> addLine [("break " <> uidToText lbl <> ";", sr, Nothing)] $> "undefined"
  M.EContinue lbl -> addLine [("continue " <> uidToText lbl <> ";", sr, Nothing)] $> "undefined"
  M.EImplicitCast e' ->
    trExpr e'
  M.ESignExtendInt e' -> trExpr e'
  M.EIntToF64 e' -> trExpr e'
  M.ECastNumber e' toType -> do
    e'' <- trExpr e'
    pure $ case toType of
      M.TI32 -> "(" <> e'' <> " | 0)"
      _ -> e''
  M.ESum _ idx e' -> do
    e'' <- trExpr e'
    pure $ "[" <> tShow idx <> "|0, " <> e'' <> "]"
  M.EUnreachable msg -> do
    addLine [("throw new Error(" <> tShow msg <> ");", sr, Nothing)]
    pure "undefined"
  M.ESumTypeActiveIndex e' -> do
    e'' <- trExpr e'
    pure $ e'' <> "[0]"
  M.ESumTypeGet e' -> do
    e'' <- trExpr e'
    pure $ e'' <> "[1]"

buildJsListFromExprs :: (MonadTr m) => SrcRange -> [M.Expr] -> m Text
buildJsListFromExprs sr es = do
  tmp <- mkTmpVarName

  xs <- forM (toList es) trExpr
  addLine [(T.concat ["const ", tmp, " = [", T.intercalate ", " xs, "];"], sr, Nothing)]
  pure tmp

trStmt :: (MonadTr m) => M.Stmt -> m ()
trStmt (s, sr) = case s of
  M.SLet uid nameMaybe mut e -> do
    e' <- trExpr e
    let nameComment = case nameMaybe of Just (n, _) -> " // " <> n; _ -> ""
    addLine
      [ (if mut then "let " else "const ", sr, Nothing),
        (uidToText uid, sr, nameMaybe <&> fst),
        (T.concat [" = ", e', ";", nameComment], sr, Nothing)
      ]
  M.SLetUninit uid _ -> do
    addLine [("let ", sr, Nothing), (uidToText uid, sr, Nothing), (T.concat [";"], sr, Nothing)]
  M.SRecLet uid nameMaybe e -> do
    case fst e of
      M.EClosure fnId -> do
        let cloName = uidToText uid
        trClosure fnId sr (Just cloName) (nameMaybe <&> fst)
      _ -> error "SRecLet not closure"
  M.SExpr e -> do
    void $ trExpr e
  M.SAssign uid nameMaybe e -> do
    e' <- trExpr e
    addLine
      [ (uidToText uid, sr, nameMaybe <&> fst),
        (T.concat [" = ", e', ";"], sr, Nothing)
      ]
  M.SLoop body lbl -> do
    addLine [(uidToText lbl <> ": for(;;) {", sr, Nothing)]
    _ <- trExpr body
    addLine [("}", sr, Nothing)]

-- Removes symbols that cannot appear in a JS identifier and replaces them with a dollar sign followed by
-- the base-36 encoded ASCII value of the character
filterFqn :: Text -> Text
filterFqn s = runST $ do
  cs <- newSTRef []
  forM_ (T.unpack s) $ \c -> case elemIndex c forbiddenSymbols of
    Just i ->
      let i' = chr $ if i >= 0 && i <= 9 then i + ord '0' else i + ord 'A' - 10
       in modifySTRef' cs $ \cs' -> i' : '$' : cs'
    _ -> modifySTRef' cs (c :)
  readSTRef cs <&> (reverse >>> T.pack)

forbiddenSymbols :: [Char]
forbiddenSymbols = ['#', '/', ':', '.', '$', '\'']

toBase64Char :: Int -> Char
toBase64Char x | x >= 0 && x <= 25 = chr $ x + ord 'A'
toBase64Char x | x >= 26 && x <= 51 = chr $ x - 26 + ord 'a'
toBase64Char x | x >= 52 && x <= 61 = chr $ x - 52 + ord '0'
toBase64Char x | x == 62 = '+'
toBase64Char x | x == 63 = '/'
toBase64Char _ = error "Out of range"

toVlq :: Int -> Text
toVlq i = runST $ do
  outputRev <- newSTRef []

  -- Process first 4 bits

  let absI = abs i
  value <- newSTRef absI
  do
    let signBit :: Int = (if i >= 0 then 0 else 1)
    let bits = (absI .&. 15) `shiftL` 1
    let cont :: Int = (if absI > 15 then 1 else 0) `shiftL` 5
    let x = bits .|. signBit .|. cont
    modifySTRef' outputRev (toBase64Char x :)
    modifySTRef' value (`shiftR` 4)

  -- Process remaining 5 bits at a time
  let loop = do
        v <- readSTRef value
        when (v /= 0) $ do
          let bits = v .&. 31
          let cont :: Int = (if v > 31 then 1 else 0) `shiftL` 5
          let x = bits .|. cont
          modifySTRef' outputRev (toBase64Char x :)
          modifySTRef' value (`shiftR` 5)
          loop
  loop

  readSTRef outputRev <&> (reverse >>> T.pack)

addLine :: (MonadTr m, HasSrcRange sr, HasCallStack) => [(Text, sr, Maybe Text)] -> m ()
addLine parts = do
  let l = T.concat $ parts <&> fst3

  srcIdx <- getCurrentFileIdx

  off <- newVar 0
  mapGroups <- forM parts $ \(part, sr, nameMaybe) -> do
    o <- getVar off
    setVar off $ length part -- Length of part is used as relative column offset for next part
    let loc = startLoc sr
    let lineNo = loc.line - 1
    oldIdx <- getAndSetSourceIndex srcIdx
    oldLineNo <- getAndSetLineNumber lineNo
    n <- case nameMaybe of
      Just n -> do
        assertM $ '$' `notElem` T.unpack n
        i <- addName n
        oldNameIdx <- getAndSetNameIdx i
        pure $ toVlq (i - oldNameIdx)
      _ -> pure ""
    -- TODO Column info
    pure $ toVlq o <> toVlq (srcIdx - oldIdx) <> toVlq (lineNo - oldLineNo) <> "A" <> n

  addLine' l $ T.intercalate "," mapGroups

type Tr = ReaderT State IO

data State = State
  { pkgs :: HashMap PkgName Mir,
    nextTmpId :: IORef Int,
    linesRev :: IORef [Text],
    -- One entry for every line in the generated JS file
    sourceMapRev :: IORef [Text],
    allFilePathsRev :: IORef [FilePath],
    allNames :: IORef [Text],
    lastSourceIndex :: IORef Int,
    lastLineNumber :: IORef Int,
    lastNameIdx :: IORef Int,
    currentFilePathIdx :: IORef Int,
    constToUid :: HashTable M.Const ConstUid,
    uidToConst :: HashTable ConstUid M.Const,
    nextConstUid :: IORef Int
  }

instance MonadVars Tr where
  type Var Tr = IORef
  newVar = liftIO . newIORef
  setVar v x = liftIO $ writeIORef v x
  getVar v = liftIO $ readIORef v
  modVar v f = liftIO $ modifyIORef' v f

instance MonadTr Tr where
  type Pkg Tr = Mir
  getPkg n = do
    pkgs <- asks (.pkgs)
    pure $ must $ HM.lookup n pkgs
  allPkgs = do
    pkgs <- asks (.pkgs)
    pure $ toList pkgs
  getVDefs pkg = do
    liftIO $ HT.toList pkg.vDefs
  getVDef fqn = do
    pkg <- getPkg (vFqnToPkg fqn)
    liftIO $ HT.lookup pkg.vDefs fqn <&> must
  resetFnState = do
    nextTmpId <- asks (.nextTmpId)
    liftIO $ writeIORef nextTmpId 0
  mkTmpVarName = do
    x <- asks (.nextTmpId)
    i <- liftIO $ readIORef x
    liftIO $ writeIORef x (i + 1)
    pure $ "t" <> tShow i
  addFilePath p = do
    allFilePathsRevRef <- asks (.allFilePathsRev)
    allFilePathsRev' <- liftIO $ readIORef allFilePathsRevRef
    case elemIndex p allFilePathsRev' of
      Just i ->
        -- Index in the list once it has later been reversed
        pure $ length allFilePathsRev' - i - 1
      _ -> do
        liftIO $ modifyIORef' allFilePathsRevRef (p :)
        pure $ length allFilePathsRev'
  getFilePaths = do
    allFilePathsRev <- asks (.allFilePathsRev)
    liftIO $ readIORef allFilePathsRev <&> reverse
  addName p = do
    allNames <- asks (.allNames)
    allNames' <- liftIO $ readIORef allNames
    case elemIndex p allNames' of
      Just i -> pure $ length allNames' - i - 1
      _ -> do
        liftIO $ writeIORef allNames $ p : allNames'
        pure $ length allNames'
  getNames = do
    allNames <- asks (.allNames)
    liftIO $ readIORef allNames <&> reverse
  getSourceMaps = do
    sourceMapRev <- asks (.sourceMapRev)
    liftIO $ readIORef sourceMapRev <&> reverse
  getAndSetSourceIndex idx = do
    lastSourceIndex <- asks (.lastSourceIndex)
    old <- liftIO $ readIORef lastSourceIndex
    liftIO $ writeIORef lastSourceIndex idx
    pure old
  getAndSetLineNumber no = do
    lastLineNumber <- asks (.lastLineNumber)
    old <- liftIO $ readIORef lastLineNumber
    liftIO $ writeIORef lastLineNumber no
    pure old
  getAndSetNameIdx i = do
    lastNameIdx <- asks (.lastNameIdx)
    old <- liftIO $ readIORef lastNameIdx
    liftIO $ writeIORef lastNameIdx i
    pure old
  setFile path = do
    i <- addFilePath path
    x <- asks (.currentFilePathIdx)
    liftIO $ writeIORef x i
  getCurrentFileIdx = do
    x <- asks (.currentFilePathIdx)
    liftIO $ readIORef x
  getConstUid c = do
    constsToUidRef <- asks (.constToUid)
    uidToConstRef <- asks (.uidToConst)
    uidMaybe <- liftIO $ HT.lookup constsToUidRef c
    case uidMaybe of
      Just x -> pure x
      _ -> do
        nextConstUidRef <- asks (.nextConstUid)
        uid <- liftIO $ readIORef nextConstUidRef <&> ConstUid
        liftIO $ modifyIORef' nextConstUidRef (+ 1)
        liftIO $ HT.insert uidToConstRef uid c
        liftIO $ HT.insert constsToUidRef c uid
        pure uid
  getAllConsts = do
    constsRef <- asks (.uidToConst)
    liftIO $ HT.toList constsRef
  addLine' l sm = do
    x <- asks (.linesRev)
    liftIO $ modifyIORef' x (l :)
    y <- asks (.sourceMapRev)
    liftIO $ modifyIORef' y (sm :)
  getLines = do
    x <- asks (.linesRev)
    liftIO $ readIORef x <&> reverse
