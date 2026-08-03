-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

-- We go back
module Driver where

import Back.MirToJs (JsOutput, toJs)
import Control.Concurrent.Async (async, wait)
import Control.Exception (Exception, throwIO)
import Control.Monad (forM, when)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.HashMap.Strict qualified as HM
import Data.HashTable.IO qualified as HT
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8')
import Data.Text.IO qualified as TIO
import Data.Time (diffUTCTime, getCurrentTime)
import Error
import Front.Ast (Ast)
import Front.AstPp qualified
import Front.Hir (Hir)
import Front.HirFns (showHir)
import Front.LexPost (convertTokenStream)
import Front.Lexer (lexMoorhen)
import Front.Macros (expandMacros)
import Front.Parser
import Front.Tc.Tc (typeCheckPackage)
import MhPrelude
import Mid.HirToMir (toMir)
import Mid.Mir (Mir)
import Mid.Optimiser (optimisePackage)
import Names
import SrcLoc
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeBaseName, takeExtension, (<.>), (</>))
import System.IO (IOMode (WriteMode), hPutStrLn, withFile)
import Timings (Timings (..))

newtype CompileException = CompileException Text
  deriving (Show, Eq, Generic)
  deriving anyclass (Exception, Newtype)

byteStringToTextOrThrow :: ByteString -> IO Text
byteStringToTextOrThrow bs = case decodeUtf8' bs of
  Left e -> throwIO $ CompileException $ tShow e
  Right x -> pure x

parseFile :: FilePath -> Maybe Text -> FilePath -> Bool -> IO (Ast, Timings)
parseFile srcPath srcMaybe dumpDir writeAsts = do
  let name = takeBaseName srcPath
  src <- case srcMaybe of
    Nothing -> BS.readFile srcPath >>= byteStringToTextOrThrow
    Just x -> pure x

  let mkLexerErr :: Text -> IO a
      mkLexerErr x =
        throwIO $ CompileException $ formatError True $ Error ErrLexer SevError (SrcRange srcPath def def) x

  lexingStartTime <- getCurrentTime
  (tokens, lexingEndTime, lexingPostTime) <- case lexMoorhen srcPath src of
    Left e -> mkLexerErr $ T.pack e
    Right x -> do
      lexingEndTime <- getCurrentTime
      convertTokenStream x >>= \case
        Left e -> throwIO $ CompileException $ formatError True e
        Right x' -> do
          lexingPostEndTime <- getCurrentTime
          pure (x', lexingEndTime, diffUTCTime lexingPostEndTime lexingEndTime)

  when writeAsts
    $ withFile (dumpDir </> name <.> ".tokens.txt") WriteMode
    $ flip TIO.hPutStr
    $ T.unlines
    $ tokens
    <&> \(t, sr) -> tShow (getLineNum sr) <> " " <> tShow t

  parsingStartTime <- getCurrentTime
  ast <-
    parseMoorhenAst srcPath tokens >>= \case
      Left e -> throwIO $ CompileException $ formatError True e
      Right a -> pure a
  parsingEndTime <- getCurrentTime

  macrosStartTime <- getCurrentTime
  ast' <-
    expandMacros ast srcPath >>= \case
      Left e -> throwIO $ CompileException $ formatError True e
      Right a -> pure a
  macrosEndTime <- getCurrentTime

  when writeAsts $ do
    withFile (dumpDir </> name <.> ".ast.hs.txt") WriteMode
      $ flip hPutStrLn
      $ show ast'
    withFile (dumpDir </> name <.> ".ast.txt") WriteMode
      $ flip TIO.hPutStrLn
      $ Front.AstPp.prettyPrint ast'

  pure
    ( ast',
      def
        { lexing = diffUTCTime lexingEndTime lexingStartTime,
          lexingPost = lexingPostTime,
          parsing = diffUTCTime parsingEndTime parsingStartTime,
          macroExpansion = diffUTCTime macrosEndTime macrosStartTime
        }
    )

compilePackage :: PkgName -> FilePath -> [(PkgName, Hir)] -> Bool -> Bool -> FilePath -> IO (Hir, Timings)
compilePackage pkgName dirOrFilePath depPkgs writeAsts writeHir outDir = do
  (asts', timings1) <- findSrcFiles dirOrFilePath pkgName outDir writeAsts
  let asts = HM.fromList asts'

  depPkgs' <- HT.fromList depPkgs
  typeCheckingStartTime <- getCurrentTime
  (tcErrs, hirMaybe) <- typeCheckPackage pkgName depPkgs' asts
  let errsString = T.intercalate "\n\n" $ tcErrs <&> formatError True
  hir <- case hirMaybe of
    Nothing -> throwIO $ CompileException errsString
    Just hir -> pure hir
  when (notNull tcErrs) $ TIO.putStrLn errsString
  typeCheckingEndTime <- getCurrentTime
  let typeCheckingTime = diffUTCTime typeCheckingEndTime typeCheckingStartTime

  when writeHir $ do
    x <- showHir hir
    withFile (outDir </> T.unpack (un pkgName) <.> ".hir.hs.txt") WriteMode
      $ flip TIO.hPutStrLn x

  pure (hir, timings1 {typeChecking = typeCheckingTime})

findSrcFiles :: FilePath -> PkgName -> FilePath -> Bool -> IO ([(Namespace, Ast)], Timings)
findSrcFiles dirOrFilePath pkg dumpDir writeAsts = do
  isDir <- doesDirectoryExist dirOrFilePath
  files <-
    if isDir
      then do
        filesRelPath <- listDirectory dirOrFilePath <&> filter (takeExtension >>> (== ".mh"))
        let filesAbsPath = (dirOrFilePath </>) <$> filesRelPath
        let namespaces =
              filesRelPath <&> \path ->
                Namespace $ un pkg <> "/" <> T.pack (takeBaseName path)
        pure $ zip namespaces filesAbsPath
      else do
        pure [(Namespace $ un pkg <> "/", dirOrFilePath)]

  as <- forM files $ \(ns, path) -> do
    async (parseFile path Nothing dumpDir writeAsts) <&> (ns,)

  xs <- forM as $ \(ns, a) -> do
    (ast, timings) <- wait a
    pure (ns, ast, timings)

  pure (fst2Of3 <$> xs, mconcat $ thd3 <$> xs)

compileBuiltins :: Bool -> Bool -> FilePath -> FilePath -> IO (Hir, Mir, Timings)
compileBuiltins outputDebugAst outputDebugHir builtinsDir outDir = do
  (hir, t) <-
    compilePackage
      (PkgName "#builtins")
      builtinsDir
      def
      outputDebugAst
      outputDebugHir
      outDir

  loweringStartTime <- getCurrentTime
  let pkgs = HM.fromList [(PkgName "#builtins", hir)]
  mir' <- toMir pkgs (PkgName "#builtins")
  loweringEndTime <- getCurrentTime

  optimisingStartTime <- getCurrentTime
  let pkgs' = HM.fromList [(PkgName "#builtins", mir')]
  mir <- optimisePackage pkgs' (PkgName "#builtins") -- Needed for setting values in VDefs
  optimisingEndTime <- getCurrentTime

  pure
    ( hir,
      mir,
      t
        { lowering = diffUTCTime loweringEndTime loweringStartTime,
          optimising = diffUTCTime optimisingEndTime optimisingStartTime
        }
    )

typeCheckStLib :: Bool -> Bool -> FilePath -> Hir -> FilePath -> IO (Hir, Timings)
typeCheckStLib outputDebugAst outputDebugHir stlibDir builtinsHir outDir = do
  compilePackage
    (PkgName "#stlib")
    stlibDir
    [(PkgName "#builtins", builtinsHir)]
    outputDebugAst
    outputDebugHir
    outDir

compileStLib :: (Hir, Mir) -> Hir -> IO (Mir, Timings)
compileStLib (builtinsHir, builtinsMir) hir = do
  let pkgs = HM.fromList [(PkgName "#builtins", builtinsHir), (PkgName "#stlib", hir)]

  loweringStartTime <- getCurrentTime
  mir' <- toMir pkgs (PkgName "#stlib")
  loweringEndTime <- getCurrentTime

  optimisingStartTime <- getCurrentTime
  let pkgs' = HM.fromList [(PkgName "#builtins", builtinsMir), (PkgName "#stlib", mir')]
  mir <- optimisePackage pkgs' (PkgName "#stlib")
  optimisingEndTime <- getCurrentTime

  pure
    ( mir,
      def
        { lowering = diffUTCTime loweringEndTime loweringStartTime,
          optimising = diffUTCTime optimisingEndTime optimisingStartTime
        }
    )

genPackageMir :: HashMap PkgName Hir -> HashMap PkgName Mir -> PkgName -> Bool -> IO (Mir, Timings)
genPackageMir pkgsHir pkgsMir pkgName optimise = do
  loweringStartTime <- getCurrentTime
  mir <- toMir pkgsHir pkgName
  loweringEndTime <- getCurrentTime

  optimisingStartTime <- getCurrentTime
  mir' <-
    if optimise
      then do
        let pkgsMir' = HM.insert pkgName mir pkgsMir
        optimisePackage pkgsMir' pkgName
      else pure mir
  optimisingEndTime <- getCurrentTime

  let timings =
        def
          { lowering = diffUTCTime loweringEndTime loweringStartTime,
            optimising = diffUTCTime optimisingEndTime optimisingStartTime
          }

  pure (mir', timings)

genJS :: PkgName -> HashMap PkgName Mir -> IO (JsOutput, Timings)
genJS pkgName pkgsMir' = do
  toJsStartTime <- getCurrentTime
  let n = T.tail $ un pkgName
  js <- toJs pkgsMir' ".." n
  toJsEndTime <- getCurrentTime

  pure (js, def {transpiling = diffUTCTime toJsEndTime toJsStartTime})
