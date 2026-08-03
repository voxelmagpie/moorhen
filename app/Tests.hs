-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tests where

import Back.MirToJs
import Control.Monad (forM, forM_, when)
import Data.ByteString qualified as BS
import Data.Char (isSpace)
import Data.HashMap.Strict qualified as HM
import Data.HashTable.IO qualified as HT
import Data.List (isSuffixOf, sort)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Time (diffUTCTime, getCurrentTime)
import Driver
import Error
import Front.Hir (Hir)
import Front.LexPost (convertTokenStream)
import Front.Lexer (lexMoorhen)
import Front.Parser
import Front.Tc.Tc (typeCheckPackage)
import MhPrelude
import Mid.HirToMir (toMir)
import Mid.Mir (Mir)
import Mid.Optimiser (optimisePackage)
import Names (Namespace (Namespace), PkgName (PkgName))
import System.Directory (createDirectoryIfMissing, listDirectory)
import System.Exit (die)
import System.FilePath ((<.>), (</>))
import System.IO (IOMode (WriteMode), withFile)
import Timings (Timings (..), writeTimingsFile)

compileTest :: (Hir, Mir) -> String -> Bool -> Bool -> FilePath -> IO (Mir, Timings)
compileTest builtins testName writeAsts writeHir outDir = do
  let pkgName = PkgName $ T.pack $ '#' : testName

  (hir, timings) <-
    compilePackage
      pkgName
      ("tests" </> testName <.> ".mh")
      [(PkgName "#builtins", fst builtins)]
      writeAsts
      writeHir
      outDir

  let pkgs = HM.fromList [(PkgName "#builtins", fst builtins), (pkgName, hir)]

  loweringStartTime <- getCurrentTime
  mir' <- toMir pkgs pkgName
  loweringEndTime <- getCurrentTime

  optimisingStartTime <- getCurrentTime
  let pkgs' = HM.fromList [(PkgName "#builtins", snd builtins), (pkgName, mir')]
  mir <- optimisePackage pkgs' pkgName
  optimisingEndTime <- getCurrentTime

  pure
    ( mir,
      timings
        { lowering = diffUTCTime loweringEndTime loweringStartTime,
          optimising = diffUTCTime optimisingEndTime optimisingStartTime
        }
    )

runTcErrTests :: Hir -> IO ()
runTcErrTests builtins = do
  fullSrc <- BS.readFile "tc_err_tests.mh" >>= byteStringToTextOrThrow
  let tests = T.splitOn "// --- //\n" fullSrc <&> T.dropWhile isSpace
  forM_ tests $ \src -> do
    tokens <- case lexMoorhen "tc_err_tests.mh" src of
      Left e -> die $ T.unpack $ "tc_err_tests.mh lexer error:\n" <> T.pack e <> "\n" <> src
      Right x ->
        convertTokenStream x >>= \case
          Left e -> die $ T.unpack $ "tc_err_tests.mh lexer error:\n" <> formatError True e <> "\n" <> src
          Right x' -> pure x'
    astMaybe <- parseMoorhenAst "tc_err_tests.mh" tokens
    ast <- case astMaybe of
      (Left e) -> die $ T.unpack $ "tc_err_tests.mh parser error:\n" <> formatError True e <> "\n" <> src
      (Right a) -> pure a
    depPkgs' <- HT.fromList [(PkgName "#builtins", builtins)]
    let asts = HM.singleton (Namespace "#/main") ast
    (tcErrs, _) <- typeCheckPackage (PkgName "#") depPkgs' asts
    -- TIO.putStrLn $ T.unlines $ tcErrs <&> formatError True
    when (null tcErrs) $ die $ T.unpack $ "Type checker error test did not fail:\n" <> src

runTests :: (Hir, Mir, Timings) -> Bool -> Bool -> Text -> FilePath -> IO ()
runTests (builtinsHir, builtinsMir, builtinsTimings) writeAsts writeHir builtinsJs outDir = do
  runTcErrTests builtinsHir

  putStrLn "Compiling tests..."

  createDirectoryIfMissing False "out"

  tests <- listDirectory "tests" <&> filter (".mh" `isSuffixOf`)
  let testNames = tests <&> dropTail (T.length ".mh") & sort

  testsMirTimings <- forM testNames $ \n -> do
    putStrLn $ "Compiling " <> n
    x <- compileTest (builtinsHir, builtinsMir) n writeAsts writeHir outDir
    pure (T.pack n, x)

  let testsMir = testsMirTimings <&> \(n, (mir, _)) -> (PkgName $ "#" <> n, mir)

  let pkgsMir = HM.fromList $ (PkgName "#builtins", builtinsMir) : testsMir

  toJsStartTime <- getCurrentTime
  js <- toJs pkgsMir ".." "tests"
  toJsEndTime <- getCurrentTime

  let mainFqns = testNames <&> \n -> filterFqn $ "#" <> T.pack n <> "/:main"

  withFile "out/tests.mjs" WriteMode $ \f -> do
    TIO.hPutStrLn f "// This file can be run in NodeJS\n"
    TIO.hPutStrLn f js.js
    TIO.hPutStrLn f builtinsJs
    TIO.hPutStr f "\n\n\n"

    forM_ (zip testNames mainFqns) $ \(n, fqn) -> do
      src <- BS.readFile ("tests/" <> n <> ".mh") >>= byteStringToTextOrThrow
      let ex = T.drop 2 $ must $ head $ T.lines src
      TIO.hPutStrLn f $ T.concat ["var x = ", fqn, "();"]
      TIO.hPutStrLn f
        $ T.concat
          ["if (x != ", ex, ") { throw new Error(\"Test failed: ", T.pack n, ", got \" + x + \", expected \" + ", ex, "); }"]
      TIO.hPutStrLn f $ T.concat ["console.log(\"Test passed: ", T.pack n, "\");"]
    TIO.hPutStrLn f "process.exit()"

  writeTimingsFile "out/timings.txt"
    $ ("builtins", builtinsTimings)
    : ("Tests JS", def {transpiling = diffUTCTime toJsEndTime toJsStartTime})
    : (second snd <$> testsMirTimings)

  putStrLn "Finished compiling tests"
