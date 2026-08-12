-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Main (main) where

import Back.MirToJs
import CmdLine
import Control.Exception (handle, throwIO)
import Control.Monad (when)
import Data.HashMap.Strict qualified as HM
import Data.Maybe (fromMaybe, isJust)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Driver
import Embed
import Error
import MhPrelude
import Names (PkgName (PkgName))
import System.Directory (createDirectoryIfMissing, getSymbolicLinkTarget)
import System.Environment (getArgs)
import System.Exit (die)
import System.FilePath (takeBaseName, takeDirectory, (<.>), (</>))
import System.IO (IOMode (WriteMode), withFile)
import Tests
import Timings (writeTimingsFile)

main :: IO ()
main = do
  let onArgsEx (ArgsException msg) = die $ T.unpack $ formatSimpleTextError msg
  handle @CompileException (un >>> T.unpack >>> die) $ handle @ArgsException onArgsEx main'

main' :: IO ()
main' = do
  args <- getArgs
  do
    cfg <- case extractArgs args of Left e -> throwIO e; Right x -> pure x

    selfDir <- getSymbolicLinkTarget "/proc/self/exe" <&> takeDirectory

    let builtinsDir = fromMaybe (selfDir </> "builtins.mh") cfg.builtinsPath
    let stlibDir = fromMaybe (selfDir </> "stlib") cfg.stlibPath

    let outDir = fromMaybe "out" cfg.outDir

    when (cfg.outputDebugAst || cfg.outputDebugHir || cfg.outputDebugMir) $ createDirectoryIfMissing False outDir

    case cfg.action of
      Just ActHelp ->
        TIO.putStrLn helpFile
      Just ActTests -> do
        builtins <- compileBuiltins cfg.outputDebugAst cfg.outputDebugHir cfg.outputDebugMir builtinsDir outDir
        runTests builtins cfg.outputDebugAst cfg.outputDebugHir cfg.outputDebugMir builtinsMjs outDir
      Nothing -> putStrLn "Moorhen compiler v0.1.0"
      Just action -> do
        (builtinsHir, builtinsMir, builtinsTimings) <-
          compileBuiltins cfg.outputDebugAst cfg.outputDebugHir cfg.outputDebugMir builtinsDir outDir

        srcPath <- case action of
          ActBuild x -> pure x
          ActCheck x -> pure x

        let bn = T.pack (takeBaseName srcPath)
        when (isJust $ T.find (\c -> c == '/' || c == '#') bn) $ die "Source path contains invalid characters"
        let pkgName = PkgName $ "#" <> bn

        (stLibHir, stLibTimings) <- typeCheckStLib cfg.outputDebugAst cfg.outputDebugHir stlibDir builtinsHir outDir

        case action of
          ActBuild _ -> do
            createDirectoryIfMissing False outDir

            (stlibMir, stLibTimings2) <- compileStLib cfg.outputDebugMir outDir (builtinsHir, builtinsMir) stLibHir True

            let pkgs = [(PkgName "#builtins", builtinsHir), (PkgName "#stlib", stLibHir)]

            (hir, hirGenTimings) <-
              handle @CompileException (un >>> T.unpack >>> die)
                $ compilePackage pkgName srcPath pkgs cfg.outputDebugAst cfg.outputDebugHir outDir

            let pkgsHir =
                  HM.fromList [(PkgName "#builtins", builtinsHir), (PkgName "#stlib", stLibHir), (pkgName, hir)]

            let pkgsMir = HM.fromList [(PkgName "#builtins", builtinsMir), (PkgName "#stlib", stlibMir)]

            (mir', genMirTimings) <- genPackageMir cfg.outputDebugMir outDir pkgsHir pkgsMir pkgName True

            let pkgsMir' = HM.insert pkgName mir' pkgsMir
            (js, toJsTimings) <- genJS pkgName pkgsMir'

            withFile (outDir </> T.unpack js.fileNameNoExt <.> "mjs") WriteMode $ \f -> do
              TIO.hPutStrLn f js.js
              TIO.hPutStrLn f builtinsMjs
              -- TODO Check there is a main function during/after type checking
              TIO.hPutStrLn f $ filterFqn (un pkgName <> "/:main") <> "()"
            withFile (outDir </> T.unpack js.fileNameNoExt <.> "mjs.map") WriteMode $ flip TIO.hPutStrLn js.sourceMap

            let appTimings = hirGenTimings <> genMirTimings <> toJsTimings
            when cfg.timings
              $ writeTimingsFile
                (outDir </> "timings.txt")
                [("builtins", builtinsTimings), ("stlib", stLibTimings <> stLibTimings2), ("app", appTimings)]
          --
          ActCheck _ -> do
            let pkgs = [(PkgName "#builtins", builtinsHir), (PkgName "#stlib", stLibHir)]
            (_hir, timings) <-
              handle @CompileException (un >>> T.unpack >>> die)
                $ compilePackage pkgName srcPath pkgs cfg.outputDebugAst cfg.outputDebugHir outDir

            when cfg.timings
              $ writeTimingsFile
                (outDir </> "timings.txt")
                [("builtins", builtinsTimings), ("stlib", stLibTimings), ("app", timings)]
