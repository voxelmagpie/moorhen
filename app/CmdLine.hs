-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module CmdLine (ArgsException (..), extractArgs, Config (..)) where

import Control.Exception (Exception)
import Control.Monad (when)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State (State, gets, modify', runState)
import Data.List (elemIndex, isPrefixOf)
import Data.Maybe (isJust)
import Data.Text qualified as T
import MhPrelude

newtype ArgsException = ArgsException Text
  deriving (Show, Generic, Eq)
  deriving anyclass (Exception, Newtype)

-- If an arg begins with "-" then it is a setting, otherwise it is a file path/name
data Arg = ArgFilePath String | ArgSetting String (Maybe String)

type ArgProcessor = ExceptT ArgsException (State ([Arg], Config))

getNextArg :: ArgProcessor (Maybe Arg)
getNextArg =
  gets fst >>= \case
    [] -> pure Nothing
    (y : ys) -> do
      modify' $ first $ const ys
      pure $ Just y

peekNextArg :: ArgProcessor (Maybe Arg)
peekNextArg = gets (head . fst)

-- For getting args after "--" to pass to the compiled program
getAllRemainingArgStrings :: ArgProcessor [String]
getAllRemainingArgStrings = do
  xs <- gets fst
  modify' $ first (const [])
  pure $ xs <&> \case
    ArgFilePath x -> x
    ArgSetting x Nothing -> x
    ArgSetting x (Just y) -> x <> "=" <> y

-- e.g. moorhen build foo.moorhen --build-mode=debug lol.moorhen -a --stlib res/stlib/
extractArgs :: [String] -> Either ArgsException Config
extractArgs xs = case runState (runExceptT go1) (xs', def) of
  (Left err, _) -> Left err
  (Right _, (_, y)) -> Right y
  where
    go1 :: ArgProcessor ()
    go1 = do
      -- Get source file or directory
      peekNextArg >>= \case
        Just (ArgFilePath path) -> do
          _ <- getNextArg
          modify' $ second $ \s -> s {inputFileOrDir = Just path}
          peekNextArg >>= \case
            Just (ArgFilePath _) -> throwError $ ArgsException "Multiple input files/directories"
            _ -> go2
        _ -> go2

    go2 :: ArgProcessor ()
    go2 = do
      -- Get configuration argument
      getNextArg >>= \case
        Just (ArgSetting option valueMaybe) -> do
          let hasVal = isJust valueMaybe
          let checkNoVal = when hasVal $ throwError $ ArgsException "Expected path, got value (=)"
          case option of
            "--out-dir" -> do
              checkNoVal
              getNextArg >>= \case
                Just (ArgFilePath path) -> do
                  modify' $ second $ \s -> s {outDir = Just path}
                _ -> throwError $ ArgsException "Expected output executable file path"
            "--" -> do
              as <- getAllRemainingArgStrings
              modify' $ second $ \s -> s {args = as}
            "--builtins-path" -> do
              checkNoVal
              getNextArg >>= \case
                Just (ArgFilePath path) -> do
                  modify' $ second $ \s -> s {builtinsPath = Just path}
                _ -> throwError $ ArgsException "Expected directory path"
            "--stlib-path" -> do
              checkNoVal
              getNextArg >>= \case
                Just (ArgFilePath path) -> do
                  modify' $ second $ \s -> s {stlibPath = Just path}
                _ -> throwError $ ArgsException "Expected directory path"
            "--timings" ->
              modify' $ second $ \s -> s {timings = True}
            "--debug-ast" -> modify' $ second $ \s -> s {outputDebugAst = True}
            "--debug-hir" -> modify' $ second $ \s -> s {outputDebugHir = True}
            _ -> throwError $ ArgsException $ "Unknown configuration option: " <> T.pack option
          go2
        _ -> pure ()
    xs' =
      xs <&> \s ->
        if "-" `isPrefixOf` s
          then case elemIndex '=' s of
            Just i -> ArgSetting (take i s) (Just $ drop (i + 1) s)
            _ -> ArgSetting s Nothing
          else
            ArgFilePath s

data Config = Config
  { inputFileOrDir :: Maybe String,
    outDir :: Maybe String,
    args :: [String],
    builtinsPath :: Maybe FilePath,
    stlibPath :: Maybe FilePath,
    timings :: Bool,
    outputDebugAst :: Bool,
    outputDebugHir :: Bool
  }
  deriving (Show, Eq, Generic, Default)
