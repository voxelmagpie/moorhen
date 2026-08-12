-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module CmdLine (ArgsException (..), extractArgs, Config (..), Action (..)) where

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
data Arg = ArgFilePathOrCmd String | ArgSetting String (Maybe String)

type ArgProcessor = ExceptT ArgsException (State ([Arg], Config))

getNextArg :: ArgProcessor (Maybe Arg)
getNextArg =
  gets fst >>= \case
    [] -> pure Nothing
    (y : ys) -> do
      modify' $ first $ const ys
      pure $ Just y

-- For getting args after "--" to pass to the compiled program
getAllRemainingArgStrings :: ArgProcessor [String]
getAllRemainingArgStrings = do
  xs <- gets fst
  modify' $ first (const [])
  pure $ xs <&> \case
    ArgFilePathOrCmd x -> x
    ArgSetting x Nothing -> x
    ArgSetting x (Just y) -> x <> "=" <> y

-- e.g. moorhen --xyz build foo.moorhen --build-mode=debug lol.moorhen -a --stlib res/stlib/
extractArgs :: [String] -> Either ArgsException Config
extractArgs xs = case runState (runExceptT go) (xs', def) of
  (Left err, _) -> Left err
  (Right _, (_, y)) -> Right y
  where
    go :: ArgProcessor ()
    go = do
      -- Get configuration argument
      getNextArg >>= \case
        -- Actions
        Just (ArgFilePathOrCmd cmd) -> do
          hasCmdAlready <- gets (snd >>> (.action)) <&> isJust
          when hasCmdAlready $ throwError $ ArgsException "Multiple commands specified"
          case cmd of
            "tests" -> do
              modify' $ second $ \s -> s {action = Just ActTests}
            "build" -> do
              getNextArg >>= \case
                Just (ArgFilePathOrCmd path) -> do
                  modify' $ second $ \s -> s {action = Just $ ActBuild path}
                _ -> throwError $ ArgsException "Expected source file or package path"
            "help" -> do
              modify' $ second $ \s -> s {action = Just ActHelp}
            "check" -> do
              getNextArg >>= \case
                Just (ArgFilePathOrCmd path) -> do
                  modify' $ second $ \s -> s {action = Just $ ActCheck path}
                _ -> throwError $ ArgsException "Expected source file or package path"
            _ ->
              throwError
                $ ArgsException
                $ "Unrecognised action: "
                <> T.pack cmd
                <> "\nRun 'moorhen help' to get a list of actions"
          go
        -- Settings
        Just (ArgSetting option valueMaybe) -> do
          let hasVal = isJust valueMaybe
          let checkNoVal = when hasVal $ throwError $ ArgsException "Expected path, got value (=)"
          case option of
            "--out-dir" -> do
              checkNoVal
              getNextArg >>= \case
                Just (ArgFilePathOrCmd path) -> do
                  modify' $ second $ \s -> s {outDir = Just path}
                _ -> throwError $ ArgsException "Expected output executable file path"
            "--" -> do
              as <- getAllRemainingArgStrings
              modify' $ second $ \s -> s {args = as}
            "--builtins-path" -> do
              checkNoVal
              getNextArg >>= \case
                Just (ArgFilePathOrCmd path) -> do
                  modify' $ second $ \s -> s {builtinsPath = Just path}
                _ -> throwError $ ArgsException "Expected directory path"
            "--stlib-path" -> do
              checkNoVal
              getNextArg >>= \case
                Just (ArgFilePathOrCmd path) -> do
                  modify' $ second $ \s -> s {stlibPath = Just path}
                _ -> throwError $ ArgsException "Expected directory path"
            "--timings" ->
              modify' $ second $ \s -> s {timings = True}
            "--debug-ast" -> modify' $ second $ \s -> s {outputDebugAst = True}
            "--debug-hir" -> modify' $ second $ \s -> s {outputDebugHir = True}
            "--debug-mir" -> modify' $ second $ \s -> s {outputDebugMir = True}
            "--help" -> modify' $ second $ \s -> s {help = True}
            _ -> throwError $ ArgsException $ "Unknown configuration option: " <> T.pack option
          go
        Nothing -> pure ()
    xs' =
      xs <&> \s ->
        if "-" `isPrefixOf` s
          then case elemIndex '=' s of
            Just i -> ArgSetting (take i s) (Just $ drop (i + 1) s)
            _ -> ArgSetting s Nothing
          else
            ArgFilePathOrCmd s

data Action = ActTests | ActBuild FilePath | ActHelp | ActCheck FilePath
  deriving (Show, Eq)

data Config = Config
  { action :: Maybe Action,
    outDir :: Maybe String,
    args :: [String],
    builtinsPath :: Maybe FilePath,
    stlibPath :: Maybe FilePath,
    timings :: Bool,
    outputDebugAst :: Bool,
    outputDebugHir :: Bool,
    outputDebugMir :: Bool,
    help :: Bool
  }
  deriving (Show, Eq, Generic, Default)
