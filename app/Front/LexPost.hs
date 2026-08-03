-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.LexPost (convertTokenStream, convertTokenStream1Line) where

import Control.Exception (throwIO, try)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Error
import Front.Tokens
import MhPrelude
import SrcLoc

-- Tracks indentation, converts raw newlines and tabs from Token'
-- into Indent/Newline/Outdent that can be used by the parser
convertTokenStream :: [Token'L] -> IO (Either Error [TokenL])
convertTokenStream =
  try . go'
  where
    go' :: [Token'L] -> IO [TokenL]
    go' [] = pure []
    go' inputTokensList'@((_, firstTokenSr) : _) = do
      let inputTokensList = dropWhile (fst >>> (== Newline')) inputTokensList'
      ind <- newIORef (0 :: Int) -- Measured in tabs, not Indentation tokens
      indStack <- newIORef []
      lastSr <- newIORef firstTokenSr
      let go :: [Token'L] -> [TokenL] -> IO [TokenL]
          go [] acc = do
            -- Close any remaining open indentation blocks at end of file
            indStackLen <- readIORef indStack <&> length
            sr <- readIORef lastSr
            let unind = replicate indStackLen (Outdent, sr)
            pure $ (Newline, sr) : unind <> acc
          go ((Newline', sr) : ts) acc = do
            -- Look ahead to get indentation level after this newline
            let (newInd, ts') = case dropWhile (fst >>> (== Newline')) ts of
                  ((Indent' i, _) : ts'') -> (i, ts'')
                  ts'' -> (0, ts'')
            curInd <- readIORef ind
            writeIORef lastSr sr

            if newInd == curInd
              then
                go ts' $ (Newline, sr) : acc
              else do
                writeIORef ind newInd
                let deltaInd = newInd - curInd
                if newInd > curInd
                  then do
                    modifyIORef' indStack (deltaInd :)
                    go ts' ((Indent, sr) : acc)
                  else do
                    -- Loops through the indentation stack to check this is a valid number of outdents.
                    -- Tab counts are summed from the stack (amnt) until they equal the outdent amount (-deltaInd).
                    -- 'ctr' tracks the number of indentation blocks closed.
                    let countInds _ _ [] = throwIO $ Error ErrLexer SevError sr "Out of place indented block"
                        countInds ctr amnt (x : xs) =
                          let newAmnt = amnt + x
                           in if newAmnt == -deltaInd
                                then
                                  pure $ ctr + 1
                                else
                                  if newAmnt > -deltaInd
                                    then
                                      throwIO $ Error ErrLexer SevError sr "Out of place indented block"
                                    else
                                      countInds (ctr + 1) newAmnt xs
                    indStack' <- readIORef indStack
                    indCnt <- countInds (0 :: Int) (0 :: Int) indStack'
                    modifyIORef' indStack $ drop indCnt
                    let outdents = replicate indCnt [(Outdent, sr), (Newline, sr)]
                    go ts' (((Newline, sr) : concat outdents) <> acc)

          -- If we get an Indent here then it is not after a newline and is therefore invalid as
          -- tabs cannot be midway through a line and the first line in a file can't be indented
          go ((Indent' _, sr) : _) _ =
            throwIO $ Error ErrLexer SevError sr $ "Unexpected indentation on line " <> tShow (getLineNum sr)
          go ((y, sr) : ts) acc = do
            writeIORef lastSr sr
            -- No transformation here
            case convertSimpleToken y of
              Just t -> go ts $ (t, sr) : acc
              Nothing -> error "convertTokenStream: unexpected Newline' or Indent' here"
      -- List was built in reverse order
      reverse <$> go inputTokensList []

convertTokenStream1Line :: [Token'L] -> IO (Either Error [TokenL])
convertTokenStream1Line = try . go'
  where
    go' :: [Token'L] -> IO [TokenL]
    go' [] = pure []
    go' ts' = reverse <$> go [] ts'

    go :: [TokenL] -> [Token'L] -> IO [TokenL]
    go acc [] = pure acc
    go acc ((t, sr) : ts) = case convertSimpleToken t of
      Just t' -> go ((t', sr) : acc) ts
      Nothing -> throwIO $ Error ErrLexer SevError sr "Unexpected newline or indentation in 1-line source snippet"

-- Converts a raw token to a processed token, ignoring Newline' and Indent'
convertSimpleToken :: Token' -> Maybe Token
convertSimpleToken = \case
  Ident' x -> Just (Ident x)
  Kw' x -> Just (Kw x)
  TypeName' x -> Just (TypeName x)
  FloatLiteral' x -> Just (FloatLiteral x)
  IntLiteral' x -> Just (IntLiteral x)
  StringLiteral' x -> Just (StringLiteral x)
  Symbol' x -> Just (Symbol x)
  Newline' -> Nothing
  Indent' _ -> Nothing
