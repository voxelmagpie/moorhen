-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

{
{-# LANGUAGE NoDuplicateRecordFields #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE NoStrictData #-}
{-# OPTIONS_GHC -O2 #-}

module Front.Lexer(lexMoorhen) where

import Front.Tokens
import Data.Text.Read qualified as TextRead
import Data.Text (Text)
import Data.Text qualified as T
import Names (VName(..), TName(..))
import SrcLoc (SrcLoc(..), SrcRange(..))
import Data.Functor ((<&>))
import Data.Foldable (Foldable (foldl'))
import Control.Arrow ((<<<), (>>>))
import Data.Char(ord)
import Data.List(isPrefixOf)
import Data.Int(Int64)
}

%wrapper "monad-strict-text"
%encoding "latin1"

$whitespace = [\ \r\f\v]

tokens :-

  "//" [^\n]* ;
  \n ^ $whitespace { \ _ _ -> alexError "Non-tab whitespace at start of line" }
  \n ^ [$whitespace \t]+ [\n]+ ;
  \n ^ [$whitespace \t]+ /{eof} ;
  \n ^ [$whitespace \t]+ "//" [^\n]* ;
  $whitespace+ ;
  \n+ { tok $ const Newline' }
  \n ^ \t+ { tok countTabs }
  \t+ { \ _ _ -> alexError "Tab not at start of line" }

  -- Floats: Match a negative float if preceded by an open bracket, whitespace, or tab (to distinguish from subtraction)
  -- E.g. (-3), x-3
  [\(\[\{ $whitespace \t] ^ "-" [0-9]+ \. [[0-9]]+ { tok FloatLiteral' }

  -- Floats: Match a float if not preceded by a dot (to distinguish from member access)
  -- E.g. 0.0, x.0.0
  [^\.] ^ [0-9]+ \. [[0-9]]+ { tok FloatLiteral' }

  -- Ints: Match a negative int if preceded by an open bracket, whitespace, or tab (to distinguish from subtraction)
  [\(\[\{ $whitespace \t] ^ "-" [0-9]+ { tok $ parseInt }

  [0-9]+ { tok $ parseInt }

  "-"? 0 [xX] [0-9a-fA-F]+ { tok parseHexInt }
  "-"? 0 [bB] [01]+ { tok parseBinInt }

  [\[\]\{\}\(\)] { tok Symbol' }
  \=\= | \!\= | \>\= | \<\= | \*\* | \:\: | \-\> | \+\+ | \.\.  { tok Symbol' }
  [\`\~\!\@\#\$\%\^\&\*\-\=\+\;\:\,\<\.\>\/\?\\\|\'\#]  { tok Symbol' }


  let  { tok $ const $ Kw' KwLet }
  iterator  { tok $ const $ Kw' KwIterator }
  type   { tok $ const $ Kw' KwType }
  builtin  { tok $ const $ Kw' KwBuiltin }
  data   { tok $ const $ Kw' KwData }
  and  { tok $ const $ Kw' KwAnd }
  or   { tok $ const $ Kw' KwOr }
  import   { tok $ const $ Kw' KwImport }
  as   { tok $ const $ Kw' KwAs }
  if   { tok $ const $ Kw' KwIf }
  then   { tok $ const $ Kw' KwThen }
  else   { tok $ const $ Kw' KwElse }
  match  { tok $ const $ Kw' KwMatch }
  mut  { tok $ const $ Kw' KwMut }
  set  { tok $ const $ Kw' KwSet }
  mod   { tok $ const $ Kw' KwMod }
  trait  { tok $ const $ Kw' KwTrait }
  for  { tok $ const $ Kw' KwFor }
  throw  { tok $ const $ Kw' KwThrow }
  try  { tok $ const $ Kw' KwTry }
  catch  { tok $ const $ Kw' KwCatch }
  finally  { tok $ const $ Kw' KwFinally }
  foreach  { tok $ const $ Kw' KwForeach }
  in   { tok $ const $ Kw' KwIn }
  loop   { tok $ const $ Kw' KwLoop }
  break  { tok $ const $ Kw' KwBreak }
  continue   { tok $ const $ Kw' KwContinue }
  rec { tok $ const $ Kw' KwRec }
  trait { tok $ const $ Kw' KwTrait }
  where { tok $ const $ Kw' KwWhere }
  true  { tok $ const $ Kw' KwTrue }
  false { tok $ const $ Kw' KwFalse }
  yield { tok $ const $ Kw' KwYield }

  
  [[a-z] \_] [[a-zA-Z] [0-9] \_]* { tok $ Ident' . VName }  
  [A-Z] [[a-zA-Z] [0-9] \_]* { tok $ TypeName' . TName }
  
  \" ([^\"] | (\\\"))* \" { \i@(AlexPn _ row _, _, _, _) l -> tok' (mkStringTok row) i l }

{

type Token'L' = (Token', (SrcLoc, SrcLoc))

-- Only allow non-control-code ASCII for now. Will either support unicode later or switch to ByteString input.
hasInvalidChars :: Text -> Bool
hasInvalidChars = T.any isInvalid
  where
    isInvalid c = (ord c < 32 && not (c `elem` ['\t', '\n', '\r'])) || ord c > 127 

lexMoorhen :: FilePath -> Text -> Either String [Token'L]
lexMoorhen fileName src =
  if hasInvalidChars src then 
    Left "File contains non-ASCII or null/control character(s)" 
  else 
    run
  where
    -- Repeatedly scan tokens until alexMonadScan returns Nothing
    go :: Alex [Token'L']
    go = do
      tokenMaybe <- alexMonadScan
      case tokenMaybe of
        Nothing -> pure []
        Just t -> fmap (t :) go
    run = 
      case runAlex src go of
        Right x -> Right $ x <&> \(t, (a, b)) -> (t, SrcRange fileName a b)
        Left e -> 
          -- Alex prefixes errors with "lexical error...". Capitalize the 'l' for consistency.
          if "lexical" `isPrefixOf` e then 
            Left $ 'L' : drop 1 e
          else
            Left e

alexEOF :: Alex (Maybe Token'L')
alexEOF = pure Nothing

eof :: user -> AlexInput -> Int -> AlexInput -> Bool
eof _ _ _ (_, _, _, t) = T.null t

tok :: (Text -> Token') -> AlexInput -> Int -> Alex (Maybe Token'L')
tok mkTok (pos, _, _, remainingText) len =
  let tokenText = T.take len remainingText in
    pure $ Just (mkTok tokenText, makeSrcRange pos len)

tok' :: (Text -> Alex Token') -> AlexInput -> Int -> Alex (Maybe Token'L')
tok' mkTok (pos, _, _, remainingText) len = do
  let tokenText = T.take len remainingText
  t <- mkTok tokenText
  pure $ Just (t, makeSrcRange pos len)


makeSrcRange :: AlexPosn -> Int -> (SrcLoc, SrcLoc)
makeSrcRange (AlexPn i row _) len = (l, r)
  where
    l = SrcLoc row i
    r = SrcLoc row (i+len-1)

countTabs :: Text -> Token'
countTabs = T.length >>> Indent'

-- Parsing cannot fail as the lexer rule guarantees that it is a valid number
parseInt :: Text -> Token'
parseInt s = case TextRead.signed TextRead.decimal s of
  Left e -> error e
  Right (x, _) -> IntLiteral' x

parseHexInt :: Text -> Token'
parseHexInt s = case TextRead.signed TextRead.hexadecimal s of
  Left e -> error e
  Right (x, _) -> IntLiteral' x

parseBinInt' :: Text -> Int64
parseBinInt' t | T.head t == '-' = -(parseBinInt' $ T.tail t)
parseBinInt' textWithPrefix = result'
  where
    chars = T.unpack $ T.drop 2 textWithPrefix
    
    f (result, add) '0' = (result, add*2)
    f (result, add) _ = (result + add, add*2)

    (result', _) = foldl' f (0 :: Int64, 1) $ reverse chars 

parseBinInt :: Text -> Token'
parseBinInt t = IntLiteral' $ parseBinInt' t

stripQuotes :: Text -> Text
stripQuotes t =  T.tail $ T.take (T.length t - 1) t 

getEscChar :: Int -> Char -> Alex Char
getEscChar row = \case
  'a' -> pure '\a'
  'b' -> pure '\b'
  'f' -> pure '\f'
  'n' -> pure '\n'
  'r' -> pure '\r'
  't' -> pure '\t'
  '"' -> pure '\"'
  '\'' -> pure '\''
  '\\' -> pure '\\'
  _ -> alexError $ "Invalid escape character on line " <> show row

-- Strips quotation marks and processes escape characters
mkStringTok :: Int -> Text -> Alex Token'
mkStringTok row s = (StringLiteral' . T.pack) <$> go (T.unpack $ stripQuotes s)
  where
    go :: String -> Alex String
    go ('\\' : x : xs) = do
      c <- getEscChar row x
      (c :) <$> go xs
    go (x : xs) = (x :) <$> go xs
    go [] = pure []


}
