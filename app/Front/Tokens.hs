-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tokens where

import Data.Char (toLower)
import Data.Int (Int64)
import Data.Text qualified as T
import MhPrelude
import Names
import SrcLoc

data Keyword
  = KwLet
  | KwType
  | KwBuiltin
  | KwData
  | KwAnd
  | KwOr
  | KwImport
  | KwAs
  | KwIf
  | KwThen
  | KwElse
  | KwMatch
  | KwMut
  | KwSet
  | KwMod
  | KwFor
  | KwThrow
  | KwTry
  | KwCatch
  | KwFinally
  | KwForeach
  | KwIn
  | KwLoop
  | KwBreak
  | KwContinue
  | KwRec
  | KwTrait
  | KwWhere
  | KwTrue
  | KwFalse
  deriving (Show, Eq)

kwToText :: Keyword -> Text
kwToText kw = case show kw of (_ : _ : c : cs) -> T.pack $ toLower c : cs; _ -> tShow kw

-- Raw token types from lexer (before indentation processing)
data Token'
  = Ident' VName -- abc, fn, _a3, etc.
  | Kw' Keyword
  | TypeName' TName -- Abc, etc.
  | FloatLiteral' Text
  | IntLiteral' Int64
  | StringLiteral' Text
  | Symbol' Text -- @, ?, \, ::, +, &, etc.
  | Newline' -- Any number of "\n"
  | Indent' Int -- Number "\t" characters
  deriving (Eq, Show, Generic)

type Token'L = (Token', SrcRange)

-- Processed token types (after indentation handling)
data Token
  = Ident VName -- abc, fn, _a3, etc.
  | Kw Keyword
  | TypeName TName -- Abc, etc.
  | FloatLiteral Text
  | IntLiteral Int64
  | StringLiteral Text
  | Symbol Text -- @, ?, \, ::, +, &, etc.
  | Newline -- End of line (no indentation change)
  | Indent -- Start of indented block
  | Outdent -- End of indented block
  deriving (Eq, Show, Generic)

type TokenL = (Token, SrcRange)

-- Convert a token to its textual representation
prettyPrintToken :: Token -> Text
prettyPrintToken = \case
  Symbol c -> "'" <> c <> "'"
  Ident (VName x) -> "'" <> x <> "'"
  Kw kw -> kwToText kw
  TypeName (TName x) -> "'" <> x <> "'"
  FloatLiteral x -> tShow x
  IntLiteral x -> tShow x
  StringLiteral x -> "\"" <> x <> "\""
  Newline -> "newline"
  Indent -> "indent"
  Outdent -> "outdent"
