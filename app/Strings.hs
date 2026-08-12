-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Strings where

import Data.Bits (Bits (shiftR, (.&.)))
import Data.Char (intToDigit, ord)
import MhPrelude

filterString :: String -> String
filterString s = go [] s
  where
    go :: String -> String -> String
    go result [] = result
    go result (c : cs) = case c of
      '\n' -> go ('n' : '\\' : result) cs
      '"' -> go ('"' : '\\' : result) cs
      '\\' -> go ('\\' : '\\' : result) cs
      '\f' -> go ('f' : '\\' : result) cs
      '\r' -> go ('r' : '\\' : result) cs
      '\t' -> go ('t' : '\\' : result) cs
      '\v' -> go ('v' : '\\' : result) cs
      '\0' -> go ('0' : '\\' : result) cs
      _ -> go (escChar c <> result) cs

escChar :: Char -> String
escChar c =
  if c >= ' ' && ord c /= 0x7f
    then [c]
    else
      let hex = ord c
          h1 = intToDigit (hex `shiftR` 4)
          h2 = intToDigit (hex .&. 0xF)
       in '\\' : 'x' : h1 : [h2]
