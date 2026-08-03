-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Error (Error (..), ErrorSeverity (..), ErrorStage (..), formatError, formatSimpleTextError) where

import Control.Exception (Exception)
import Data.Text qualified as T
import MhPrelude
import SrcLoc

data Error = Error ErrorStage ErrorSeverity SrcRange Text
  deriving (Show, Generic, Exception, Eq)

data ErrorSeverity = SevError | SevWarning | SevHint
  deriving (Show, Generic, Eq)

data ErrorStage = ErrLexer | ErrParser | ErrMacroExpansion | ErrTypeChecker
  deriving (Show, Generic, Eq)

srcLocColour :: Text
srcLocColour = "\x1b[34;1m" -- Blue, bold

errorColour :: Text
errorColour = "\x1b[31;1m" -- Red, bold

emphasisColour :: Text
emphasisColour = "\x1b[0;1m" -- Default, bold

warningColour :: Text
warningColour = "\x1b[33;1m" -- Yellow, bold

noteColour :: Text
noteColour = "\x1b[32;1m" -- Green, bold

resetColour :: Text
resetColour = "\x1b[0m"

type UseTerminalColours = Bool

formatError :: UseTerminalColours -> Error -> Text
formatError colours (Error stage sev (SrcRange fp sl _) msg) =
  let (errCol, sevStr) = case sev of
        SevError -> (errorColour, "error\n")
        SevWarning -> (warningColour, "warning\n")
        SevHint -> (noteColour, "note\n")
      c x = if colours then x else ""
   in T.concat
        [ c errCol,
          case stage of
            ErrLexer -> "Lex "
            ErrParser -> "Parse "
            ErrMacroExpansion -> "Macro expansion "
            ErrTypeChecker -> "Type ",
          sevStr,
          c emphasisColour,
          msg,
          c resetColour,
          "\nIn ",
          c srcLocColour,
          T.pack fp,
          if sl.line == 0 then "" else ":" <> tShow sl.line,
          c resetColour,
          "\n"
        ]

formatSimpleTextError :: Text -> Text
formatSimpleTextError msg = T.concat [errorColour, "Error: ", msg, resetColour]
