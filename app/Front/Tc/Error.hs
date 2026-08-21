-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Error where

import Control.Exception (Exception)
import Control.Monad (when)
import Error
import MhPrelude
import SrcLoc

-- This is used for control flow and does not hold the error value
-- Errors are stored in a list in the type checker state
newtype TcException = TcException ()
  deriving (Show, Generic)
  deriving anyclass (Newtype, Exception)

class (Monad m) => MonadTcError m where
  getErrsListRev :: m [Error]
  consErr :: Error -> m ()
  throwTcException :: m a

  throw :: (HasSrcRange r) => r -> Text -> m a
  throw sr msg = do
    addError SevError sr msg
    throwTcException

  addError :: (HasSrcRange r) => ErrorSeverity -> r -> Text -> m ()
  addError sev sr msg' = do
    consErr $ Error ErrTypeChecker sev (srcRangeOf sr sr) msg'

    e <- getErrsListRev <&> filter (\(Error _ s _ _) -> s == SevError)
    when (length e > 100) throwTcException

  -- This is for continuing type checking another definition after errors are encountered
  -- This is never used to mask errors or speculatively type check code
  tryTcKeepErrors :: m a -> m (Maybe a)
