-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Vars where

import Control.Monad (Monad)
import Control.Monad.ST (ST)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef, writeSTRef)
import Prelude (IO)

class (Monad m) => MonadVars m where
  type Var m :: Type -> Type
  newVar :: a -> m (Var m a)
  setVar :: Var m a -> a -> m ()
  getVar :: Var m a -> m a
  modVar :: Var m a -> (a -> a) -> m ()

instance MonadVars (ST s) where
  type Var (ST s) = STRef s
  newVar = newSTRef
  setVar = writeSTRef
  getVar = readSTRef
  modVar = modifySTRef'

instance MonadVars IO where
  type Var IO = IORef
  newVar = newIORef
  setVar = writeIORef
  getVar = readIORef
  modVar = modifyIORef'
