-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module SrcLoc where

import MhPrelude

data SrcLoc = SrcLoc
  { line :: Int, -- 1-based
    index :: Int -- 0-based index into file (bytes)
  }
  deriving (Show, Eq, Generic, Hashable, Default)

instance Ord SrcLoc where
  compare x y = compare x.index y.index

data SrcLoc'
  = SrcLoc'
      FilePath
      SrcLoc
  deriving (Show, Eq, Generic, Hashable, Default)

data SrcRange
  = SrcRange
      FilePath
      SrcLoc
      SrcLoc
  deriving (Eq, Generic, Hashable, Default)

srcRangeToSrcLoc' :: SrcRange -> SrcLoc'
srcRangeToSrcLoc' (SrcRange fp l _) = SrcLoc' fp l

-- Improper show instance for printing ASTs (does not produce a haskell code string)
instance Show SrcRange where
  show (SrcRange _ s0 s1) | s0.line == s1.line = "line " <> show s0.line
  show (SrcRange _ s0 s1) = "line " <> show s0.line <> "-" <> show s1.line

toSrcRange :: FilePath -> SrcLoc -> SrcRange
toSrcRange f l = SrcRange f l l

getLineNum :: (HasSrcRange a) => a -> Int
getLineNum = startLoc >>> (.line)

srcRangeFirstChar :: SrcRange -> SrcRange
srcRangeFirstChar (SrcRange f l _) = SrcRange f l l

srcRangeLastChar :: SrcRange -> SrcRange
srcRangeLastChar (SrcRange f _ l) = SrcRange f l l

class HasSrcRange a where
  startLoc :: a -> SrcLoc
  endLoc :: a -> SrcLoc
  filePath :: a -> FilePath

instance HasSrcRange SrcLoc' where
  startLoc (SrcLoc' _ x) = x
  endLoc (SrcLoc' _ x) = x
  filePath (SrcLoc' f _) = f

instance HasSrcRange SrcRange where
  startLoc (SrcRange _ x _) = x
  endLoc (SrcRange _ _ x) = x
  filePath (SrcRange f _ _) = f

instance (HasSrcRange a) => HasSrcRange [a] where
  startLoc xs | null xs = def
  startLoc xs = startLoc $ must $ head xs
  endLoc xs | null xs = def
  endLoc xs = endLoc $ must $ last xs
  filePath xs | null xs = def
  filePath xs = filePath $ must $ head xs

instance (HasSrcRange a) => HasSrcRange (List1 a) where
  startLoc (List1 x _) = startLoc x
  endLoc (List1 x []) = endLoc x
  endLoc (List1 _ ys) = endLoc ys
  filePath (List1 x _) = filePath x

instance (HasSrcRange a) => HasSrcRange (List2 a) where
  startLoc (List2 x _ _) = startLoc x
  endLoc (List2 _ x []) = endLoc x
  endLoc (List2 _ _ zs) = endLoc zs
  filePath (List2 x _ _) = filePath x

instance (HasSrcRange b) => HasSrcRange (a, b) where
  startLoc (_, x) = startLoc x
  endLoc (_, x) = endLoc x
  filePath (_, x) = filePath x

instance (HasSrcRange a) => HasSrcRange (Maybe a) where
  startLoc (Just x) = startLoc x
  startLoc _ = def
  endLoc (Just x) = endLoc x
  endLoc _ = def
  filePath (Just x) = filePath x
  filePath _ = def

srcRangeOf :: (HasSrcRange a, HasSrcRange b) => a -> b -> SrcRange
srcRangeOf x y =
  let x' = startLoc x
      y' = startLoc y
   in SrcRange (filePath x) (if x' == def then y' else x') (if y' == def then x' else y')
