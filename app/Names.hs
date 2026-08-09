-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Names where

import Data.Char (isAsciiUpper)
import Data.Text qualified as T
import MhPrelude
import SrcLoc (SrcRange)

type TextL = (Text, SrcRange)

-- E.g. #stlib
-- Note that the # symbol is included in the string. Same for Namespaces and T/VFqn.
newtype PkgName = PkgName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

-- E.g. "#app/main", "#stlib/json/parser", etc.
newtype Namespace = Namespace Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

nsToPkg :: Namespace -> PkgName
nsToPkg = un >>> T.split (== '/') >>> (!! 0) >>> PkgName

data ImportNames = NoNames | AllNames | VisibleNames [NameL] | HiddenNames [NameL]
  deriving (Show, Generic, Eq)

-- a, _f9, etc.
newtype VName = VName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type VNameL = (VName, SrcRange)

-- +, -, etc.
newtype OpName = OpName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type OpNameL = (OpName, SrcRange)

-- X, Y_9, etc.
newtype TName = TName Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type TNameL = (TName, SrcRange)

nameToVNameOrTName :: Name -> Either VName TName
nameToVNameOrTName (Name n) | isAsciiUpper $ T.head n = Right $ TName n
nameToVNameOrTName (Name n) = Left $ VName n

-- TName or VName
newtype Name = Name Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type NameL = (Name, SrcRange)

class IsAName n where
  forgetNameType :: n -> Name

instance IsAName VName where
  forgetNameType = un >>> Name

instance IsAName TName where
  forgetNameType = un >>> Name

instance IsAName Name where
  forgetNameType = identity

-- #stlib/a:a, etc.
newtype VFqn = VFqn Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

fqnToPkg :: Text -> PkgName
fqnToPkg x = PkgName $ T.takeWhile (/= '/') x

vFqnToPkg :: VFqn -> PkgName
vFqnToPkg x = PkgName $ T.takeWhile (/= '/') $ un x

vFqnToNamespace :: VFqn -> Namespace
vFqnToNamespace (VFqn x) = Namespace $ T.takeWhile (/= ':') x

vFqnToName :: VFqn -> VName
vFqnToName = un >>> T.takeWhileEnd (/= ':') >>> T.takeWhileEnd (/= '.') >>> VName

-- #abc/xyz/abc:A.B, etc.
newtype TFqn = TFqn Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

tFqnToPkg :: TFqn -> PkgName
tFqnToPkg x = PkgName $ T.takeWhile (/= '/') $ un x

tFqnToNamespace :: TFqn -> Namespace
tFqnToNamespace (TFqn x) = Namespace $ T.takeWhile (/= ':') x

tFqnToName :: TFqn -> TName
tFqnToName = un >>> T.takeWhileEnd (/= ':') >>> T.takeWhileEnd (/= '.') >>> TName

-- VFqn or TFqn
newtype Fqn = Fqn Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

newtype Attribute = Attribute Text
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

shortenFqn :: Text -> Text
shortenFqn t = case T.findIndex (== '$') t of
  Just i -> T.drop (i + 1) t
  _ -> T.drop (must (T.findIndex (== ':') t) + 1) t
