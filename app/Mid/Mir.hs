-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Mid.Mir where

import Data.HashTable.IO qualified as HT
import Data.Int (Int32)
import MhPrelude
import Names
import SrcLoc (SrcRange)
import TypeString

data Mir = Mir
  { name :: PkgName,
    vDefs :: HashTable VFqn VDef
  }

newtype Mir' = Mir'
  { vDefs :: [(VFqn, VDef)]
  }
  deriving (Show)

-- Types

data Effects = Effects {noThrow :: Bool, pure :: Bool}
  deriving (Show, Generic, Eq, Hashable, Default)

instance Semigroup Effects where
  x <> y = Effects {noThrow = x.noThrow && y.noThrow, pure = x.pure && y.pure}

instance Monoid Effects where
  mempty = Effects {noThrow = True, pure = True}

type IsAsync = Bool

data Type
  = TFunc [Type] Type Effects IsAsync
  | TProduct (List2 Type)
  | TSum (List2 Type) -- Does not include enums (sum types with no data) which use TI32
  | TInt
  | TI32
  | TReal
  | TUnit
  | TString
  | TVec Type
  | TBool
  | TLazy Type
  | TAny -- For generics, and untyped javascript values
  -- Where the type would appear within itself it is replaced with TAny.
  -- E.g. data X (Vec[(X, Int)]) -> TRecursive $ TVec $ TProduct(TAny, TInt)
  -- The inner type is always TProduct, TSum, TVec, or TAny
  | TRecursive Type
  deriving (Show, Generic, Eq, Hashable)

type TypeL = (Type, SrcRange)

-- Globals & functions

data Const = CInt Integer | CI32 Int32 | CFloat Text | CBool Bool | CString Text | CVec [Const] | CFn VFqn
  deriving (Show, Eq, Generic, Hashable)

data Fn = Fn
  { params :: [(LocalVarUid, Maybe VName, Type, SrcRange)],
    ret :: Type,
    expr :: Expr,
    effects :: Effects,
    fqn :: VFqn,
    isAsync :: IsAsync
  }
  deriving (Show, Generic, Eq, Hashable)

type Weight = Int

data VDef = VDef
  { name :: TextL,
    fqn :: VFqn,
    type' :: Type,
    exprMaybe :: Maybe Expr,
    value :: Maybe Const,
    nextLocalUid :: Int
  }
  deriving (Show, Generic, Eq)

-- Expressions

-- !! If adding new expressions with a LocalVarUid then update renameExpr in Optimiser.hs !!

data Expr'
  = ELoadConst Const
  | EVec [Expr]
  | EVar LocalVarUid
  | EGlobal VFqn
  | EClosure Fn
  | EFnCall Expr [Expr] IsAsync Type
  | EDoBlock [Stmt] (Maybe Expr)
  | EIf Expr Expr Expr Type
  | EProduct (List2 Expr)
  | ESum (List2 Type) Int Expr
  | EUnreachable Text -- panics, type is unit
  | EAnd Expr Expr
  | EOr Expr Expr
  | ETry
      { tryExpr :: Expr,
        catch :: List1 (TypeString, LocalVarUid, SrcRange, Expr),
        finally :: Maybe Expr
      }
  | EThrow Expr TypeString
  | EIndex Expr Int (Maybe VName) -- Tuple/record or Vec (unchecked)
  | ESumTypeActiveIndex Expr -- As I32, not for enums
  | ESumTypeGet Expr
  | EBreak LocalVarUid -- UID is label
  | EContinue LocalVarUid -- UID is label
  | EImplicitCast Expr
  | ESignExtendInt Expr
  | EIntToF64 Expr
  | ECastNumber Expr Type
  deriving (Show, Generic, Eq, Hashable)

type ExprWeight = Int

type Expr = (Expr', SrcRange)

-- Name is unique within the top-level definition
-- Ids are *not* reset for each closure expression
newtype LocalVarUid = LocalVarUid Int
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type IsMutable = Bool

data Stmt'
  = SLet LocalVarUid (Maybe TextL) IsMutable Expr
  | SRecLet LocalVarUid (Maybe TextL) Expr
  | SLetUninit LocalVarUid Type
  | SExpr Expr
  | SAssign LocalVarUid (Maybe TextL) Expr
  | SLoop Expr LocalVarUid
  deriving (Show, Generic, Eq, Hashable)

type Stmt = (Stmt', SrcRange)

showMir :: Mir -> IO Text
showMir ir = do
  ir' <- Mir' <$> HT.toList ir.vDefs
  pure $ tShow ir'
