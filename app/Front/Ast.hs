-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Ast where

import Data.Int (Int64)
import Front.TypeKind
import MhPrelude
import Names
import SrcLoc (SrcRange)

data Ast = Ast
  { imports :: [Import],
    vDefs :: HashMap VName VDef,
    tDefs :: HashMap TName TDef
  }
  deriving (Show, Generic, Eq, Default)

data Import = Import
  { path :: Text,
    sr :: SrcRange,
    qual :: Maybe TNameL,
    names :: ImportNames
  }
  deriving (Show, Generic, Eq)

-- Top-level definitions

data AnyDef = AVDef VDef | ATDef TDef
  deriving (Show, Generic, Eq)

type WhereClauses = [(TypeExpr, TypeExpr)]

data VDef = VDef
  { name :: VNameL,
    op :: Maybe OpNameL,
    genParams :: [(TypeKind, TNameL)],
    whereClauses :: WhereClauses,
    typeExpr :: Maybe TypeExpr, -- Nothing for impls of trait fns
    expr :: Maybe Expr, -- Nothing for trait functions and builtins
    idx :: Int
  }
  deriving (Show, Generic, Eq)

data BlockInner = BlockInner
  { vDefsOrdered :: [VDef],
    nameMap :: HashMap VName VDef,
    opMap :: HashMap OpName (List1 VDef)
  }
  deriving (Show, Generic, Eq)

data TDef = TDef
  { name :: TNameL,
    genParams :: [(TypeKind, TNameL)],
    isEffect :: Bool, -- Presence of '@' before name, always False for aliases
    tDef :: TDef'
  }
  deriving (Show, Generic, Eq)

data TDef'
  = TypeAliasDecl TypeExpr -- type T = ...
  | TypeDecl (List1 DataCons) [(Text, SrcRange)] -- data T = A | B C deriving ...
  | BuiltinTypeDecl -- builtin Vec [T]
  | Module TypeExpr BlockInner [TypeExpr] WhereClauses
  | Trait BlockInner [TypeExpr] WhereClauses
  deriving (Show, Generic, Eq)

data ADataCons = ADataCons {typeName :: TName, name :: TName}
  deriving (Show, Generic, Eq)

data DataCons = DataCons TNameL Fields
  deriving (Show, Generic, Eq)

data Fields = TupleFields [TypeExpr] | RecordFields (List1 (VNameL, TypeExpr))
  deriving (Show, Generic, Eq)

data TypeExpr'
  = TFunc {params :: [TypeExpr], ret :: TypeExpr, effects :: [TypeExpr]}
  | TUnit
  | TTuple (List2 TypeExpr)
  | TNamed (Maybe TNameL) TNameL [TypeExpr]
  | TEffect [TypeExpr]
  | TLifetime VName
  deriving (Show, Generic, Eq)

type TypeExpr = (TypeExpr', SrcRange)

-- Expressions
data Expr'
  = ELitInt Int64
  | ELitFloat Text
  | ELitBool Bool
  | ELitString Text
  | ELitList [Expr]
  | EVar (Maybe TNameL) VName [TypeExpr]
  | EClosure [(Destructure, Maybe TypeExpr)] Expr
  | EFnCall Expr [Expr]
  | EDoBlock [Stmt] (Maybe Expr)
  | EIf Expr Expr Expr
  | ETuple (List2 Expr)
  | EAnd Expr Expr
  | EOr Expr Expr
  | EMatch Expr (List1 MatchBranch)
  | EDataCons (Maybe TNameL) TNameL [TypeExpr]
  | EMemberCall Expr (Either VName OpName, SrcRange) [Expr]
  | ETry
      { expr :: Expr,
        catch :: List1 CatchBlock,
        finally :: Maybe Expr
      }
  | EThrow Expr
  | EIndex Expr Int
  | EFieldAccess Expr VNameL
  | ERecordInit TypeExpr (List1 (VNameL, Maybe Expr))
  | EBreak
  | EContinue
  | EUpdate Expr [(List1 AccessorChainPart, Expr)]
  | EExplicitType Expr TypeExpr
  | EAs Expr TypeExpr
  deriving (Show, Generic, Eq)

type Expr = (Expr', SrcRange)

type CatchBlock = (Maybe (TypeExpr, Destructure), SrcRange, Expr)

data AccessorChainPart'
  = AccessorChainName VName
  | AccessorChainIndex Int
  deriving (Show, Generic, Eq)

type AccessorChainPart = (AccessorChainPart', SrcRange)

data Pattern'
  = PIgnore
  | PName VName
  | PTuple (List2 Pattern)
  | PDataCons TNameL [Pattern]
  | PRecord TNameL [(VNameL, Pattern)]
  deriving (Show, Generic, Eq)

type Pattern = (Pattern', SrcRange)

data MatchBranch = MatchBranch {pattern :: Pattern, guard :: Maybe Expr, expr :: Expr}
  deriving (Show, Generic, Eq)

type IsMutable = Bool

data Stmt'
  = SLet Destructure (Maybe TypeExpr) Expr
  | SRecLet VNameL TypeExpr Expr
  | SExpr Expr'
  | SWhen Expr Expr
  | SAssign VNameL Expr
  | SForEach
      { destr :: Destructure,
        inExpr :: Expr,
        bodyExpr :: Expr
      }
  | SLoop Expr
  deriving (Show, Generic, Eq)

type Stmt = (Stmt', SrcRange)

data Destructure'
  = DIgnore
  | DName VName IsMutable
  | DTupleLike (List1 Destructure)
  | DRecord [(VNameL, Destructure)]
  | DAs VNameL IsMutable Destructure
  deriving (Show, Generic, Eq)

type Destructure = (Destructure', SrcRange)
