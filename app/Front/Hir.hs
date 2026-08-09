-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Hir where

import Data.Int (Int64)
import Front.TypeKind
import MhPrelude
import Names
import SrcLoc (SrcRange)

data Hir = Hir
  { name :: PkgName,
    exports :: HashTable Namespace (HashTable VName VFqn, HashTable TName TNameExport, [Module]),
    vDefs :: HashTable VFqn VDef,
    vDefExpr :: HashTable VFqn VDefExpr,
    tDefs1 :: HashTable TFqn TDef,
    dataTypeDefs :: HashTable TFqn DataTypeDef
  }

data VDefExpr = VDefExpr {expr :: Expr, nextLocalUid :: Int}
  deriving (Show)

data Hir' = Hir'
  { exports :: [(Namespace, ([(VName, VFqn)], [(TName, TNameExport)]))],
    vDefs :: [(VFqn, VDef)],
    vDefExpr :: [(VFqn, VDefExpr)],
    tDefs1 :: [(TFqn, TDef)],
    dataTypeDefs :: [(TFqn, DataTypeDef)]
  }
  deriving (Show)

-- Types

data Type
  = TFunc {params :: [Type], ret :: Type, eff :: Type} -- TODO Store eff as HashSet Type?
  | TTuple (List2 Type)
  | TNamed TFqn [Type]
  | TEffect (HashSet Type) -- All HashSet types are TNamed
  | TLifetime Int
  deriving (Show, Generic, Eq, Hashable)

type TypeL = (Type, SrcRange)

-- Top-level definitions

type TraitRef = (TFqn, [Type])

-- No duplicates
newtype WhereClauses = WhereClauses [(Type, List1 TraitRef)]
  deriving (Show, Generic, Eq)
  deriving anyclass (Newtype, Default)

instance ToList WhereClauses where
  type ToListItemType WhereClauses = (Type, List1 TraitRef)
  toList = un

-- No duplicates
newtype TraitsList = TraitsList (HashMap TFqn [Type])
  deriving (Show, Generic, Eq)
  deriving anyclass (Newtype, Default)

instance ToList TraitsList where
  type ToListItemType TraitsList = TraitRef
  toList = un >>> toList

data VDef = VDef
  { name :: VNameL,
    op :: Maybe OpNameL,
    fqn :: VFqn,
    genParams :: [GenParam],
    moduleWhereClauses :: WhereClauses,
    whereClauses :: WhereClauses,
    type' :: Type
  }
  deriving (Show, Generic, Eq)

data GenParam = GenParam
  { fqn :: TFqn,
    sr :: SrcRange,
    type' :: Type,
    kind :: TypeKind
  }
  deriving (Show, Generic, Eq)

data Module = Module
  { genParams :: [GenParam],
    name :: TName,
    fqn :: TFqn,
    forType :: Type,
    vDefNames :: [VName],
    ops :: HashMap OpName (List1 VName),
    traits :: TraitsList,
    whereClauses :: WhereClauses
  }
  deriving (Show, Generic, Eq)

data Trait = Trait
  { genParams :: [GenParam],
    name :: TName,
    fqn :: TFqn,
    selfType :: GenParam,
    vDefs :: [TraitVDef],
    names :: HashMap VName TraitVDef,
    ops :: HashMap OpName (List1 VName),
    traits :: TraitsList,
    whereClauses :: WhereClauses,
    recursiveNames :: HashSet VName -- All Definition names, including names from dependency traits
  }
  deriving (Show, Generic, Eq)

data TraitVDef = TraitVDef
  { genParams :: [GenParam], -- Dose not include trait gen params
    idx :: Int,
    vDef :: VDef
  }
  deriving (Show, Generic, Eq)

data TNameExportType = IsTypeDef | IsModule Module | IsTrait Trait
  deriving (Show, Generic, Eq)

data TNameExport = TNameExport {fqn :: TFqn, typ :: TNameExportType}
  deriving (Show, Generic, Eq)

-- Data types (including builtins), aliases, generic parameters
data TDef = TDef
  { name :: TNameL,
    fqn :: TFqn,
    genParams :: [GenParam],
    selfType :: Type,
    isAlias :: Bool,
    typeKind :: TypeKind,
    isGenericParameter :: Bool, -- or 'for'/Self type
    isBuiltin :: Bool
  }
  deriving (Show, Generic, Eq)

-- data X, data X = Y (Int) | Z, etc.
-- Not builtins (Int/Real/etc.), generic parameters, or type aliases
data DataTypeDef = DataTypeDef
  { t1 :: TDef,
    dataCons :: List1 DataCons,
    isEnumType :: Bool
  }
  deriving (Show, Generic, Eq)

data DataCons = DataCons TNameL Fields
  deriving (Show, Generic, Eq)

data Fields = TupleFields [Type] | RecordFields (List1 (VName, Type))
  deriving (Show, Generic, Eq)

-- Expressions

type IsGenericOverEffectType = Bool

-- E.g.:
-- mod X [A] for A where A : Eq -- <- FromBlockWheres
--    fn f [B] () where B : Eq -- <- FromVDefWheres
data FromWhereClauseSource = FromBlockWheres | FromVDefWheres
  deriving (Show, Generic, Eq)

-- The trait used for a where clause can come from another where clause or a concrete module
-- If it comes from a where clause then the first Int is the index into the current function's where clauses and
-- the second Int is the index into that where clause's list of traits
data ChosenTrait = FromWhereClause FromWhereClauseSource Int Int | FromModule TFqn [Type] WhereClauseTraitsList
  deriving (Show, Generic, Eq)

-- For each where clause: for each trait in the where clause: chosen module
type WhereClauseTraitsList = [List1 (TraitRef, ChosenTrait)]

data WhereClauseTraits = WhereClauseTraits
  { mod :: WhereClauseTraitsList,
    vDef :: WhereClauseTraitsList
  }
  deriving (Show, Generic, Eq, Default)

data Expr'
  = ELitInt Int64
  | ELitInt32 Int
  | ELitFloat Text
  | ELitBool Bool
  | ELitString Text
  | ELitList [Expr]
  | EVar LocalVarUid
  | EGlobal VFqn [Type] IsGenericOverEffectType WhereClauseTraits
  | EWheresGet
      { -- The indices are for finding the vdef in the where clause parameters
        src :: FromWhereClauseSource,
        whereClauseIdx :: Int,
        whereClauseTraitIdx :: Int,
        fnIdx :: Int,
        nextWhereClauses :: WhereClauseTraitsList -- For generic trait functions
      }
  | EClosure [Destructure] Expr
  | EFnCall Expr [Expr]
  | EDoBlock [Stmt] (Maybe Expr)
  | EIf Expr Expr Expr
  | ETuple (List2 Expr)
  | EAnd Expr Expr
  | EOr Expr Expr
  | EMatch Expr (List1 MatchBranch)
  | EDataCons DataConsInfo
  | ETry
      { expr :: Expr,
        catch :: List1 (Destructure, Expr),
        finally :: Maybe Expr
      }
  | EThrow Expr
  | EIndex Expr Int
  | EFieldAccess Expr VNameL
  | ERecordInit DataConsInfo (List1 Expr) (List1 (VName, Int)) -- TODO Do we need the names here?
  | ENewtypeAccess Expr
  | EBreak LocalVarUid -- UID is label
  | EContinue LocalVarUid -- UID is label
  | EUpdate Expr [Expr] EUpdatePart
  | EImplicitCast Expr -- A change of type that doesn't generate code, e.g. changing effect types on a fn ptr
  | ESignExtendInt Expr -- Takes any integer type other than Int
  | EIntToF64 Expr
  | ECastNumber Expr -- Casts between Int, I32, Real, and sum types -> Int/I32
  deriving (Show, Generic, Eq)

data EUpdatePart
  = EUpdateValue Int
  | EUpdateNoChange
  | EUpdateTuple (List1 EUpdatePart) -- Tuples and tuple-like product data constructors
  | EUpdateRecord DataConsInfo (List1 (VName, EUpdatePart))
  deriving (Show, Generic, Eq)

data DataConsInfo = DataConsInfo
  { fqn :: TFqn,
    dcName :: TName,
    dcIdx :: Int,
    isFn :: Bool, -- Data constructor is tuple-like and holds data, e.g. Some
    isProduct :: Bool, -- E.g. data X I32 I32
    isEnum :: Bool -- E.g. data X = A | B
  }
  deriving (Show, Generic, Eq)

data Pattern'
  = PIgnore
  | PName VName LocalVarUid
  | PTuple (List2 Pattern)
  | PDataCons DataConsInfo [Pattern]
  | PRecord DataConsInfo [(VName, Pattern)]
  deriving (Show, Generic, Eq)

type Pattern = (Pattern', Type, SrcRange)

data MatchBranch = MatchBranch {pattern :: Pattern, guard :: Maybe Expr, expr :: Expr}
  deriving (Show, Generic, Eq)

type Expr = (Expr', Type, SrcRange)

-- Name is unique within the top-level definition
newtype LocalVarUid = LocalVarUid Int
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
  deriving anyclass (Newtype)

type IsMutable = Bool

data Stmt'
  = SLet Destructure Expr
  | SRecLet VNameL LocalVarUid Expr -- Must be a EClosure
  | SExpr Expr
  | SWhen Expr Expr
  | SAssign LocalVarUid VNameL Expr
  | SForEach
      { destr :: Destructure,
        inExpr :: Expr, -- Iter[varType]
        bodyExpr :: Expr,
        label :: LocalVarUid
      }
  | SLoop Expr LocalVarUid
  deriving (Show, Generic, Eq)

type Stmt = (Stmt', SrcRange)

data Destructure'
  = DIgnore
  | DName VName LocalVarUid IsMutable
  | DTuple (List2 Destructure)
  | DDataCons DataConsInfo (List1 Destructure)
  | DRecord DataConsInfo [(VName, Destructure)]
  | DAs VNameL LocalVarUid IsMutable Destructure
  deriving (Show, Generic, Eq)

type Destructure = (Destructure', Type, SrcRange)
