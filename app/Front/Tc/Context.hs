-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Tc.Context where

import Front.Ast qualified as A
import Front.Hir qualified as H
import Front.Tc.Inputs
import MhPrelude
import Names

data CtxModOrTrait = CtxModOrTrait
  { name :: TName,
    selfType :: H.Type,
    associatedTypes :: HashMap TName (TFqn, H.Type)
  }

data Ctx = Ctx
  { namespace :: Namespace,
    thisAst :: A.Ast,
    thisAstImports :: ImportsList,
    tcIn :: Inputs,
    --
    -- Fields below this are only set when type checking within a definition
    -- E.g. Record fields, expressions
    --
    modOrTrait :: Maybe CtxModOrTrait,
    fqn :: Maybe (Either VFqn TFqn),
    tNameToGp :: HashMap TName H.GenParam,
    genParams :: [H.GenParam],
    blockWhereClauses :: H.WhereClauses,
    vDefWhereClauses :: H.WhereClauses,
    thisDefType :: Maybe H.Type,
    --
    -- Fields below are only set when type checking an expression
    --
    variables :: [Variable],
    closureDepth :: Int,
    inLoop :: Maybe H.LocalVarUid
  }

data Variable = Variable
  { isMutable :: Bool,
    name :: VNameL,
    uid :: H.LocalVarUid,
    typ :: H.Type,
    closureDepth :: Int
  }
  deriving (Show)

findLocalVarByName :: Ctx -> VName -> Maybe Variable
findLocalVarByName ctx name =
  find ((.name) >>> fst >>> (== name)) ctx.variables

mkFileCtx :: Namespace -> (A.Ast, ImportsList) -> Inputs -> Ctx
mkFileCtx namespace (thisAst, thisAstImports) tcIn =
  Ctx
    { namespace = namespace,
      thisAst = thisAst,
      thisAstImports = thisAstImports,
      tcIn = tcIn,
      modOrTrait = def,
      fqn = def,
      tNameToGp = def,
      genParams = def,
      blockWhereClauses = def,
      vDefWhereClauses = def,
      thisDefType = def,
      variables = def,
      closureDepth = 0,
      inLoop = Nothing
    }

mkFileCtx' :: Ctx -> Ctx
mkFileCtx' c = mkFileCtx c.namespace (c.thisAst, c.thisAstImports) c.tcIn
