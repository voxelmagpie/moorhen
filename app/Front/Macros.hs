-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Macros (expandMacros) where

import Control.Exception (Exception, throwIO)
import Control.Monad (forM_)
import Data.HashMap.Strict qualified as HM
import Data.Maybe (mapMaybe)
import Error
import Front.Ast qualified as A
import Front.LexPost (convertTokenStream1Line)
import Front.Lexer (lexMoorhen)
import Front.Parser
import GHC.Stack (HasCallStack)
import MhPrelude
import Names
import SrcLoc
import Vars

newtype MacrosException = MacrosException Error
  deriving (Show, Eq, Generic)
  deriving anyclass (Exception, Newtype)

throw :: (HasCallStack, HasSrcRange r) => r -> Text -> IO a
throw sr msg = throwIO $ MacrosException $ Error ErrMacroExpansion SevError (srcRangeOf sr sr) $ msg

expandMacros :: A.Ast -> FilePath -> IO (Either Error A.Ast)
expandMacros ast srcPath = do
  let tDefs = flip mapMaybe (HM.elems ast.tDefs) $ \x -> case x.tDef of
        A.TypeDecl dc ds | notNull ds -> Just (x, dc, ds)
        _ -> Nothing

  newModules <- newVar []

  forM_ tDefs $ \(tDef, dataConss, ds) -> forM_ ds $ \deriveName -> do
    case fst deriveName of
      "Eq" -> do
        i <- generateEqMod tDef dataConss (snd deriveName) srcPath
        modVar newModules (i :)
      _ ->
        throw (snd deriveName) $ "No such builtin derivable type class: " <> fst deriveName

  newModules' <- getVar newModules

  pure $ Right $ ast {A.tDefs = HM.union ast.tDefs $ HM.fromList $ newModules' <&> \i -> (fst i.name, i)}

generateEqMod :: A.TDef -> List1 A.DataCons -> SrcRange -> FilePath -> IO A.TDef
generateEqMod tDef dataConss sr srcPath = do
  let name = fst tDef.name
  let genArgs = tDef.genParams <&> \(_, (n, _)) -> (A.TNamed (n, sr) [], sr)
  let forType = (A.TNamed (name, sr) genArgs, sr)

  let mkComparisons :: [(A.Expr, A.Expr)] -> A.Expr
      mkComparisons [] = (A.ELitBool True, sr)
      mkComparisons [(x, y)] = (A.EMemberCall x (Right $ OpName "==", sr) [y], sr)
      mkComparisons ((x, y) : rest) = (A.EAnd (A.EMemberCall x (Right $ OpName "==", sr) [y], sr) (mkComparisons rest), sr)

  let isEnum = flip all dataConss $ \case A.DataCons _ (A.TupleFields []) -> True; _ -> False

  let eqExpr =
        if isEnum
          then do
            let intType = (A.TNamed (TName "I32", sr) [], sr)
            let getter n = (A.EAs (A.EVar (VName n) [], sr) intType, sr)
            mkComparisons [(getter "x", getter "y")]
          else case dataConss of
            -- 1 data constructor (product type)
            List1 (A.DataCons _ fields) [] -> do
              case fields of
                A.TupleFields fs -> do
                  let idxs = [0 :: Int .. length fs - 1]
                  let mkGetter i n = (A.EIndex (A.EVar (VName n) [], sr) (fromIntegral i), sr)
                  let gettersX = idxs <&> \i -> mkGetter i "x"
                  let gettersY = idxs <&> \i -> mkGetter i "y"
                  mkComparisons (zip gettersX gettersY)
                A.RecordFields fs -> do
                  let names = toList fs <&> (fst >>> fst)
                  let gettersX = names <&> \n -> (A.EFieldAccess (A.EVar (VName "x") [], sr) (n, sr), sr)
                  let gettersY = names <&> \n -> (A.EFieldAccess (A.EVar (VName "y") [], sr) (n, sr), sr)
                  mkComparisons (zip gettersX gettersY)
            -- Sum type, requires pattern match
            _ -> do
              let matchExpr = (A.ETuple $ List2 (A.EVar (VName "x") [], sr) (A.EVar (VName "y") [], sr) [], sr)
              let mkBranch (A.DataCons dcName fields) = do
                    let numFields = case fields of A.TupleFields fs -> length fs; A.RecordFields fs -> length fs
                    let mkFieldPattern prefix i = VName (prefix <> tShow i)
                    let xNames = [0 .. numFields - 1] <&> \i -> mkFieldPattern "x" i
                    let yNames = [0 .. numFields - 1] <&> \i -> mkFieldPattern "y" i
                    let xPats = xNames <&> \n -> (A.PName n, sr)
                    let yPats = yNames <&> \n -> (A.PName n, sr)
                    let ptn = case fields of
                          A.TupleFields _ -> do
                            (A.PTuple $ List2 (A.PDataCons dcName xPats, sr) (A.PDataCons dcName yPats, sr) [], sr)
                          A.RecordFields fs -> do
                            let fieldNames = toList fs <&> (fst >>> fst)
                            let mkPRecordPairs pats = zip fieldNames pats <&> \(n, p) -> ((n, sr), p)
                            let xs =
                                  List2
                                    (A.PRecord dcName (mkPRecordPairs xPats), sr)
                                    (A.PRecord dcName (mkPRecordPairs yPats), sr)
                                    []
                            (A.PTuple xs, sr)

                    let e = mkComparisons $ zip (xNames <&> \n -> (A.EVar n [], sr)) (yNames <&> \n -> (A.EVar n [], sr))
                    A.MatchBranch ptn Nothing e
              let finalBranch = A.MatchBranch (A.PIgnore, sr) Nothing (A.ELitBool False, sr)
              let matchBranches = must $ listToList1 $ (toList dataConss <&> mkBranch) <> [finalBranch]
              (A.EMatch matchExpr matchBranches, sr)

  let cloParam n = ((A.DName (VName n) False, sr), Nothing)
  let eqCloExpr = (A.EClosure [cloParam "x", cloParam "y"] eqExpr, sr)

  let eqVDef = A.VDef (VName "eq", sr) (Just (OpName "==", sr)) [] [] Nothing (Just eqCloExpr) 0

  neqExpr <- parseExpr "\\x, y -> !(x == y)" srcPath
  let neqVDef = A.VDef (VName "neq", sr) (Just (OpName "!=", sr)) [] [] Nothing (Just neqExpr) 1

  let vDefsOrdered = [eqVDef, neqVDef]
  let nameMap = HM.fromList [(VName "eq", eqVDef), (VName "neq", neqVDef)]
  let opMap = HM.fromList [(OpName "==", List1 eqVDef []), (OpName "!=", List1 neqVDef [])]
  let vDefs = A.BlockInner {vDefsOrdered, nameMap, opMap}

  let eqTrait = (A.TNamed (TName "Eq", sr) [], sr)

  let mod = A.Module forType vDefs [eqTrait] def
  let modName = TName $ un name <> "Eq"
  pure $ A.TDef {name = (modName, sr), genParams = tDef.genParams, isEffect = False, tDef = mod}

-- Source string must be valid or this will crash
parseExpr :: Text -> FilePath -> IO A.Expr
parseExpr src srcPath = do
  case lexMoorhen srcPath src of
    Left _ -> undefined
    Right x -> do
      tokens <- convertTokenStream1Line x <&> must
      parseMoorhenExpr srcPath tokens <&> must
