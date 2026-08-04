-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Front.Macros (expandMacros) where

import Control.Exception (Exception, throwIO)
import Control.Monad (forM_)
import Data.HashMap.Strict qualified as HM
import Data.List (intersperse)
import Data.Maybe (mapMaybe)
import Error
import Front.Ast qualified as A
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

expandMacros :: A.Ast -> IO (Either Error A.Ast)
expandMacros ast = do
  let tDefs = flip mapMaybe (HM.elems ast.tDefs) $ \x -> case x.tDef of
        A.TypeDecl dc ds | notNull ds -> Just (x, dc, ds)
        _ -> Nothing

  newModules <- newVar []

  forM_ tDefs $ \(tDef, dataConss, ds) -> forM_ ds $ \deriveName -> do
    case fst deriveName of
      "Eq" -> do
        i <- generateEqMod tDef dataConss (snd deriveName)
        modVar newModules (i :)
      "Show" -> do
        i <- generateShowMod tDef dataConss (snd deriveName)
        modVar newModules (i :)
      _ ->
        throw (snd deriveName) $ "No such builtin derivable type class: " <> fst deriveName

  newModules' <- getVar newModules

  pure $ Right $ ast {A.tDefs = HM.union ast.tDefs $ HM.fromList $ newModules' <&> \i -> (fst i.name, i)}

generateEqMod :: A.TDef -> List1 A.DataCons -> SrcRange -> IO A.TDef
generateEqMod tDef dataConss sr = do
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

  let neqExpr =
        let x = (A.EVar (VName "x") [], sr)
            y = (A.EVar (VName "y") [], sr)
            eqOp = (A.EMemberCall x (Right (OpName "=="), sr) [y], sr)
            notEq = (A.EMemberCall eqOp (Right (OpName "!"), sr) [], sr)
        in (A.EClosure [cloParam "x", cloParam "y"] notEq, sr)
  let neqVDef = A.VDef (VName "neq", sr) (Just (OpName "!=", sr)) [] [] Nothing (Just neqExpr) 1

  let vDefsOrdered = [eqVDef, neqVDef]
  let nameMap = HM.fromList [(VName "eq", eqVDef), (VName "neq", neqVDef)]
  let opMap = HM.fromList [(OpName "==", List1 eqVDef []), (OpName "!=", List1 neqVDef [])]
  let vDefs = A.BlockInner {vDefsOrdered, nameMap, opMap}

  let eqTrait = (A.TNamed (TName "Eq", sr) [], sr)

  let mod = A.Module forType vDefs [eqTrait] def
  let modName = TName $ un name <> "Eq"
  pure $ A.TDef {name = (modName, sr), genParams = tDef.genParams, isEffect = False, tDef = mod}

generateShowMod :: A.TDef -> List1 A.DataCons -> SrcRange -> IO A.TDef
generateShowMod tDef dataConss sr = do
  let name = fst tDef.name
  let genArgs = tDef.genParams <&> \(_, (n, _)) -> (A.TNamed (n, sr) [], sr)
  let forType = (A.TNamed (name, sr) genArgs, sr)

  let lit :: Text -> A.Expr
      lit s = (A.ELitString s, sr)

  -- ++
  let mkAppend :: [A.Expr] -> A.Expr
      mkAppend [] = lit ""
      mkAppend [x] = x
      mkAppend (x : xs) = (A.EMemberCall x (Right (OpName "++"), sr) [mkAppend xs], sr)

  -- x.show()
  let showField :: VName -> A.Expr
      showField n = (A.EMemberCall (A.EVar n [], sr) (Left (VName "show"), sr) [], sr)

  let wrapParens :: Text -> Text -> [A.Expr] -> A.Expr
      wrapParens _ _ [] = lit "" -- Empty data constructor
      wrapParens l r xs = mkAppend (lit l : xs <> [lit r])

  let mkBranch :: A.DataCons -> A.MatchBranch
      mkBranch (A.DataCons dcName fields) = do
        let dcName' = un $ fst dcName
        case fields of
          A.TupleFields fs -> do
            let patVars = [0 .. length fs - 1] <&> \i -> VName ("x" <> tShow i)
            let pats = patVars <&> \n -> (A.PName n, sr)
            let ptn = (A.PDataCons dcName pats, sr)
            let args = intersperse (lit ", ") $ patVars <&> showField
            A.MatchBranch ptn Nothing $ mkAppend [lit dcName', wrapParens "(" ")" args]
          A.RecordFields fs -> do
            let fieldNames = toList fs <&> (fst >>> fst)
            let patVars = [0 .. length fieldNames - 1] <&> \i -> VName ("x" <> tShow i)
            let pats = patVars <&> \n -> (A.PName n, sr)
            let pairs = zip fieldNames pats <&> \(n, p) -> ((n, sr), p)
            let ptn = (A.PRecord dcName pairs, sr)
            let args' = zipWith (\n v -> mkAppend [lit (un n <> " = "), showField v]) fieldNames patVars
            let args = intersperse (lit ", ") args'
            A.MatchBranch ptn Nothing $ mkAppend $ lit (dcName' <> "{") : args <> [lit "}"]

  let matchExpr = (A.EVar (VName "x") [], sr)
  let matchBranches = dataConss <&> mkBranch
  let showExpr = (A.EMatch matchExpr matchBranches, sr)

  let cloParam n = ((A.DName (VName n) False, sr), Nothing)
  let showCloExpr = (A.EClosure [cloParam "x"] showExpr, sr)
  let showVDef = A.VDef (VName "show", sr) Nothing [] [] Nothing (Just showCloExpr) 0

  let vDefsOrdered = [showVDef]
  let nameMap = HM.fromList [(VName "show", showVDef)]
  let vDefs = A.BlockInner {vDefsOrdered, nameMap, opMap = def}

  let showTrait = (A.TNamed (TName "Show", sr) [], sr)
  let mod = A.Module forType vDefs [showTrait] def
  let modName = TName $ un name <> "Show"
  pure $ A.TDef {name = (modName, sr), genParams = tDef.genParams, isEffect = False, tDef = mod}
