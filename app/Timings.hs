-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# OPTIONS_GHC -Wno-orphans #-}

module Timings (Timings (..), writeTimingsFile) where

import Control.Monad (forM_)
import Data.List (sortBy)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Time.Clock (NominalDiffTime)
import MhPrelude
import System.IO (IOMode (WriteMode), withFile)

-- Times in seconds
data Timings = Timings
  { lexing :: NominalDiffTime,
    lexingPost :: NominalDiffTime,
    parsing :: NominalDiffTime,
    macroExpansion :: NominalDiffTime,
    typeChecking :: NominalDiffTime,
    lowering :: NominalDiffTime,
    optimising :: NominalDiffTime,
    transpiling :: NominalDiffTime,
    compiling :: NominalDiffTime,
    execute :: NominalDiffTime
  }
  deriving (Show, Generic, Default)

getTotal :: Timings -> NominalDiffTime
getTotal tt = tt.lexing + tt.lexingPost + tt.parsing + tt.macroExpansion + tt.typeChecking + tt.lowering + tt.optimising + tt.transpiling + tt.compiling + tt.execute

instance Semigroup Timings where
  x <> y =
    Timings
      { lexing = x.lexing + y.lexing,
        lexingPost = x.lexingPost + y.lexingPost,
        parsing = x.parsing + y.parsing,
        macroExpansion = x.macroExpansion + y.macroExpansion,
        typeChecking = x.typeChecking + y.typeChecking,
        lowering = x.lowering + y.lowering,
        optimising = x.optimising + y.optimising,
        transpiling = x.transpiling + y.transpiling,
        compiling = x.compiling + y.compiling,
        execute = x.execute + y.execute
      }

instance Monoid Timings where
  mempty = Timings def def def def def def def def def def

data TimingsPct = TimingsPct
  { lexingPct :: Float,
    lexingPostPct :: Float,
    parsingPct :: Float,
    macroExpansionPct :: Float,
    typeCheckingPct :: Float,
    loweringPct :: Float,
    optimisingPct :: Float,
    transpilingPct :: Float,
    compilingPct :: Float,
    executePct :: Float
  }
  deriving (Show, Generic, Default)

timingsPctToText :: Timings -> TimingsPct -> Text
timingsPctToText y x =
  T.unlines
    $ concat
      [ ["Lexing: " <> tShow (toMs y.lexing) <> " ms (" <> tShow x.lexingPct <> "%)" | y.lexing > 0.0],
        ["Lexing post processing: " <> tShow (toMs y.lexingPost) <> " ms (" <> tShow x.lexingPostPct <> "%)" | y.lexingPost > 0.0],
        ["Parsing: " <> tShow (toMs y.parsing) <> " ms (" <> tShow x.parsingPct <> "%)" | y.parsing > 0.0],
        ["MacroExpansion: " <> tShow (toMs y.macroExpansion) <> " ms (" <> tShow x.macroExpansionPct <> "%)" | y.macroExpansion > 0.0],
        ["Type Checking: " <> tShow (toMs y.typeChecking) <> " ms (" <> tShow x.typeCheckingPct <> "%)" | y.typeChecking > 0.0],
        ["Lowering: " <> tShow (toMs y.lowering) <> " ms (" <> tShow x.loweringPct <> "%)" | y.lowering > 0.0],
        ["Optimising: " <> tShow (toMs y.optimising) <> " ms (" <> tShow x.optimisingPct <> "%)" | y.optimising > 0.0],
        ["Transpiling: " <> tShow (toMs y.transpiling) <> " ms (" <> tShow x.transpilingPct <> "%)" | y.transpiling > 0.0],
        ["Code Generation: " <> tShow (toMs y.compiling) <> " ms (" <> tShow x.compilingPct <> "%)" | y.compiling > 0.0],
        ["Execution: " <> tShow (toMs y.execute) <> " ms (" <> tShow x.executePct <> "%)" | y.execute > 0.0]
      ]

-- Rounds to 1dp
toPct :: (RealFrac a) => a -> Float
toPct x = let y :: Int = round (x * 1000); z :: Float = fromIntegral y in z / 10

-- Rounds to 1dp
toMs :: (RealFrac a) => a -> Float
toMs x = let y :: Int = round (x * 10000); z :: Float = fromIntegral y in z / 10

timingsToPct :: Timings -> TimingsPct
timingsToPct tt =
  let total = getTotal tt
   in if total == 0
        then def
        else
          TimingsPct
            { lexingPct = toPct $ tt.lexing / total,
              lexingPostPct = toPct $ tt.lexingPost / total,
              parsingPct = toPct $ tt.parsing / total,
              macroExpansionPct = toPct $ tt.macroExpansion / total,
              typeCheckingPct = toPct $ tt.typeChecking / total,
              loweringPct = toPct $ tt.lowering / total,
              optimisingPct = toPct $ tt.optimising / total,
              transpilingPct = toPct $ tt.transpiling / total,
              compilingPct = toPct $ tt.compiling / total,
              executePct = toPct $ tt.execute / total
            }

instance Default NominalDiffTime where
  def = 0

writeTimingsFile :: FilePath -> [(Text, Timings)] -> IO ()
writeTimingsFile path timings = withFile path WriteMode
  $ \h -> do
    let overallTimings' = foldl' (<>) def $ snd <$> timings
    let overallTimings = timingsToPct overallTimings'
    let totalTime = sum $ timings <&> (snd >>> getTotal >>> realToFrac)

    TIO.hPutStrLn h $ "Total: " <> tShow (toMs totalTime) <> "ms"
    TIO.hPutStrLn h "--------"
    TIO.hPutStrLn h $ timingsPctToText overallTimings' overallTimings
    TIO.hPutStrLn h ""

    let timingsWithPct = timings <&> (\(n, t) -> (n, t, toMs $ getTotal t, toPct $ getTotal t / totalTime))
    let timingsWithPctSorted = sortBy (\(_, _, _, p1) (_, _, _, p2) -> compare p2 p1) timingsWithPct

    forM_ timingsWithPctSorted $ \(name, t, tot, pct) -> do
      TIO.hPutStrLn h $ (if T.null name then "(app)" else name) <> ": " <> tShow tot <> "ms (" <> tShow pct <> "%)"
      TIO.hPutStrLn h "--------"
      TIO.hPutStrLn h $ timingsPctToText t $ timingsToPct t
