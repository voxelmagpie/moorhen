# Run this from the parent dir
set -e
time -f "Compiling chess engine demo took %es" cabal run --disable-optimization --enable-debug-info --enable-profiling --ghc-options="-fprof-auto-calls" moorhen -- build chess/chess.mh --builtins-path ./builtins.mh --stlib-path ./stlib --out-dir ./out --timings +RTS -N

