set -e
sh debug_build.sh
# Add -xc (RTS arg) for extra backtrace information
# Add --debug-ast and/or --debug-hir for IR debugging output
time -f "Building compiler took %es" cabal build --disable-optimization --enable-debug-info --enable-profiling --ghc-options="-fprof-auto-calls" moorhen
timeout -s KILL 10s time -f "Compiling tests took %es" cabal run --disable-optimization --enable-debug-info --enable-profiling --ghc-options="-fprof-auto-calls" moorhen -- tests --builtins-path ./builtins.mh --stlib-path ./stlib +RTS -N -RTS 
cd out; timeout -s KILL 5s time -f "Took %es" node --enable-source-maps tests.mjs; cd ..
