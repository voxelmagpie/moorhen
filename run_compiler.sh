# Run from project (git repo) root
# Takes path to moorhen file/package
# Add -xc (RTS arg) for extra backtrace information
# Add --debug-ast and/or --debug-hir for IR debugging output
cabal run --disable-optimization --enable-debug-info --enable-profiling --ghc-options="-fprof-auto-calls" moorhen -- "$@" --builtins-path ./builtins.mh --stlib-path ./stlib --out-dir ./out --timings +RTS -N -RTS
