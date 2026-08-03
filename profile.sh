set +e
cabal run --enable-optimization=2 --enable-profiling moorhen -- tests --builtins-path ./builtins.mh --stlib-path ./stlib +RTS -N -sstderr -pj -hy -l

# Drag and drop the .prof file into https://www.speedscope.app/

# eventlog2html moorhen.eventlog # cabal install eventlog2html

