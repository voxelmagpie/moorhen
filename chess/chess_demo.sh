# !! Run this from the parent directory (repository root) !!
set -e
timeout -s KILL 10s time -f "Compiling chess engine demo took %es" sh run_compiler.sh build chess/chess.mh

