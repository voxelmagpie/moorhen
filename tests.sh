set -e
sh debug_build.sh
timeout -s KILL 10s time -f "Compiling tests took %es" sh run_compiler.sh tests
cd out; timeout -s KILL 5s time -f "Running tests took %es" node tests.mjs; cd ..
