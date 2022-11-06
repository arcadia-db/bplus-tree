set -e

cd ../../../
cargo build --release

cd ./src/misc/bindings/
gcc -Wall -Wextra -Wpedantic -o main main.h main.c ../../../target/release/libtest1.so

./main
