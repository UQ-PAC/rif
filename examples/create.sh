aarch64-linux-gnu-gcc -O2 -march=armv8-a+nopauth $1.c -o $1.out
ddisasm $1.out
gtirb-semantics $1.gtirb $1.gts --json $1.json
