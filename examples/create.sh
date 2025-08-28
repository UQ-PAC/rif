aarch64-linux-gnu-gcc -O2 -march=armv8-a+nopauth $1 -o $1.out
ddisasm $1.out
gtirb-semantics $1.out.gtirb $1.out.gts --json $1.out.json
