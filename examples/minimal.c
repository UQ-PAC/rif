#include <stdatomic.h>
#include <stdlib.h>

int y = 0;
int *x;

int foo(int argc) {
  int a = *x;
  atomic_store_explicit(&y, 100, memory_order_relaxed);
  atomic_store_explicit(x, argc, memory_order_relaxed);
  return a;
}

int main(int argc, char **argv) {
  int *x = malloc(sizeof(int));
  return foo(argc);
}
