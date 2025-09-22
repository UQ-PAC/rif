#include <stdatomic.h>
#include <stdio.h>

int shared = 0;
int lock;

int zero = 0;
int one = 1;

#define LOCK(l) do { if (__atomic_compare_exchange((l), &zero, &one, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) break; } while (1)
#define UNLOCK(l) do { __atomic_store((l), &zero, __ATOMIC_SEQ_CST); } while (0)

void stuff(int* a) {
  *a -= 1;
}

int reader(void) {
  int local;

  LOCK(&lock);
  local = shared;
  UNLOCK(&lock);

  return local;
}

void writer(void) {
  LOCK(&lock);
  shared = 0xFF;
  stuff(&shared);
  shared = 0;
  UNLOCK(&lock);
}

int main(void) {
  return reader();
}
