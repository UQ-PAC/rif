#include <stdatomic.h>

struct spin_lock_t {
  int lock;
};

void spin_lock(struct spin_lock_t *s) {
  int zero = 0;
  int one = 1;

  while (1) {
    if (__atomic_compare_exchange(&s->lock, &zero, &one, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
      return;
  }
}

void spin_unlock(struct spin_lock_t *s) {
  int zero = 0;
  __atomic_store(&s->lock, &zero, __ATOMIC_SEQ_CST);
}

void main(void) {
  struct spin_lock_t s;
  spin_lock(&s);
  spin_unlock(&s);
}
