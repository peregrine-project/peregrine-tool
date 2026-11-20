#include <stdio.h>
#include "gc_stack.h"
extern value body(struct thread_info *);
int main(void) {
  struct thread_info *tinfo = make_tinfo();
  value v = body(tinfo);
  printf("result %lld\n", (long long) Long_val(v));
  return 0;
}
