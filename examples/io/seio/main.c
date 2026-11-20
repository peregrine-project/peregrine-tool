#include "gc_stack.h"
extern value body(struct thread_info *);
int main(void) { body(make_tinfo()); return 0; }
