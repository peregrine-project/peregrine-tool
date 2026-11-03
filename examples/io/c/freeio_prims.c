/* The two IO primitives of FreeIO.v for the CertiRocq C backend. */
#include <stdio.h>
#include "gc_stack.h"
#include "prim_int63.h"

value freeio_put_int(value n, value w)
{
  printf("%lld\n", (long long) Long_val(n));
  return w;
}

value freeio_get_int(struct thread_info *ti, value w)
{
  long long x = 0;
  if (scanf("%lld", &x) != 1) x = 0;
  return mk_pair(ti, Val_long(x), w);
}
