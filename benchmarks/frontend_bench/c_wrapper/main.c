#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"

extern value body(struct thread_info *);
unsigned long long get_Coq_Init_Datatypes_nat_tag(value);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
extern value call(struct thread_info *tinfo, value clos, value arg0);
extern value *get_args(value);

value int_to_nat(struct thread_info *tinfo, unsigned int num) {
  value n = make_Coq_Init_Datatypes_nat_O();
  for(unsigned int i = 0; i < num; i++) {
    n = alloc_make_Coq_Init_Datatypes_nat_S(tinfo, n);
  }
  return n;
}

int get_nat(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_nat_tag($v);
  switch ($tag) {
    case 0:
      return 0;
    case 1:
      $args = get_args($v);
      return get_nat(*((value *) $args + 0)) + 1;
  }
}

int main(int argc, char *argv[]) {
  value clo;
  value val;
  struct thread_info* tinfo;


  tinfo = make_tinfo();
  clo = body(tinfo);
  int in = strtol(argv[1], NULL, 10);
  value n = int_to_nat(tinfo, in);
  val = call(tinfo, clo, n);
  printf("%d\n", get_nat(val));

  return 0;
}
