#ifndef GLUE_H
#define GLUE_H
#include <gc_stack.h>
#include <stdio.h>
extern unsigned long long get_unboxed_ordinal(value);
extern unsigned long long get_boxed_ordinal(value);
extern value *get_args(value);
extern value make_Coq_Init_Datatypes_list_nil(void);
extern value make_Coq_Init_Datatypes_list_cons(value, value, value *);
extern value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, value, value);
extern value make_CertiCoq_bool_false(void);
extern value make_CertiCoq_bool_true(void);
extern value make_Coq_Init_Datatypes_nat_O(void);
extern value make_Coq_Init_Datatypes_nat_S(value, value *);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
extern value make_Coq_Init_Datatypes_option_Some(value, value *);
extern value alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, value);
extern value make_Coq_Init_Datatypes_option_None(void);
extern value make_Coq_Init_Datatypes_prod_pair(value, value, value *);
extern value alloc_make_Coq_Init_Datatypes_prod_pair(struct thread_info *, value, value);
extern unsigned long long get_Coq_Init_Datatypes_list_tag(value);
extern unsigned long long get_CertiCoq_bool_tag(value);
extern unsigned long long get_Coq_Init_Datatypes_nat_tag(value);
extern unsigned long long get_Coq_Init_Datatypes_option_tag(value);
extern unsigned long long get_Coq_Init_Datatypes_prod_tag(value);
extern void print_Coq_Init_Datatypes_list(value, void (*)(value));
extern void print_CertiCoq_bool(value);
extern void print_Coq_Init_Datatypes_nat(value);
extern void print_Coq_Init_Datatypes_option(value, void (*)(value));
extern void print_Coq_Init_Datatypes_prod(value, void (*)(value), void (*)(value));
extern value call(struct thread_info *, value, value);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_list[2][5];

extern signed char const names_of_CertiCoq_bool[2][6];

extern signed char const names_of_Coq_Init_Datatypes_nat[2][2];

extern signed char const names_of_Coq_Init_Datatypes_option[2][5];

extern signed char const names_of_Coq_Init_Datatypes_prod[1][5];


#endif /* GLUE_H */
