#!/usr/bin/env bash
# Usage: gen-params.sh N > FILE.ast
# An untyped lambda-box program with N inductive types I0 .. I(N-1), each with
# one parameter and one constructor of one field, and a constant `main` that
# applies the constructor of each to a box.  The HM inference of
# --untyped-dearg allocates one type variable per parameter, so the list of
# global variables that `compact` (theories/erasure/EHindleyMilner.v)
# deduplicates after `main` has at least N elements.
n=${1:?usage: gen-params.sh N}
mp='(MPfile ("Perf"))'
ind() { printf '(inductive (%s "I%d") 0)' "$mp" "$1"; }
body='(tConstruct (inductive ((MPfile ("Perf")) "Unit") 0) 0 ())'
for ((k = 0; k < n; k++)); do
  body="(tApp (tLambda nAnon $body) (tApp (tApp (tConstruct $(ind $k) 0 ()) tBox) tBox))"
done
printf '(Untyped ('
printf '((%s "main") (ConstantDecl (constant_body (Some %s))))' "$mp" "$body"
for ((k = n - 1; k >= 0; k--)); do
  printf ' ((%s "I%d") (InductiveDecl (mutual_inductive_body Finite 1 ((one_inductive_body "I%d" false IntoAny ((constructor_body "I%d.mk" 1)) ())))))' "$mp" $k $k $k
done
printf ' ((%s "Unit") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body "Unit" false IntoAny ((constructor_body "Unit.tt" 0)) ())))))' "$mp"
printf ') (Some (tConst (%s "main"))))\n' "$mp"
