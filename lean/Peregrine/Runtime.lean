/-
  Peregrine.Runtime — minimal support library for code emitted by
  the Lean backend of peregrine.

  λ_□ is untyped; the printer maps every value to a single universal
  type `Obj`.  Source-language constructors retain their original
  names (with a trailing `_`) and become Lean inductives whose fields
  are all of type `Obj`.  Recovering the original type at a match
  site uses `cast`, an unsafe reinterpretation that is sound because
  the upstream λ_□ program is well-typed.
-/

namespace Peregrine

/-- Universal "object" type for extracted values.  All emitted Lean
    inductives are wrappers around this type. -/
unsafe inductive Obj : Type
  | mk : (Unit → Obj) → Obj

/-- Reinterpret an `Obj` at any concrete type.  Sound when the `Obj`
    actually was produced by a value of type `α` upstream — guaranteed
    by the source λ_□ program being well-typed. -/
@[inline] unsafe def cast {α : Type} (o : Obj) : α := unsafeCast o

@[inline] unsafe def reflect {α : Type} (a : α) : Obj := unsafeCast a

/-- Universal application: reinterpret `f` as `Obj → Obj` and apply.
    Used to apply [Obj]-typed function values whose source-language
    arity has been erased. -/
@[inline] unsafe def apply (f x : Obj) : Obj := (unsafeCast f : Obj → Obj) x

end Peregrine

