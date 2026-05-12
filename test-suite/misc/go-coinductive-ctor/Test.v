(* Regression test: a single-constructor [CoInductive] used to emit a
   thunk-wrapping [type T struct{ Force func() T_body }] together with
   a [type T_body struct{...}], while constructor sites and pattern
   matches used the constructor's name (e.g. [Coq_go]) as both struct
   literal and type-switch tag. The result was an undefined-symbol
   error in Go: the declared type [T_body] never matched the used
   name [Coq_go].

   This mirrors [coq-itree]'s [itree] datatype: a single-constructor
   CoInductive whose constructor [go] is the Go-keyword case. The
   constructor [go] sanitises to the Go identifier [Coq_go], which is
   the name the rest of the extracted code already refers to.

   The fix aligns the CoInductive path with the record/variant path:
   one interface for the type, one struct named after the constructor. *)
From Corelib Require Extraction.

Variant itreeF (itree : Type) :=
| RetF (r : nat)
| TauF (t : itree)
.
Arguments RetF [_].
Arguments TauF [_].

CoInductive itree : Type := go
{ _observe : itreeF itree }.

(* Pattern-match site: [Coq_go] appears in a type switch. Previously this
   referred to an undeclared identifier. *)
Definition observe (t : itree) : itreeF itree := t.(_observe).

(* Constructor application: [Coq_go{Field0: ...}] as a struct literal.
   Same undefined-symbol failure mode without the fix. *)
Definition build_ret (n : nat) : itree := go (RetF n).

Extraction Language Go.
Set Extraction Go Module "coindtest/extracted".
Set Extraction Output Directory "out".

Separate Extraction observe build_ret.
