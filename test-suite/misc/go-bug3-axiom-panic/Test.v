(* Regression test for Bug 3: an unrealised Parameter (axiom of non-Type
   sort) used to be extracted as `func Foo() any { return panic(...) }`,
   which Go rejects because panic is a no-value expression. The fix emits
   a bare `panic(...)` statement at the top-level body. *)
From Corelib Require Extraction.

Parameter encode_unimpl : nat -> bool.

Definition use_it (n : nat) : bool := encode_unimpl n.

Extraction Language Go.
Set Extraction Go Module "bug3test/extracted".
Set Extraction Output Directory "out".

Separate Extraction use_it.
