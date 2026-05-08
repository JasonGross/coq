(* Regression test for Bug 2: Go extraction emitted two same-named
   top-level declarations when an inductive's Go name collided with one
   of its constructors' Go names — the canonical case being
   [Coq.Strings.Ascii.ascii := Ascii (...)] where both type and
   constructor capitalise to "Ascii" inside the [ascii] package.

   We replicate the structure precisely: an inductive [ascii] living in
   its own top-level file/module (so [Separate Extraction] places it in
   the [ascii] Go package by itself), with a sole constructor [Ascii].
   Without the fix, Go rejects the file with "Ascii redeclared in this
   block". *)
From Corelib Require Extraction.

(* The canonical colliding case: type [ascii] and its constructor [Ascii]
   both render as the Go identifier "Ascii". Inside its own Go package
   they both end up as top-level "Ascii", which is illegal Go. *)
Inductive ascii := Ascii (b0 b1 b2 b3 b4 b5 b6 b7 : bool).

(* Use site for the constructor so the rename is exercised at
   applications too, not just in the declaration. *)
Definition zero_ascii : ascii :=
  Ascii false false false false false false false false.

(* Control: a non-colliding inductive (two constructors so it isn't
   optimised away as a singleton wrapper). The rename must NOT fire
   here — [MkFoo] should stay [MkFoo], not become [MkMkFoo]. *)
Inductive foo := MkFoo (n : nat) | OtherFoo.

Definition zero_foo : foo := MkFoo 0.
