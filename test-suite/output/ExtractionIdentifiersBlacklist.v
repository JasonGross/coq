Require Import Coq.extraction.Extraction.

Extraction Language OCaml.

Module Import A.
  Parameter int : Type.
  Parameter int_zero : int.
  Parameter int_succ : int -> int.
  Parameter int_opp : int -> int.
  Parameter int_twice : int -> int.

  Extraction Identifier Blacklist int.
  Extract Inlined Constant int => int.
  Extract Inlined Constant int_zero => "0".
  Extraction Identifier Blacklist succ.
  Extract Inlined Constant int_succ => "succ".
  Extract Inlined Constant int_opp => "-".
  Extract Inlined Constant int_twice => "2 *".
End A.
Extraction Identifier Blacklist A.
Extraction Blacklist A.
Inductive int := Zero | Succ (_ : int).
Definition zero := Zero.
Definition succ := Succ.

Definition test := (int_zero, int_succ, int_opp, int_twice, zero, succ).
Recursive Extraction test.
