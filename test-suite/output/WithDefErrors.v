(* Test improved error messages for "with Definition" constraints *)

(* Test 1: Type mismatch - expected nat but got bool *)
Module Type T1.
  Parameter x : nat.
End T1.
Definition y1 : bool := true.
Fail Module Type T1' := T1 with Definition x := y1.

(* Test 2: Body mismatch - definitions with different values *)
Module Type T2.
  Definition x := 0.
End T2.
Definition y2 : nat := 1.
Fail Module Type T2' := T2 with Definition x := y2.

(* Test 3: Polymorphic constraint mismatch *)
Module Type T3.
  Polymorphic Parameter p : Type.
End T3.
Fail Module Type T3' := T3 with Definition p := nat.

(* Test 4: Universe constraint issues *)
Module Type T4.
  Parameter x : Set.
End T4.
Definition y4 := Type.
Fail Module Type T4' := T4 with Definition x := y4.

(* NOTE: WithCannotConstrainPrimitive and WithCannotConstrainSymbol errors
   cannot be triggered from user code because module types export primitives
   and symbols as parameters. These errors exist for internal consistency. *)
