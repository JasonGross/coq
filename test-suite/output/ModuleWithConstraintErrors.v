(* Tests for improved error messages on module with constraints *)
(* These examples are based on the issue report *)

(* Test 1: Type mismatch in with constraint - Parameter case *)
Module Type A.
  Parameter x : nat.
End A.

Definition y : bool := true.

Fail Module B <: A with Definition x := y.

(* Test 2: Body mismatch in with constraint - Definition case *)
Module Type A2.
  Definition x : nat := 0.
End A2.

Definition y2 : nat := 1.

Fail Module B2 <: A2 with Definition x := y2.

(* Test 3: Universe inconsistency in with constraint *)
Module Type A3.
  Parameter x : Set.
End A3.

Definition y3 := Set.

Fail Module B3 <: A3 with Definition x := y3.
