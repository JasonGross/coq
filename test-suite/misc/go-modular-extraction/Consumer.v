(* Consumer module: uses types and functions from Base *)
From Top Require Import Base.

Definition mydouble (n : mynat) : mynat := myadd n n.

Definition test_even : bool := myeven (MyS (MyS MyO)).

Inductive mylist (A : Type) := mynil | mycons (x : A) (xs : mylist A).
Arguments mynil {A}.
Arguments mycons {A} x xs.

Fixpoint mylength {A : Type} (l : mylist A) : mynat :=
  match l with mynil => MyO | mycons _ t => MyS (mylength t) end.
