From Corelib Require Extraction.
Extraction Language Go.

(* Test 1: Simple inductive with constructors *)
Inductive color := Red | Green | Blue.
Recursive Extraction color.

(* Test 2: Function with pattern matching *)
Definition mynegb (b : bool) := match b with true => false | false => true end.
Extraction mynegb.

(* Test 3: Recursive function *)
Fixpoint myadd (n m : nat) : nat :=
  match n with O => m | S p => S (myadd p m) end.
Extraction myadd.

(* Test 4: Record type *)
Record mypoint := mk_mypoint { mypx : nat; mypy : nat }.
Recursive Extraction mypoint.

(* Test 5: Higher-order function *)
Definition apply_fn (f : nat -> nat) (x : nat) := f x.
Extraction apply_fn.

(* Test 6: Option type and matching *)
Inductive myopt (A : Type) := myNone | mySome (x : A).
Arguments myNone {A}.
Arguments mySome {A} x.
Definition from_opt (A : Type) (d : A) (o : myopt A) :=
  match o with myNone => d | mySome x => x end.
Recursive Extraction from_opt.

(* Test 7: Let-in expression *)
Definition test_let (n : nat) := let x := S n in S x.
Extraction test_let.

(* Test 8: Mutual recursion *)
Fixpoint myeven (n : nat) : bool :=
  match n with O => true | S p => myodd p end
with myodd (n : nat) : bool :=
  match n with O => false | S p => myeven p end.
Recursive Extraction myeven.

(* Test 9: Polymorphic identity *)
Definition myid (A : Type) (x : A) := x.
Extraction myid.

(* Test 10: Composition *)
Definition compose (A B C : Type) (g : B -> C) (f : A -> B) (x : A) := g (f x).
Extraction compose.
