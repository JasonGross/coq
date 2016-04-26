CoInductive CoFalse := .

CoFixpoint loop : CoFalse :=
  (cofix f := loop with g := loop for f).

Definition bad : forall x, x := match loop with end.
