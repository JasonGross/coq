Inductive sTrue : SProp := stt.
Set Primitive Projections.
Record foo := { bar : sTrue }.
Goal forall x y : foo, x = y.
destruct x, y; reflexivity.
Defined.
