(* -*- coq-prog-args: ("-emacs" "-nois") -*- *)
Inductive False := .
Axiom bad : False.
Definition bad2 : forall x, x := match bad with end.
