Require Import Div2.
Require Import Even.

Ltac Gencli h h1 h2 :=
  (generalize h ; clear h1 ; intro h2).

Lemma EVEN_PLUS_EVEN :
  forall (m n:nat),
    (even m)->(even n)->(even (plus m n)).
Proof.
intros m n evm evn.
try Gencli (even_2n evm) evm evm. (* previously Anomaly: Illegal application: (APP even_2n evm). Please report. *)
Abort.
