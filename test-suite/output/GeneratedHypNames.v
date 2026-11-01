(* Warning "generated-hyp-name": a later tactic uses a hypothesis name that
   an earlier tactic sentence generated. *)
Set Warnings "generated-hyp-name".

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons (h : A) (n : nat) (t : vec A n) : vec A (S n).

Fixpoint vlen {A n} (v : vec A n) : nat :=
  match v with
  | vnil _ => 0
  | vcons _ _ _ t => S (vlen t)
  end.

(* intros, induction with generated names *)
Lemma plus_0 : forall n : nat, n + 0 = n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* the same proof with explicit names: no warning *)
Lemma plus_0' : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* generated names that no later sentence uses: no warning *)
Lemma plus_0'' : forall n : nat, n + 0 = n.
Proof.
  intros. induction n; simpl; auto.
Qed.

(* destruct of a vector reuses the name of the hypothesis *)
Lemma vlen_ok : forall A n (v : vec A n), vlen v = n.
Proof.
  intros A n v. destruct v.
  - reflexivity.
  - simpl. induction v.
    + reflexivity.
    + simpl. rewrite IHv. reflexivity.
Qed.

(* a goal selector is kept in the replacement *)
Lemma pair_eq : forall (p : nat * bool), p = p /\ True.
Proof.
  intros p. split. 2: exact I. 1: destruct p. destruct n; destruct b; reflexivity.
Qed.

(* inversion: the untouched hypotheses n and m are not reported *)
Lemma S_inj : forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H. inversion H. clear H1. reflexivity.
Qed.

(* no replacement text for other tactics: only the names and the range *)
Lemma remember_len : forall (l : list nat), l = l.
Proof.
  intros l. remember (length l). destruct n; reflexivity.
Qed.

(* a user-given name takes over a generated one: no warning for [clear H] *)
Lemma user_takes_over : forall n : nat, n = n -> n = n -> True.
Proof.
  intros n. intro. clear H. intro H. clear H. exact I.
Qed.
