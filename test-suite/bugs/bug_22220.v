(* Schemes over template polymorphic inductives should not mention the
   global template universes in their types, so that using them does not
   constrain the template universes.
   See https://github.com/rocq-prover/rocq/issues/22220
   (Reduced version for 9.1: no bad-template-constraint warning and no
   [Scheme Rewriting] command on this branch; this only checks that
   on-demand rewriting scheme generation still works.) *)
Set Warnings "-missing-scheme".
Inductive myeq (A:Type) (x:A) : A -> Prop := myeq_refl : myeq A x x.

Goal forall (A:Type) (x y : A) (P : A -> Prop), myeq A x y -> P y -> P x.
Proof. intros * H HP. rewrite H. exact HP. Qed.

Goal forall (A:Type) (x y : A) (P : A -> Prop), myeq A x y -> P x -> P y.
Proof. intros * H HP. rewrite H in HP. exact HP. Qed.

(* dependent rewrite, exercising the rew_dep schemes *)
Goal forall (A:Type) (x y : A) (P : forall a : A, myeq A x a -> Prop)
            (H : myeq A x y), P y H -> P x (myeq_refl A x).
Proof. intros * HP. rewrite <- H in HP. exact HP. Qed.
