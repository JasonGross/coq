Require Import Arith.
Definition pred_subset : forall (n:nat), ~n=(0)->nat.
refine (fun (x:nat) => (match x with
              O => fun (h:~(0)=(0)) => _
           | (S p) => fun (h:~(S p)=(0)) => p
           end : ~x=(0)->nat)). (* used to be Anomaly: type_of: this is not a well-typed term. Please report. *)
Abort.
