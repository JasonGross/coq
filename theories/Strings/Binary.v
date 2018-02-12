(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ascii String.
Require Import BinNums.
Import BinNatDef.
Import BinIntDef.
Import BinPosDef.

Local Open Scope positive_scope.
Local Open Scope string_scope.

Fixpoint bin_string_of_pos' (p : positive) (rest : string) : string
  := match p with
     | 1 => String "1" rest
     | p'~0 => bin_string_of_pos' p' (String "0" rest)
     | p'~1 => bin_string_of_pos' p' (String "1" rest)
     end.
Definition bin_string_of_pos (p : positive) : string
  := String "0" (String "b" (bin_string_of_pos' p "")).
Definition bin_string_of_N (n : N) : string
  := match n with
     | N0 => "0b0"
     | Npos p => bin_string_of_pos p
     end.
Definition bin_string_of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (bin_string_of_pos p)
     | Z0 => "0b0"
     | Zpos p => bin_string_of_pos p
     end.

Fixpoint N_of_bin_string' (s : string) (rest : N)
  : N
  := match s with
     | "" => rest
     | String ch s'
       => N_of_bin_string'
            s'
            (if ascii_beq ch "0"
             then match rest with
                  | N0 => N0
                  | Npos p => Npos (xO p)
                  end
             else if ascii_beq ch "1"
                  then match rest with
                       | Npos p => Npos (xI p)
                       | N0 => Npos xH
                       end
                  else N0)
     end.
Definition N_of_bin_string (s : string) : N
  := match s with
     | String s0 (String sb s)
       => if ascii_beq s0 "0"
          then if ascii_beq sb "b"
               then N_of_bin_string' s N0
               else N0
          else N0
     | _ => N0
     end.
Definition pos_of_bin_string (s : string) : positive
  := match N_of_bin_string s with
     | N0 => 1
     | Npos p => p
     end.
Definition Z_of_bin_string (s : string) : Z
  := let '(is_neg, n) := match s with
                         | String s0 s'
                           => if ascii_beq s0 "-"
                              then (true, N_of_bin_string s')
                              else (false, N_of_bin_string s)
                         | EmptyString => (false, N_of_bin_string s)
                         end in
     match n with
     | N0 => Z0
     | Npos p => if is_neg then Zneg p else Zpos p
     end.

Lemma N_of_bin_string_of_pos' (p : positive) (rest : string) (base : N)
  : N_of_bin_string' (bin_string_of_pos' p rest) base
    = N_of_bin_string' rest match base with
                            | N0 => N.pos p
                            | Npos v => Npos (Pos.app v p)
                            end.
Proof.
  revert base rest; induction p, base; intros; try reflexivity;
    cbn; rewrite IHp; reflexivity.
Qed.

Lemma N_of_bin_string_of_N (n : N)
  : N_of_bin_string (bin_string_of_N n)
    = n.
Proof.
  destruct n; [ reflexivity | apply N_of_bin_string_of_pos' ].
Qed.

Lemma Z_of_bin_string_of_Z (z : Z)
  : Z_of_bin_string (bin_string_of_Z z)
    = z.
Proof.
  cbv [bin_string_of_Z Z_of_bin_string]; destruct z as [|z|z]; cbn;
    try reflexivity;
    rewrite N_of_bin_string_of_pos'; cbn; reflexivity.
Qed.

Lemma pos_of_bin_string_of_pos (p : positive)
  : pos_of_bin_string (bin_string_of_pos p)
    = p.
Proof.
  cbv [bin_string_of_pos pos_of_bin_string N_of_bin_string]; cbn;
    rewrite N_of_bin_string_of_pos'; cbn; reflexivity.
Qed.

Example bin_string_of_pos_1 : bin_string_of_pos 1 = "0b1" := eq_refl.
Example bin_string_of_pos_2 : bin_string_of_pos 2 = "0b10" := eq_refl.
Example bin_string_of_pos_3 : bin_string_of_pos 3 = "0b11" := eq_refl.
Example oct_string_of_N_0 : bin_string_of_N 0 = "0b0" := eq_refl.
Example bin_string_of_Z_0 : bin_string_of_Z 0 = "0b0" := eq_refl.
Example bin_string_of_Z_m1 : bin_string_of_Z (-1) = "-0b1" := eq_refl.
