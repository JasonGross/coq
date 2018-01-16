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

Fixpoint oct_string_of_pos' (p : positive) (rest : string) : string
  := match p with
     | 1 => String "1" rest
     | 2 => String "2" rest
     | 3 => String "3" rest
     | 4 => String "4" rest
     | 5 => String "5" rest
     | 6 => String "6" rest
     | 7 => String "7" rest
     | p'~0~0~0 => oct_string_of_pos' p' (String "0" rest)
     | p'~0~0~1 => oct_string_of_pos' p' (String "1" rest)
     | p'~0~1~0 => oct_string_of_pos' p' (String "2" rest)
     | p'~0~1~1 => oct_string_of_pos' p' (String "3" rest)
     | p'~1~0~0 => oct_string_of_pos' p' (String "4" rest)
     | p'~1~0~1 => oct_string_of_pos' p' (String "5" rest)
     | p'~1~1~0 => oct_string_of_pos' p' (String "6" rest)
     | p'~1~1~1 => oct_string_of_pos' p' (String "7" rest)
     end.
Definition oct_string_of_pos (p : positive) : string
  := String "0" (String "o" (oct_string_of_pos' p "")).
Definition oct_string_of_N (n : N) : string
  := match n with
     | N0 => "0o0"
     | Npos p => oct_string_of_pos p
     end.
Definition oct_string_of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (oct_string_of_pos p)
     | Z0 => "0o0"
     | Zpos p => oct_string_of_pos p
     end.
Definition oct_string_of_nat (n : nat) : string
  := oct_string_of_N (N.of_nat n).

Fixpoint N_of_oct_string' (s : string) (rest : N)
  : N
  := match s with
     | "" => rest
     | String ch s'
       => N_of_oct_string'
            s'
            (if ascii_dec ch "0"
             then match rest with
                  | N0 => N0
                  | Npos p => Npos (p~0~0~0)
                  end
             else if ascii_dec ch "1"
             then match rest with
                  | N0 => Npos 1
                  | Npos p => Npos (p~0~0~1)
                  end
             else if ascii_dec ch "2"
             then match rest with
                  | N0 => Npos 2
                  | Npos p => Npos (p~0~1~0)
                  end
             else if ascii_dec ch "3"
             then match rest with
                  | N0 => Npos 3
                  | Npos p => Npos (p~0~1~1)
                  end
             else if ascii_dec ch "4"
             then match rest with
                  | N0 => Npos 4
                  | Npos p => Npos (p~1~0~0)
                  end
             else if ascii_dec ch "5"
             then match rest with
                  | N0 => Npos 5
                  | Npos p => Npos (p~1~0~1)
                  end
             else if ascii_dec ch "6"
             then match rest with
                  | N0 => Npos 6
                  | Npos p => Npos (p~1~1~0)
                  end
             else if ascii_dec ch "7"
             then match rest with
                  | N0 => Npos 7
                  | Npos p => Npos (p~1~1~1)
                  end
             else N0)
     end.
Definition N_of_oct_string (s : string) : N
  := match s with
     | String s0 (String so s)
       => if ascii_dec s0 "0"
          then if ascii_dec so "o"
               then N_of_oct_string' s N0
               else N0
          else N0
     | _ => N0
     end.
Definition pos_of_oct_string (s : string) : positive
  := match N_of_oct_string s with
     | N0 => 1
     | Npos p => p
     end.
Definition Z_of_oct_string (s : string) : Z
  := let '(is_neg, n) := match s with
                         | String s0 s'
                           => if ascii_dec s0 "-"
                              then (true, N_of_oct_string s')
                              else (false, N_of_oct_string s)
                         | EmptyString => (false, N_of_oct_string s)
                         end in
     match n with
     | N0 => Z0
     | Npos p => if is_neg then Zneg p else Zpos p
     end.
Definition nat_of_oct_string (s : string) : nat
  := N.to_nat (N_of_oct_string s).

Fixpoint pos_oct_app (p q:positive) : positive :=
  match q with
  | 1 => p~0~0~1
  | 2 => p~0~1~0
  | 3 => p~0~1~1
  | 4 => p~1~0~0
  | 5 => p~1~0~1
  | 6 => p~1~1~0
  | 7 => p~1~1~1
  | q~0~0~0 => (pos_oct_app p q)~0~0~0
  | q~0~0~1 => (pos_oct_app p q)~0~0~1
  | q~0~1~0 => (pos_oct_app p q)~0~1~0
  | q~0~1~1 => (pos_oct_app p q)~0~1~1
  | q~1~0~0 => (pos_oct_app p q)~1~0~0
  | q~1~0~1 => (pos_oct_app p q)~1~0~1
  | q~1~1~0 => (pos_oct_app p q)~1~1~0
  | q~1~1~1 => (pos_oct_app p q)~1~1~1
  end.

Fixpoint N_of_oct_string_of_pos' (p : positive) (rest : string) (base : N)
  : N_of_oct_string' (oct_string_of_pos' p rest) base
    = N_of_oct_string' rest match base with
                            | N0 => N.pos p
                            | Npos v => Npos (pos_oct_app v p)
                            end.
Proof.
  do 3 try destruct p as [p|p|]; destruct base; try reflexivity;
    cbn; rewrite N_of_oct_string_of_pos'; reflexivity.
Qed.

Lemma N_of_oct_string_of_N (n : N)
  : N_of_oct_string (oct_string_of_N n)
    = n.
Proof.
  destruct n; [ reflexivity | apply N_of_oct_string_of_pos' ].
Qed.

Lemma Z_of_oct_string_of_Z (z : Z)
  : Z_of_oct_string (oct_string_of_Z z)
    = z.
Proof.
  cbv [oct_string_of_Z Z_of_oct_string]; destruct z as [|z|z]; cbn;
    try reflexivity;
    rewrite N_of_oct_string_of_pos'; cbn; reflexivity.
Qed.

Lemma nat_of_oct_string_of_nat (n : nat)
  : nat_of_oct_string (oct_string_of_nat n)
    = n.
Proof.
  cbv [nat_of_oct_string oct_string_of_nat];
    rewrite N_of_oct_string_of_N, Nnat.Nat2N.id; reflexivity.
Qed.

Lemma pos_of_oct_string_of_pos (p : positive)
  : pos_of_oct_string (oct_string_of_pos p)
    = p.
Proof.
  cbv [oct_string_of_pos pos_of_oct_string N_of_oct_string]; cbn;
    rewrite N_of_oct_string_of_pos'; cbn; reflexivity.
Qed.

Example oct_string_of_pos_1 : oct_string_of_pos 1 = "0o1" := eq_refl.
Example oct_string_of_pos_2 : oct_string_of_pos 2 = "0o2" := eq_refl.
Example oct_string_of_pos_3 : oct_string_of_pos 3 = "0o3" := eq_refl.
Example oct_string_of_pos_7 : oct_string_of_pos 7 = "0o7" := eq_refl.
Example oct_string_of_pos_8 : oct_string_of_pos 8 = "0o10" := eq_refl.
Example oct_string_of_N_0 : oct_string_of_N 0 = "0o0" := eq_refl.
Example oct_string_of_Z_0 : oct_string_of_Z 0 = "0o0" := eq_refl.
Example oct_string_of_Z_m1 : oct_string_of_Z (-1) = "-0o1" := eq_refl.
Example oct_string_of_nat_0 : oct_string_of_nat 0 = "0o0" := eq_refl.
