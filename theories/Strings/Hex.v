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

Fixpoint hex_string_of_pos' (p : positive) (rest : string) : string
  := match p with
     | 1 => String "1" rest
     | 2 => String "2" rest
     | 3 => String "3" rest
     | 4 => String "4" rest
     | 5 => String "5" rest
     | 6 => String "6" rest
     | 7 => String "7" rest
     | 8 => String "8" rest
     | 9 => String "9" rest
     | 10 => String "a" rest
     | 11 => String "b" rest
     | 12 => String "c" rest
     | 13 => String "d" rest
     | 14 => String "e" rest
     | 15 => String "f" rest
     | p'~0~0~0~0 => hex_string_of_pos' p' (String "0" rest)
     | p'~0~0~0~1 => hex_string_of_pos' p' (String "1" rest)
     | p'~0~0~1~0 => hex_string_of_pos' p' (String "2" rest)
     | p'~0~0~1~1 => hex_string_of_pos' p' (String "3" rest)
     | p'~0~1~0~0 => hex_string_of_pos' p' (String "4" rest)
     | p'~0~1~0~1 => hex_string_of_pos' p' (String "5" rest)
     | p'~0~1~1~0 => hex_string_of_pos' p' (String "6" rest)
     | p'~0~1~1~1 => hex_string_of_pos' p' (String "7" rest)
     | p'~1~0~0~0 => hex_string_of_pos' p' (String "8" rest)
     | p'~1~0~0~1 => hex_string_of_pos' p' (String "9" rest)
     | p'~1~0~1~0 => hex_string_of_pos' p' (String "a" rest)
     | p'~1~0~1~1 => hex_string_of_pos' p' (String "b" rest)
     | p'~1~1~0~0 => hex_string_of_pos' p' (String "c" rest)
     | p'~1~1~0~1 => hex_string_of_pos' p' (String "d" rest)
     | p'~1~1~1~0 => hex_string_of_pos' p' (String "e" rest)
     | p'~1~1~1~1 => hex_string_of_pos' p' (String "f" rest)
     end.
Definition hex_string_of_pos (p : positive) : string
  := String "0" (String "x" (hex_string_of_pos' p "")).
Definition hex_string_of_N (n : N) : string
  := match n with
     | N0 => "0x0"
     | Npos p => hex_string_of_pos p
     end.
Definition hex_string_of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (hex_string_of_pos p)
     | Z0 => "0x0"
     | Zpos p => hex_string_of_pos p
     end.
Definition hex_string_of_nat (n : nat) : string
  := hex_string_of_N (N.of_nat n).

Local Notation "a || b"
  := (if a then true else if b then true else false).
Fixpoint N_of_hex_string' (s : string) (rest : N)
  : N
  := match s with
     | "" => rest
     | String ch s'
       => N_of_hex_string'
            s'
            (if ascii_dec ch "0"
             then match rest with
                  | N0 => N0
                  | Npos p => Npos (p~0~0~0~0)
                  end
             else if ascii_dec ch "1"
             then match rest with
                  | N0 => Npos 1
                  | Npos p => Npos (p~0~0~0~1)
                  end
             else if ascii_dec ch "2"
             then match rest with
                  | N0 => Npos 2
                  | Npos p => Npos (p~0~0~1~0)
                  end
             else if ascii_dec ch "3"
             then match rest with
                  | N0 => Npos 3
                  | Npos p => Npos (p~0~0~1~1)
                  end
             else if ascii_dec ch "4"
             then match rest with
                  | N0 => Npos 4
                  | Npos p => Npos (p~0~1~0~0)
                  end
             else if ascii_dec ch "5"
             then match rest with
                  | N0 => Npos 5
                  | Npos p => Npos (p~0~1~0~1)
                  end
             else if ascii_dec ch "6"
             then match rest with
                  | N0 => Npos 6
                  | Npos p => Npos (p~0~1~1~0)
                  end
             else if ascii_dec ch "7"
             then match rest with
                  | N0 => Npos 7
                  | Npos p => Npos (p~0~1~1~1)
                  end
             else if ascii_dec ch "8"
             then match rest with
                  | N0 => Npos 8
                  | Npos p => Npos (p~1~0~0~0)
                  end
             else if ascii_dec ch "9"
             then match rest with
                  | N0 => Npos 9
                  | Npos p => Npos (p~1~0~0~1)
                  end
             else if ascii_dec ch "a" || ascii_dec ch "A"
             then match rest with
                  | N0 => Npos 10
                  | Npos p => Npos (p~1~0~1~0)
                  end
             else if ascii_dec ch "b" || ascii_dec ch "B"
             then match rest with
                  | N0 => Npos 11
                  | Npos p => Npos (p~1~0~1~1)
                  end
             else if ascii_dec ch "c" || ascii_dec ch "C"
             then match rest with
                  | N0 => Npos 12
                  | Npos p => Npos (p~1~1~0~0)
                  end
             else if ascii_dec ch "d" || ascii_dec ch "D"
             then match rest with
                  | N0 => Npos 13
                  | Npos p => Npos (p~1~1~0~1)
                  end
             else if ascii_dec ch "e" || ascii_dec ch "E"
             then match rest with
                  | N0 => Npos 14
                  | Npos p => Npos (p~1~1~1~0)
                  end
             else if ascii_dec ch "f" || ascii_dec ch "F"
             then match rest with
                  | N0 => Npos 15
                  | Npos p => Npos (p~1~1~1~1)
                  end
             else N0)
     end.
Definition N_of_hex_string (s : string) : N
  := match s with
     | String s0 (String so s)
       => if ascii_dec s0 "0"
          then if ascii_dec so "x"
               then N_of_hex_string' s N0
               else N0
          else N0
     | _ => N0
     end.
Definition pos_of_hex_string (s : string) : positive
  := match N_of_hex_string s with
     | N0 => 1
     | Npos p => p
     end.
Definition Z_of_hex_string (s : string) : Z
  := let '(is_neg, n) := match s with
                         | String s0 s'
                           => if ascii_dec s0 "-"
                              then (true, N_of_hex_string s')
                              else (false, N_of_hex_string s)
                         | EmptyString => (false, N_of_hex_string s)
                         end in
     match n with
     | N0 => Z0
     | Npos p => if is_neg then Zneg p else Zpos p
     end.
Definition nat_of_hex_string (s : string) : nat
  := N.to_nat (N_of_hex_string s).

Fixpoint pos_hex_app (p q:positive) : positive :=
  match q with
  | 1 => p~0~0~0~1
  | 2 => p~0~0~1~0
  | 3 => p~0~0~1~1
  | 4 => p~0~1~0~0
  | 5 => p~0~1~0~1
  | 6 => p~0~1~1~0
  | 7 => p~0~1~1~1
  | 8 => p~1~0~0~0
  | 9 => p~1~0~0~1
  | 10 => p~1~0~1~0
  | 11 => p~1~0~1~1
  | 12 => p~1~1~0~0
  | 13 => p~1~1~0~1
  | 14 => p~1~1~1~0
  | 15 => p~1~1~1~1
  | q~0~0~0~0 => (pos_hex_app p q)~0~0~0~0
  | q~0~0~0~1 => (pos_hex_app p q)~0~0~0~1
  | q~0~0~1~0 => (pos_hex_app p q)~0~0~1~0
  | q~0~0~1~1 => (pos_hex_app p q)~0~0~1~1
  | q~0~1~0~0 => (pos_hex_app p q)~0~1~0~0
  | q~0~1~0~1 => (pos_hex_app p q)~0~1~0~1
  | q~0~1~1~0 => (pos_hex_app p q)~0~1~1~0
  | q~0~1~1~1 => (pos_hex_app p q)~0~1~1~1
  | q~1~0~0~0 => (pos_hex_app p q)~1~0~0~0
  | q~1~0~0~1 => (pos_hex_app p q)~1~0~0~1
  | q~1~0~1~0 => (pos_hex_app p q)~1~0~1~0
  | q~1~0~1~1 => (pos_hex_app p q)~1~0~1~1
  | q~1~1~0~0 => (pos_hex_app p q)~1~1~0~0
  | q~1~1~0~1 => (pos_hex_app p q)~1~1~0~1
  | q~1~1~1~0 => (pos_hex_app p q)~1~1~1~0
  | q~1~1~1~1 => (pos_hex_app p q)~1~1~1~1
  end.

Fixpoint N_of_hex_string_of_pos' (p : positive) (rest : string) (base : N)
  : N_of_hex_string' (hex_string_of_pos' p rest) base
    = N_of_hex_string' rest match base with
                            | N0 => N.pos p
                            | Npos v => Npos (pos_hex_app v p)
                            end.
Proof.
  do 4 try destruct p as [p|p|]; destruct base; try reflexivity;
    cbn; rewrite N_of_hex_string_of_pos'; reflexivity.
Qed.

Lemma N_of_hex_string_of_N (n : N)
  : N_of_hex_string (hex_string_of_N n)
    = n.
Proof.
  destruct n; [ reflexivity | apply N_of_hex_string_of_pos' ].
Qed.

Lemma Z_of_hex_string_of_Z (z : Z)
  : Z_of_hex_string (hex_string_of_Z z)
    = z.
Proof.
  cbv [hex_string_of_Z Z_of_hex_string]; destruct z as [|z|z]; cbn;
    try reflexivity;
    rewrite N_of_hex_string_of_pos'; cbn; reflexivity.
Qed.

Lemma nat_of_hex_string_of_nat (n : nat)
  : nat_of_hex_string (hex_string_of_nat n)
    = n.
Proof.
  cbv [nat_of_hex_string hex_string_of_nat];
    rewrite N_of_hex_string_of_N, Nnat.Nat2N.id; reflexivity.
Qed.

Lemma pos_of_hex_string_of_pos (p : positive)
  : pos_of_hex_string (hex_string_of_pos p)
    = p.
Proof.
  cbv [hex_string_of_pos pos_of_hex_string N_of_hex_string]; cbn;
    rewrite N_of_hex_string_of_pos'; cbn; reflexivity.
Qed.

Example hex_string_of_pos_1 : hex_string_of_pos 1 = "0x1" := eq_refl.
Example hex_string_of_pos_2 : hex_string_of_pos 2 = "0x2" := eq_refl.
Example hex_string_of_pos_3 : hex_string_of_pos 3 = "0x3" := eq_refl.
Example hex_string_of_pos_7 : hex_string_of_pos 7 = "0x7" := eq_refl.
Example hex_string_of_pos_8 : hex_string_of_pos 8 = "0x8" := eq_refl.
Example hex_string_of_pos_9 : hex_string_of_pos 9 = "0x9" := eq_refl.
Example hex_string_of_pos_10 : hex_string_of_pos 10 = "0xa" := eq_refl.
Example hex_string_of_pos_11 : hex_string_of_pos 11 = "0xb" := eq_refl.
Example hex_string_of_pos_12 : hex_string_of_pos 12 = "0xc" := eq_refl.
Example hex_string_of_pos_13 : hex_string_of_pos 13 = "0xd" := eq_refl.
Example hex_string_of_pos_14 : hex_string_of_pos 14 = "0xe" := eq_refl.
Example hex_string_of_pos_15 : hex_string_of_pos 15 = "0xf" := eq_refl.
Example hex_string_of_pos_16 : hex_string_of_pos 16 = "0x10" := eq_refl.
Example hex_string_of_N_0 : hex_string_of_N 0 = "0x0" := eq_refl.
Example hex_string_of_Z_0 : hex_string_of_Z 0 = "0x0" := eq_refl.
Example hex_string_of_Z_m1 : hex_string_of_Z (-1) = "-0x1" := eq_refl.
Example hex_string_of_nat_0 : hex_string_of_nat 0 = "0x0" := eq_refl.
