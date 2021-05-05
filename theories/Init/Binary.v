(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Binary numbers *)

(** These numbers coded in base 2 will be used for parsing and printing
    other Coq numeral datatypes in an human-readable way.
    See the [Number Notation] command.
    We represent numbers in base 2 as lists of binary digits,
    in big-endian order (most significant digit comes first). *)

Require Import Datatypes Specif Decimal.

(** Unsigned integers are just lists of digits.
    For instance, two is (D1 (D0 Nil)) *)

Inductive uint :=
 | Nil
 | D0 (_:uint)
 | D1 (_:uint).

(** [Nil] is the number terminator. Taken alone, it behaves as zero,
    but rather use [D0 Nil] instead, since this form will be denoted
    as [0], while [Nil] will be printed as [Nil]. *)

Notation zero := (D0 Nil).

(** For signed integers, we use two constructors [Pos] and [Neg]. *)

Variant int := Pos (d:uint) | Neg (d:uint).

(** For decimal numbers, we use two constructors [Binary] and
    [BinaryExp], depending on whether or not they are given with an
    exponent (e.g., 0x1.a2p+01). [i] is the integral part while [f] is
    the fractional part (beware that leading zeroes do matter). *)

Variant binary :=
 | Binary (i:int) (f:uint)
 | BinaryExp (i:int) (f:uint) (e:Decimal.int).

Scheme Equality for uint.
Scheme Equality for int.
Scheme Equality for binary.

Declare Scope bin_uint_scope.
Delimit Scope bin_uint_scope with buint.
Bind Scope bin_uint_scope with uint.

Declare Scope bin_int_scope.
Delimit Scope bin_int_scope with bint.
Bind Scope bin_int_scope with int.

Register uint as num.binary_uint.type.
Register int as num.binary_int.type.
Register binary as num.binary.type.

Fixpoint nb_digits d :=
  match d with
  | Nil => O
  | D0 d | D1 d =>
    S (nb_digits d)
  end.

(** This representation favors simplicity over canonicity.
    For normalizing numbers, we need to remove head zero digits,
    and choose our canonical representation of 0 (here [D0 Nil]
    for unsigned numbers and [Pos (D0 Nil)] for signed numbers). *)

(** [nzhead] removes all head zero digits *)

Fixpoint nzhead d :=
  match d with
  | D0 d => nzhead d
  | _ => d
  end.

(** [unorm] : normalization of unsigned integers *)

Definition unorm d :=
  match nzhead d with
  | Nil => zero
  | d => d
  end.

(** [norm] : normalization of signed integers *)

Definition norm d :=
  match d with
  | Pos d => Pos (unorm d)
  | Neg d =>
    match nzhead d with
    | Nil => Pos zero
    | d => Neg d
    end
  end.

(** A few easy operations. For more advanced computations, use the conversions
    with other Coq numeral datatypes (e.g. Z) and the operations on them. *)

Definition opp (d:int) :=
  match d with
  | Pos d => Neg d
  | Neg d => Pos d
  end.

Definition abs (d:int) : uint :=
  match d with
  | Pos d => d
  | Neg d => d
  end.

(** For conversions with binary numbers, it is easier to operate
    on little-endian numbers. *)

Fixpoint revapp (d d' : uint) :=
  match d with
  | Nil => d'
  | D0 d => revapp d (D0 d')
  | D1 d => revapp d (D1 d')
  end.

Definition rev d := revapp d Nil.

Definition app d d' := revapp (rev d) d'.

Definition app_int d1 d2 :=
  match d1 with Pos d1 => Pos (app d1 d2) | Neg d1 => Neg (app d1 d2) end.

(** [nztail] removes all trailing zero digits and return both the
    result and the number of removed digits. *)

Definition nztail d :=
  let fix aux d_rev :=
    match d_rev with
    | D0 d_rev => let (r, n) := aux d_rev in pair r (S n)
    | _ => pair d_rev O
    end in
  let (r, n) := aux (rev d) in pair (rev r) n.

Definition nztail_int d :=
  match d with
  | Pos d => let (r, n) := nztail d in pair (Pos r) n
  | Neg d => let (r, n) := nztail d in pair (Neg r) n
  end.

(** [del_head n d] removes [n] digits at beginning of [d]
    or returns [zero] if [d] has less than [n] digits. *)

Fixpoint del_head n d :=
  match n with
  | O => d
  | S n =>
    match d with
    | Nil => zero
    | D0 d | D1 d =>
      del_head n d
    end
  end.

Definition del_head_int n d :=
  match d with
  | Pos d => del_head n d
  | Neg d => del_head n d
  end.

(** [del_tail n d] removes [n] digits at end of [d]
    or returns [zero] if [d] has less than [n] digits. *)

Definition del_tail n d := rev (del_head n (rev d)).

Definition del_tail_int n d :=
  match d with
  | Pos d => Pos (del_tail n d)
  | Neg d => Neg (del_tail n d)
  end.

Module Little.

(** Successor of little-endian numbers *)

Fixpoint succ d :=
  match d with
  | Nil => D1 Nil
  | D0 d => D1 d
  | D1 d => D0 (succ d)
  end.

(** Doubling little-endian numbers *)

Fixpoint double d :=
  match d with
  | Nil => Nil
  | D0 d => D0 (double d)
  | D1 d => D0 (succ_double d)
  end

with succ_double d :=
  match d with
  | Nil => D1 Nil
  | D0 d => D1 (double d)
  | D1 d => D1 (succ_double d)
  end.

End Little.
