(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Warning "generated-hyp-name" (disabled by default): a tactic sentence
    let Rocq choose hypothesis names, and a later sentence of the same proof
    uses one of them. *)

(** [record_sentence ~pstate ~run] runs [run ()], which executes the current
    tactic sentence on [pstate], and does the bookkeeping for the warning.
    When the warning is disabled this is just [run ()]. *)
val record_sentence :
  pstate:Declare.Proof.t -> run:(unit -> Declare.Proof.t) -> Declare.Proof.t
