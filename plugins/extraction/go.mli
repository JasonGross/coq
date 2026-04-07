(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val go_descr : Common.State.t Miniml.language_descr

(** [write_go_mod dir module_prefix] generates a go.mod file in [dir]
    with the given [module_prefix] as the module path. *)
val write_go_mod : string -> string -> unit
