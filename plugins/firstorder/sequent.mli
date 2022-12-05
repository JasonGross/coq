(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Formula

type h_item = GlobRef.t * Unify.Item.t option

type t

val has_fuel : t -> bool

val make_simple_atoms : t -> atoms

val iter_redexes : (Formula.t -> unit) -> t -> unit

val deepen: t -> t

val record: h_item -> t -> t

val lookup: Environ.env -> Evd.evar_map -> h_item -> t -> bool

val add_formula : flags:flags -> Environ.env -> Evd.evar_map -> side -> identifier -> constr -> t -> t

val re_add_formula_list : Evd.evar_map -> Formula.t list -> t -> t

val find_left : Evd.evar_map -> constr -> t -> GlobRef.t

val find_goal : Evd.evar_map -> t -> GlobRef.t

val take_formula : Evd.evar_map -> t -> Formula.t * t

val empty_seq : int -> t

val extend_with_ref_list : flags:flags -> Environ.env -> Evd.evar_map -> GlobRef.t list ->
  t -> t * Evd.evar_map

val extend_with_auto_hints : flags:flags -> Environ.env -> Evd.evar_map -> Hints.hint_db_name list ->
  t -> t * Evd.evar_map
