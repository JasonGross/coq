(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init.
From Ltac2 Require Import Std.

Ltac2 Type t := inductive.

Ltac2 @ external equal : t -> t -> bool := "rocq-runtime.plugins.ltac2" "ind_equal".
(** Equality test. *)

Ltac2 Type data.
(** Type of data representing inductive blocks. *)

Ltac2 @ external data : t -> data := "rocq-runtime.plugins.ltac2" "ind_data".
(** Get the mutual blocks corresponding to an inductive type in the current
    environment. Panics if there is no such inductive. *)

Ltac2 @ external repr : data -> t := "rocq-runtime.plugins.ltac2" "ind_repr".
(** Returns the inductive corresponding to the block. Inverse of [data]. *)

Ltac2 @ external index : t -> int := "rocq-runtime.plugins.ltac2" "ind_index".
(** Returns the index of the inductive type inside its mutual block. Guaranteed
    to range between [0] and [nblocks data - 1] where [data] was retrieved
    using the above function. *)

Ltac2 @ external nblocks : data -> int := "rocq-runtime.plugins.ltac2" "ind_nblocks".
(** Returns the number of inductive types appearing in a mutual block. *)

Ltac2 @ external nconstructors : data -> int := "rocq-runtime.plugins.ltac2" "ind_nconstructors".
(** Returns the number of constructors appearing in the current block. *)

Ltac2 @ external get_block : data -> int -> data := "rocq-runtime.plugins.ltac2" "ind_get_block".
(** Returns the block corresponding to the nth inductive type. Index must range
    between [0] and [nblocks data - 1], otherwise the function panics. *)

Ltac2 @ external get_constructor : data -> int -> constructor := "rocq-runtime.plugins.ltac2" "ind_get_constructor".
(** Returns the nth constructor of the inductive type. Index must range between
    [0] and [nconstructors data - 1], otherwise the function panics. *)

Ltac2 @ external get_projections : data -> projection array option
  := "rocq-runtime.plugins.ltac2" "ind_get_projections".
(** Returns the list of projections for a primitive record,
    or [None] if the inductive is not a primitive record. *)

(** {2 Scheme lookup} *)

Ltac2 @ external scheme_lookup : string -> t -> Std.reference option
  := "rocq-runtime.plugins.ltac2" "ind_scheme_lookup".
(** [scheme_lookup kind ind] looks up the scheme registered under [kind] for
    inductive [ind]. Returns [None] if no such scheme is registered. Common
    scheme kind strings include ["rect_dep"], ["ind_dep"], ["rec_dep"],
    ["sind_dep"], ["rect_nodep"], ["ind_nodep"], ["rec_nodep"], ["sind_nodep"],
    ["case_dep"], ["case_nodep"], ["casep_dep"], ["casep_nodep"]. *)

Ltac2 @ external scheme_find : string -> t -> Std.reference
  := "rocq-runtime.plugins.ltac2" "ind_scheme_find".
(** Like [scheme_lookup], but generates the scheme on the fly if a builder is
    registered for the given scheme kind but the scheme has not been declared
    yet. Throws if the scheme cannot be found or generated. *)

Ltac2 @ external scheme_kind_exists : string -> bool
  := "rocq-runtime.plugins.ltac2" "ind_scheme_kind_exists".
(** Returns [true] if a scheme builder has been registered under the given
    kind string. *)
