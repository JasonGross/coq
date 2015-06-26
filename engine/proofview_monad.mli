(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines the datatypes used as internal states by the
    tactic monad, and specialises the [Logic_monad] to these type. *)

(** {6 Traces} *)

module Trace : sig

  (** The intent is that an ['a forest] is a list of messages of type
      ['a]. But messages can stand for a list of more precise
      messages, hence the structure is organised as a tree. *)
  type 'a forest = 'a tree list
  and  'a tree   = Seq of 'a * 'a forest

  (** To build a trace incrementally, we use an intermediary data
      structure on which we can define an S-expression like language
      (like a simplified xml except the closing tags do not carry a
      name). *)
  type 'a incr
  val to_tree : 'a incr -> 'a forest

  (** [open a] opens a tag with name [a]. *)
  val opn : 'a -> 'a incr -> 'a incr

  (** [close] closes the last open tag. It is the responsibility of
      the user to close all the tags. *)
  val close : 'a incr -> 'a incr

  (** [leaf] creates an empty tag with name [a]. *)
  val leaf : 'a -> 'a incr -> 'a incr

  val adjust_opened_to_match : ?before_close:('a -> 'a incr -> 'a incr)
                               -> ?after_open:('a -> 'a incr -> 'a incr)
                               -> ('a -> 'a -> bool)
                               -> 'a list -> 'a incr -> 'a incr

end

(** {6 State types} *)

(** We typically label nodes of [Trace.tree] with messages to
    print. But we don't want to compute the result. *)
type lazy_msg = unit -> Pp.std_ppcmds

(** Info trace. *)
module InfoTrace : sig

  (** A type of unique identifiers for comparing equality of tags *)
  type tag_with_id

  (** The type of the tags for [info]/[trace]. *)
  type tag =
    | Msg of lazy_msg (** A simple message *)
    | Tactic of lazy_msg (** A tactic call *)
    | Zero (** A failure of the enclosing tag; not used for [info] *)
    | Dispatch  (** A call to [tclDISPATCH]/[tclEXTEND] *)
    | DBranch  (** A special marker to delimit individual branch of a dispatch. *)

  val new_tag : tag -> tag_with_id

  type state = tag_with_id Trace.incr
  type tree = tag_with_id Trace.forest

  (** Keeps track of the list of open tags, so we can adjust for
      backtracking *)
  type debug_logical_state = tag_with_id list

  val print : tree -> Pp.std_ppcmds

  (** [collapse n t] flattens the first [n] levels of [Tactic] in an
      info trace, effectively forgetting about the [n] top level of
      names (if there are fewer, the last name is kept). *)
  val collapse : int -> tree -> tree

end

(** Type of proof views: current [evar_map] together with the list of
    focused goals. *)
type proofview = {
  solution : Evd.evar_map;
  comb : Goal.goal list;
  shelf : Goal.goal list;
}

(** {6 Instantiation of the logic monad} *)

module P : sig
  type s = { proof_state : proofview * Environ.env;
             opened_tags : InfoTrace.debug_logical_state }

  (** Status (safe/unsafe) * given up *)
  type w = bool * Evar.t list

  val wunit : w
  val wprod : w -> w -> w

  (** Recording info and debug traces (true) or not. *)
  type e = { record_info : bool ; record_debug : bool }

  val do_record_none : e
  val do_record_info : e
  val do_record_debug : e

  type u = InfoTrace.state

  val uunit : u

  type nls = InfoTrace.state

  val nlsunit : nls

end

module Logical : module type of Logic_monad.Logical(P)


(** {6 Lenses to access to components of the states} *)

module type State = sig
  type t
  val get : t Logical.t
  val set : t -> unit Logical.t
  val modify : (t->t) -> unit Logical.t
end

module type Writer = sig
  type t
  val put : t -> unit Logical.t
end

(** Lens to the [proofview]. *)
module Pv : State with type t := proofview

(** Lens to the [evar_map] of the proofview. *)
module Solution : State with type t := Evd.evar_map

(** Lens to the list of focused goals. *)
module Comb : State with type t = Evar.t list

(** Lens to the global environment. *)
module Env : State with type t := Environ.env

(** Lens to the tactic status ([true] if safe, [false] if unsafe) *)
module Status : Writer with type t := bool

(** Lens to the list of goals which have been shelved during the
    execution of the tactic. *)
module Shelf : State with type t = Evar.t list

(** Lens to the list of goals which were given up during the execution
    of the tactic. *)
module Giveup : Writer with type t = Evar.t list

(** Lens and utilies pertaining to the info trace *)
module InfoTraceL : sig
  (** [record_trace t] behaves like [t] and compute its [info] trace. *)
  val record_info_trace : 'a Logical.t -> 'a Logical.t
  val record_debug_trace : 'a Logical.t -> 'a Logical.t

  val update : (InfoTrace.state -> InfoTrace.state) -> unit Logical.t
  val leaf : InfoTrace.tag -> unit Logical.t

  (** after backtracking or failure, we need to update the tags to
      close things that we skipped *)
  val sync_tags : P.s -> unit Logical.t

  (** [tag a t] opens tag [a] runs [t] then closes the tag. *)
  val tag : InfoTrace.tag -> 'a Logical.t -> 'a Logical.t
end
