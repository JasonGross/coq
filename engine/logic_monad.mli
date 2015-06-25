(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines the low-level monadic operations used by the
    tactic monad. The monad is divided into two layers: a non-logical
    layer which consists in operations which will not (or cannot) be
    backtracked in case of failure (input/output or persistent state)
    and a logical layer which handles backtracking, proof
    manipulation, and any other effect which needs to backtrack. *)


(** {6 Exceptions} *)


(** To help distinguish between exceptions raised by the IO monad from
    the one used natively by Coq, the former are wrapped in
    [Exception].  It is only used internally so that [catch] blocks of
    the IO monad would only catch exceptions raised by the [raise]
    function of the IO monad, and not for instance, by system
    interrupts. Also used in [Proofview] to avoid capturing exception
    from the IO monad ([Proofview] catches errors in its compatibility
    layer, and when lifting goal-level expressions). *)
exception Exception of exn
(** This exception is used to signal abortion in [timeout] functions. *)
exception Timeout
(** This exception is used by the tactics to signal failure by lack of
    successes, rather than some other exceptions (like system
    interrupts). *)
exception TacticFailure of exn


(** {6 Non-logical layer} *)

(** The non-logical monad is a simple [unit -> 'a] (i/o) monad. The
    operations are simple wrappers around corresponding usual
    operations and require little documentation. *)
module NonLogical : sig

  type (+'a, 'nls) t
  val return : 'a -> ('a, 'nls) t
  val (>>=) : ('a, 'nls) t -> ('a -> ('b, 'nls) t) -> ('b, 'nls) t
  val (>>) : (unit, 'nls) t -> ('a, 'nls) t -> ('a, 'nls) t
  val map : ('a -> 'b) -> ('a, 'nls) t -> ('b, 'nls) t

  val set : 'nls -> (unit, 'nls) t
  val get : ('nls, 'nls) t
  val modify : ('nls -> 'nls) -> (unit, 'nls) t

  val ignore : ('a, 'nls) t -> (unit, 'nls) t

  type 'a ref

  val ref : 'a -> ('a ref, 'nls) t
  (** [Pervasives.(:=)] *)
  val (:=) : 'a ref -> 'a -> (unit, 'nls) t
  (** [Pervasives.(!)] *)
  val (!) : 'a ref -> ('a, 'nls) t

  val read_line : (string, 'nls) t
  val print_char : char -> (unit, 'nls) t
  (** {!Pp.pp}. The buffer is also flushed. *)
  val print : Pp.std_ppcmds -> (unit, 'nls) t

  (** [Pervasives.raise]. Except that exceptions are wrapped with
      {!Exception}. *)
  val raise : ?info:Exninfo.info -> exn -> ('a, 'nls) t
  (** [try ... with ...] but restricted to {!Exception}. *)
  val catch : ('a, 'nls) t -> (Exninfo.iexn -> ('a, 'nls) t) -> ('a, 'nls) t
  val timeout : int -> ('a, 'nls) t -> ('a, 'nls) t

  (** Construct a monadified side-effect. Exceptions raised by the argument are
      wrapped with {!Exception}. *)
  val make : (unit -> 'a) -> ('a, 'nls) t

  (** [run] performs effects. *)
  val run : ('a, 'nls) t -> 'nls -> 'a * 'nls

end


(** {6 Logical layer} *)

(** The logical monad is a backtracking monad on top of which is
    layered a state monad (which is used to implement all of read/write,
    read only, and write only effects). The state monad being layered on
    top of the backtracking monad makes it so that the state is
    backtracked on failure.

    Backtracking differs from regular exception in that, writing (+)
    for exception catching and (>>=) for bind, we require the
    following extra distributivity laws:

    x+(y+z) = (x+y)+z

    zero+x = x

    x+zero = x

    (x+y)>>=k = (x>>=k)+(y>>=k) *)

(** A view type for the logical monad, which is a form of list, hence
    we can decompose it with as a list. *)
type ('a, 'b, 'e) list_view =
| Nil of 'e
| Cons of 'a * ('e -> 'b)

module BackState : sig

  type (+'a, 'nls, -'i, +'o, 'e) t
  val return : 'a -> ('a, 'nls, 'io, 'io, 'e) t
  val (>>=) : ('a, 'nls, 'i, 'm, 'e) t -> ('a -> ('b, 'nls, 'm, 'o, 'e) t) -> ('b, 'nls, 'i, 'o, 'e) t
  val (>>) : (unit, 'nls, 'i, 'm, 'e) t -> ('b, 'nls, 'm, 'o, 'e) t -> ('b, 'nls, 'i, 'o, 'e) t
  val map : ('a -> 'b) -> ('a, 'nls, 'i, 'o, 'e) t -> ('b, 'nls, 'i, 'o, 'e) t

  val ignore : ('a, 'nls, 'i, 'o, 'e) t -> (unit, 'nls, 'i, 'o, 'e) t

  val set : 'o -> (unit, 'nls, 'i, 'o, 'e) t
  val get : ('s, 'nls, 's, 's, 'e) t
  val modify : ('i -> 'o) -> (unit, 'nls, 'i, 'o, 'e) t

  val interleave : ('e1 -> 'e2) -> ('e2 -> 'e1) -> ('a, 'nls, 'i, 'o, 'e1) t ->
    ('a, 'nls, 'i, 'o, 'e2) t
  (** [interleave src dst m] adapts the exceptional content of the monad
      according to the functions [src] and [dst]. To ensure a meaningful result,
      those functions must form a retraction, i.e. [dst (src e1) = e1] for all
      [e1]. This is typically the case when the type ['e1] is [unit]. *)

  val zero : 'e -> ('a, 'nls, 'i, 'o, 'e) t
  val plus : ('a, 'nls, 'i, 'o, 'e) t -> ('e -> ('a, 'nls, 'i, 'o, 'e) t) -> ('a, 'nls, 'i, 'o, 'e) t

  val split : ('a, 'nls, 's, 's, 'e) t ->
    (('a, ('a, 'nls, 'i, 's, 'e) t, 'e) list_view, 'nls, 's, 's, 'e) t

  val once : ('a, 'nls, 'i, 'o, 'e) t -> ('a, 'nls, 'i, 'o, 'e) t
  val break : ('e -> 'e option) -> ('a, 'nls, 'i, 'o, 'e) t -> ('a, 'nls, 'i, 'o, 'e) t
  val lift : ('a, 'nls) NonLogical.t -> ('a, 'nls, 's, 's, 'e) t

  type ('a, 'nls, 'e) reified

  val repr : ('a, 'nls, 'e) reified -> (('a, ('a, 'nls, 'e) reified, 'e) list_view, 'nls) NonLogical.t

  val run : ('a, 'nls, 'i, 'o, 'e) t -> 'i -> ('a * 'o, 'nls, 'e) reified

end

(** The monad is parametrised in the types of state, environment and
    writer. *)
module type Param = sig

  (** Read only *)
  type e

  (** Write only *)
  type w

  (** [w] must be a monoid *)
  val wunit : w
  val wprod : w -> w -> w

  (** Read-write *)
  type s

  (** Update-only. Essentially a writer on [u->u]. *)
  type u

  (** [u] must be pointed. *)
  val uunit : u

  (** Non-logical update-only state. Essentially a writer on [u->u]. *)
  type nls

  (** [nls] must be pointed. *)
  val nlsunit : nls

end

module Logical (P:Param) : sig

  include Monad.S

  val ignore : 'a t -> unit t

  val set : P.s -> unit t
  val get : P.s t
  val modify : (P.s -> P.s) -> unit t
  val put : P.w -> unit t
  val current : P.e t
  val local : P.e -> 'a t -> 'a t
  val update : (P.u -> P.u) -> unit t

  val zero : Exninfo.iexn -> 'a t
  val plus : 'a t -> (Exninfo.iexn -> 'a t) -> 'a t
  val split : 'a t -> ('a, 'a t, Exninfo.iexn) list_view t
  val once : 'a t -> 'a t
  val break : (Exninfo.iexn -> Exninfo.iexn option) -> 'a t -> 'a t

  val lift : ('a, P.nls) NonLogical.t -> 'a t

  type 'a reified = ('a, P.nls, Exninfo.iexn) BackState.reified

  val repr : 'a reified -> (('a, 'a reified, Exninfo.iexn) list_view, P.nls) NonLogical.t

  val run : 'a t -> P.e -> P.s -> ('a * P.s * P.w * P.u) reified

  module Unsafe :
  sig
    type state = {
      rstate : P.e;
      ustate : P.u;
      wstate : P.w;
      sstate : P.s;
    }

    type nonlogical_state = P.nls

    val make : ('a, nonlogical_state, state, state, Exninfo.iexn) BackState.t -> 'a t
    val repr : 'a t -> ('a, nonlogical_state, state, state, Exninfo.iexn) BackState.t

  end

end
