(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines the datatypes used as internal states by the
    tactic monad, and specialises the [Logic_monad] to these type. *)

(** {6 Trees/forest for traces} *)

module Trace = struct

  (** The intent is that an ['a forest] is a list of messages of type
      ['a]. But messages can stand for a list of more precise
      messages, hence the structure is organised as a tree. *)
  type 'a forest = 'a tree list
  and  'a tree   = Seq of 'a * 'a forest

  (** To build a trace incrementally, we use an intermediary data
      structure on which we can define an S-expression like language
      (like a simplified xml except the closing tags do not carry a
      name). Note that nodes are built from right to left in ['a
      incr], the result is mirrored when returning so that in the
      exposed interface, the forest is read from left to right.

      Concretely, we want to add a new tree to a forest: and we are
      building it by adding new trees to the left of its left-most
      subtrees which is built the same way. *)
  type 'a incr = { head:'a forest ; opened: 'a tree list }

  (** S-expression like language as ['a incr] transformers. It is the
      responsibility of the library builder not to use [close] when no
      tag is open. *)
  let empty_incr = { head=[] ; opened=[] }
  let opn a { head ; opened } = { head ; opened = Seq(a,[])::opened }
  let close { head ; opened } =
    match opened with
    | [a] -> { head = a::head ; opened=[] }
    | a::Seq(b,f)::opened -> { head ; opened=Seq(b,a::f)::opened }
    | [] -> assert false
  let leaf a s = close (opn a s)

  let rec opened_matches (beq : 'a -> 'a -> bool) should_be_opened actually_opened =
    match should_be_opened, actually_opened with
    | [], [] -> true
    | [], _ -> false
    | _, [] -> false
    | so::sos, Seq(ao, _)::aos -> beq so ao && opened_matches beq sos aos

  (** Check if should_be_opened is the same as opened.  If so, return
      the incr as-is.  If no, close and open tags as necessary to make
      them match.

      Note: We give [(type a)] and the type signatures explicitly
      because it makes debugging the OCaml code easier. *)
  let adjust_opened_to_match (type a)
                             ?(before_close = fun _ x -> x)
                             ?(after_open = fun _ x -> x)
                             (beq : a -> a -> bool) =
    let rec adjust (should_be_opened : a list) ({ head ; opened } : a incr) =
      if opened_matches beq should_be_opened opened then
        { head ; opened }
      else if List.length should_be_opened < List.length opened then
        match opened with
        | Seq(t, _)::_ -> adjust should_be_opened (close (before_close t { head ; opened }))
        | [] -> assert false (* if List.length x < List.length y, y is non-empty *)
      else if List.length should_be_opened > List.length opened then
        match should_be_opened with
        | t::ts -> adjust ts (after_open t (opn t { head ; opened }))
        | [] -> assert false
      else
        match should_be_opened, opened with
        | t::ts, Seq(t', _)::ts' -> after_open t (opn t (adjust ts (close (before_close t' { head ; opened }))))
        | [], _ | _, [] -> assert false
    in adjust

  (** Returning a forest. It is the responsibility of the library
      builder to close all the tags. *)
  (* spiwack: I may want to close the tags instead, to deal with
     interruptions. *)
  let rec mirror f = List.rev_map mirror_tree f
  and mirror_tree (Seq(a,f)) = Seq(a,mirror f)

  let to_tree = function
    | { head ; opened=[] } -> mirror head
    | { head ; opened=_::_} -> assert false

end



(** {6 State types} *)

(** We typically label nodes of [Trace.tree] with messages to
    print. But we don't want to compute the result. *)
type lazy_msg = unit -> Pp.std_ppcmds
let pr_lazy_msg msg = msg ()

(** Info trace. *)
module InfoTrace = struct

  module Gensym = struct
    type t = int

    let (=) : t -> t -> bool = Int.equal

    let last_id = Pervasives.ref 0

    let fresh_id () : t =
      last_id := !last_id + 1;
      !last_id
  end

  (** The type of the tags for [info]. *)
  type tag =
    | Msg of lazy_msg (** A simple message *)
    | Tactic of lazy_msg (** A tactic call *)
    | Zero (** A failure of the enclosing tag; used only for debug *)
    | Dispatch  (** A call to [tclDISPATCH]/[tclEXTEND] *)
    | DBranch  (** A special marker to delimit individual branch of a dispatch. *)

  type tag_with_id = tag * Gensym.t

  let new_tag t =
    (t, Gensym.fresh_id ())

  let (=) (tag0, tag0_id) (tag1, tag1_id) =
    Gensym.(=) tag0_id tag1_id
    (*match tag0, tag1 with
    | Msg msg0, Msg msg1 -> Pervasives.(=) msg0 msg1 (* FIXME? *)
    | Msg _, _ -> false
    | Tactic msg0, Tactic msg1 -> Pervasives.(=) msg0 msg1 (* FIXME? *)
    | Tactic _, _ -> false
    | Zero, Zero -> true
    | Zero, _ -> false
    | Dispatch, Dispatch -> true
    | Dispatch, _ -> false
    | DBranch, DBranch -> true
    | DBranch, _ -> false*)

  type state = tag_with_id Trace.incr
  type tree = tag_with_id Trace.forest

  (** Keeps track of the list of open tags, so we can adjust for
      backtracking *)
  type debug_logical_state = tag_with_id list

  let pr_in_comments m = Pp.(str"(* "++pr_lazy_msg m++str" *)")

  let unbranch = function
    | Trace.Seq ((DBranch,_),brs) -> brs
    | Trace.Seq ((Zero,_),brs) -> brs
    | Trace.Seq ((t,_),_) ->
        match t with
        | DBranch -> assert false
        | Msg msg -> Errors.anomaly (Pp.str "Trace can only unbranch branches; a Msg is not a DBranch")
        | Tactic msg -> Errors.anomaly (Pp.str "Trace can only unbranch branches; a Tactic is not a DBranch")
        | Zero -> Errors.anomaly (Pp.str "Trace can only unbranch branches; a Zero is not a DBranch")
        | Dispatch -> Errors.anomaly (Pp.str "Trace can only unbranch branches; a Dispatch is not a DBranch")

  let is_empty_branch = let open Trace in function
    | Seq((DBranch,_),[]) -> true
    | _ -> false

  (** Dispatch with empty branches are (supposed to be) equivalent to
      [idtac] which need not appear, so they are removed from the
      trace. *)
  let dispatch id brs =
    let open Trace in
    if CList.for_all is_empty_branch brs then None
    else Some (Seq((Dispatch,id),brs))

  let constr = let open Trace in function
    | (Dispatch,id) -> dispatch id
    | t -> fun br -> Some (Seq(t,br))

  let rec compress_tree = let open Trace in function
    | Seq(t,f) -> constr t (compress f)
  and compress f =
    CList.map_filter compress_tree f

  let rec is_empty = let open Trace in function
    | Seq(Dispatch,brs) -> List.for_all is_empty brs
    | Seq(DBranch,br) -> List.for_all is_empty br
    | _ -> false

  (** [with_sep] is [true] when [Tactic m] must be printed with a
      trailing semi-colon. *)
  let rec pr_tree with_sep = let open Trace in function
    | Seq ((Msg m,_),[]) -> pr_in_comments m
    | Seq ((Tactic m,_),_) ->
        let tail = if with_sep then Pp.str";" else Pp.mt () in
        Pp.(pr_lazy_msg m ++ tail)
    | Seq ((Zero,_),_) ->
        Pp.(Pp.str"(* failed *)" ++ Pp.mt ())
    | Seq ((Dispatch,_),brs) ->
        let tail = if with_sep then Pp.str";" else Pp.mt () in
        Pp.(pr_dispatch brs++tail)
    | Seq ((Msg _,_),_::_) | Seq ((DBranch,_),_) -> assert false
  and pr_dispatch brs =
    let open Pp in
    let brs = List.map unbranch brs in
    match brs with
    | [br] -> pr_forest br
    | _ ->
        let sep () = spc()++str"|"++spc() in
        let branches = prlist_with_sep sep pr_forest brs in
        str"[>"++spc()++branches++spc()++str"]"
  and pr_forest = function
    | [] -> Pp.mt ()
    | [tr] -> pr_tree false tr
    | tr::l -> Pp.(pr_tree true tr ++ pr_forest l)

  let print f =
    pr_forest (compress f)

  let rec collapse_tree n t =
    let open Trace in
    match n , t with
    | 0 , t -> [t]
    | _ , (Seq((Tactic _,_),[]) as t) -> [t]
    | n , Seq((Tactic _,_),f) -> collapse (pred n) f
    | n , Seq(((Zero,_) as t), brs)
    | n,  Seq(((Dispatch,_) as t), brs)
    | n,  Seq(((DBranch,_) as t), brs) -> [Seq(t, (collapse n brs))]
    | _ , (Seq((Msg _,_),_) as t) -> [t]
  and collapse n f =
    CList.map_append (collapse_tree n) f
end


(** Type of proof views: current [evar_map] together with the list of
    focused goals. *)
type proofview = { solution : Evd.evar_map; comb : Goal.goal list }


(** {6 Instantiation of the logic monad} *)

(** Parameters of the logic monads *)
module P = struct

  type s = { proof_state : proofview * Environ.env;
             opened_tags : InfoTrace.debug_logical_state }

  (** Recording info and debug traces (true) or not. *)
  type e = { record_info : bool ; record_debug : bool }

  let do_record_none : e = { record_info = false ; record_debug = false }
  let do_record_info : e = { record_info = true ; record_debug = false }
  let do_record_debug : e = { record_info = false ; record_debug = true }

  (** Status (safe/unsafe) * shelved goals * given up *)
  type w = bool * Evar.t list * Evar.t list

  let wunit = true , [] , []
  let wprod (b1,s1,g1) (b2,s2,g2) = b1 && b2 , s1@s2 , g1@g2

  type u = InfoTrace.state

  let uunit = Trace.empty_incr

  type nls = InfoTrace.state

  let nlsunit = Trace.empty_incr

end

module Logical = Logic_monad.Logical(P)


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

module Pv : State with type t := proofview = struct
  let get = Logical.(map (fun { P.proof_state = (p,_) } -> p) get)
  let set p = Logical.modify (fun { P.proof_state = (_,e) ; P.opened_tags = opened_tags } ->
                               { P.proof_state = (p,e) ; opened_tags = opened_tags })
  let modify  f= Logical.modify (fun { P.proof_state = (p,e) ; P.opened_tags = opened_tags } ->
                                  { P.proof_state = (f p,e) ; opened_tags = opened_tags })
end

module Solution : State with type t := Evd.evar_map = struct
  let get = Logical.map (fun {solution} -> solution) Pv.get
  let set s = Pv.modify (fun pv -> { pv with solution = s })
  let modify f = Pv.modify (fun pv -> { pv with solution = f pv.solution })
end

module Comb : State with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let get = Logical.map (fun {comb} -> comb) Pv.get
  let set c = Pv.modify (fun pv -> { pv with comb = c })
  let modify f = Pv.modify (fun pv -> { pv with comb = f pv.comb })
end

module Env : State with type t := Environ.env = struct
  let get = Logical.(map (fun { P.proof_state = (_,e) } -> e) get)
  let set e = Logical.modify (fun { P.proof_state = (p,_) ; P.opened_tags = opened_tags } ->
                               { P.proof_state = (p,e) ; opened_tags = opened_tags })
  let modify f = Logical.modify (fun { P.proof_state = (p,e) ; P.opened_tags = opened_tags } ->
                                  { P.proof_state = (p,f e) ; opened_tags = opened_tags })
end

module Status : Writer with type t := bool = struct
  let put s = Logical.put (s,[],[])
end

module Shelf : Writer with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let put sh = Logical.put (true,sh,[])
end

module Giveup : Writer with type t = Evar.t list = struct
    (* spiwack: I don't know why I cannot substitute ([:=]) [t] with a type expression. *)
  type t = Evar.t list
  let put gs = Logical.put (true,[],gs)
end

(** Lens and utilies pertaining to the info and debug traces *)
module InfoTraceL = struct
  let recording = Logical.current

  let raw_if_recording t_info t_debug r =
    let open P in
    let open Logical in
    match r.record_info, r.record_debug with
    | true, true -> t_info >> t_debug
    | true, false -> t_info
    | false, true -> t_debug
    | false, false -> return ()

  let if_recording t_info t_debug =
    let open Logical in
    recording >>= raw_if_recording t_info t_debug

  let record_info_trace t =
    Logical.local P.do_record_info t

  let record_debug_trace t =
    Logical.local P.do_record_debug t

  let raw_update f f_tags =
    let open P in
    let open Logical in
    raw_if_recording
      (Logical.update f)
      (Logical.lift (Logic_monad.NonLogical.modify f) >>
       Logical.modify (fun { proof_state ; opened_tags } ->
                        { proof_state = proof_state ; opened_tags = f_tags opened_tags }))

  let update f =
    let open Logical in
    recording >>= raw_update f (fun x -> x)

  let leaf a = update (Trace.leaf (InfoTrace.new_tag a))

  (** after backtracking or failure, we need to update the tags to
      close things that we skipped *)
  let sync_tags =
    let open P in
    let open Logical in
    let before_close = (fun _ -> Trace.leaf (InfoTrace.new_tag InfoTrace.Zero)) in
    fun { proof_state ; opened_tags } ->
      if_recording
        (return ())
        (Logical.lift
          (Logic_monad.NonLogical.modify
            (Trace.adjust_opened_to_match ~before_close:before_close InfoTrace.(=) opened_tags)))

  let tag a t =
    let open P in
    let open Logical in
    let a = InfoTrace.new_tag a in
    recording >>= fun r ->
    if r.record_info || r.record_debug then begin
      raw_update (Trace.opn a)
                 (fun opened_tags -> a::opened_tags) r >>
      t >>= fun ret ->
      raw_update Trace.close
                 (function | x::xs -> xs | [] -> assert false) r >>
      return ret
    end else
      t
end
