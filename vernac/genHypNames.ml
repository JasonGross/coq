(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Warning "generated-hyp-name": a tactic sentence let Rocq choose some
   hypothesis names, and a later sentence of the same proof uses one of
   them. Such scripts break when the automatic naming changes (for
   instance when an inductive type or a binder is renamed). *)

open Names
open Pp

let warn_generated_hyp_name =
  CWarnings.create_warning ~name:"generated-hyp-name"
    ~from:[CWarnings.CoreCategories.fragile] ~default:CWarnings.Disabled ()

(* A sentence that generated hypothesis names *)
type entry = {
  e_loc : Loc.t;
  (* source text of the sentence, when the file could be read *)
  e_text : string option;
  (* the generated names, per goal produced by the sentence, in context order *)
  e_goals : Id.t list list;
  (* the generated names that are still in some goal and that no later
     sentence has named itself *)
  e_names : Id.Set.t;
  e_warned : bool;
}

type state = {
  proof : Id.t;
  entries : entry list; (* most recent first *)
}

let state : state option ref = Summary.ref ~name:"generated-hyp-names" None

(* Source text of a sentence *)

let file_cache : (string * string) option ref = ref None

let file_contents file =
  match !file_cache with
  | Some (f, c) when String.equal f file -> Some c
  | _ ->
    match In_channel.with_open_bin file In_channel.input_all with
    | c -> file_cache := Some (file, c); Some c
    | exception Sys_error _ -> None

let sentence_text loc =
  match loc.Loc.fname with
  | Loc.ToplevelInput -> None
  | Loc.InFile { file } ->
    match file_contents file with
    | None -> None
    | Some c ->
      let bp = loc.Loc.bp and ep = loc.Loc.ep in
      if 0 <= bp && bp <= ep && ep <= String.length c then Some (String.sub c bp (ep - bp))
      else None

(* Identifiers that occur in a piece of script, outside comments and
   strings. This is an approximation of the lexer: identifiers are maximal
   runs of letters, digits, [_], ['] and non-ASCII bytes. *)

let is_ident_char c =
  match c with
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true
  | c -> Char.code c >= 128

let idents_of_text s =
  let n = String.length s in
  let acc = ref CString.Set.empty in
  let rec skip_comment i depth =
    if i >= n then n
    else if depth = 0 then i
    else if i + 1 < n && s.[i] = '(' && s.[i+1] = '*' then skip_comment (i+2) (depth+1)
    else if i + 1 < n && s.[i] = '*' && s.[i+1] = ')' then skip_comment (i+2) (depth-1)
    else skip_comment (i+1) depth
  in
  let rec skip_string i =
    if i >= n then n
    else if s.[i] = '"' then
      if i + 1 < n && s.[i+1] = '"' then skip_string (i+2) else i+1
    else skip_string (i+1)
  in
  let rec loop i =
    if i >= n then ()
    else if i + 1 < n && s.[i] = '(' && s.[i+1] = '*' then loop (skip_comment (i+2) 1)
    else if s.[i] = '"' then loop (skip_string (i+1))
    else if is_ident_char s.[i] then begin
      let j = ref i in
      while !j < n && is_ident_char s.[!j] do incr j done;
      acc := CString.Set.add (String.sub s i (!j - i)) !acc;
      loop !j
    end
    else loop (i+1)
  in
  loop 0;
  !acc

(* Suggested replacement for the simple sentence shapes *)

let trim_sentence s =
  let s = String.trim s in
  let s = if CString.is_suffix "." s then String.sub s 0 (String.length s - 1) else s in
  String.trim s

(* Split an optional goal selector prefix, e.g. "2: " or "all: " *)
let split_selector s =
  match String.index_opt s ':' with
  | None -> "", s
  | Some i ->
    let sel = String.trim (String.sub s 0 i) in
    let is_sel =
      not (String.equal sel "") &&
      (String.equal sel "all" || String.equal sel "!" ||
       String.for_all (fun c -> ('0' <= c && c <= '9') || c = ' ' || c = ',' || c = '-') sel)
    in
    if is_sel then String.sub s 0 (i+1) ^ " ", String.trim (String.sub s (i+1) (String.length s - i - 1))
    else "", s

let pr_names ids = prlist_with_sep (fun () -> str " ") Id.print ids

let pr_or_and_pattern goals =
  str "[" ++ prlist_with_sep (fun () -> str "|") pr_names goals ++ str "]"

let case_tactics = ["destruct"; "edestruct"; "induction"; "einduction"; "inversion"]

let arg_is_simple arg =
  let words = String.split_on_char ' ' arg in
  not (String.equal arg "") &&
  not (String.exists (fun c -> c = ';' || c = '|' || c = '[' || c = ']') arg) &&
  not (List.exists (fun w -> List.mem w ["as"; "in"; "eqn"; "using"; "with"; "at"]) words)

let suggestion text goals =
  let text = trim_sentence text in
  let sel, tac = split_selector text in
  let all_names = List.concat goals in
  let non_empty = List.filter (fun l -> not (CList.is_empty l)) goals in
  let finish pp = Some (str sel ++ pp ++ str ".") in
  if String.equal tac "intros" && List.length non_empty = 1 then
    finish (str "intros " ++ pr_names all_names)
  else if String.equal tac "intro" && List.length all_names = 1 then
    finish (str "intro " ++ pr_names all_names)
  else
    match String.index_opt tac ' ' with
    | None -> None
    | Some i ->
      let head = String.sub tac 0 i in
      let arg = String.trim (String.sub tac i (String.length tac - i)) in
      if List.mem head case_tactics && arg_is_simple arg && not (CList.is_empty goals) then
        finish (str head ++ str " " ++ str arg ++ str " as " ++ pr_or_and_pattern goals)
      else None

(* The warning itself *)

type warning_data = {
  w_entry : entry;
  w_used : Id.t list;
  w_use_loc : Loc.t option;
}

let replacement d =
  match d.w_entry.e_text with
  | None -> None
  | Some text -> suggestion text d.w_entry.e_goals

let pr_warning d =
  let e = d.w_entry in
  (* generated names in context order, the live ones *)
  let names = List.filter (fun id -> Id.Set.mem id e.e_names) (List.concat e.e_goals) in
  let names = names @ List.filter (fun id -> not (List.mem id names)) (Id.Set.elements e.e_names) in
  let n = List.length names in
  let use = match d.w_use_loc with
    | Some loc -> Printf.sprintf "line %d" loc.Loc.line_nb
    | None -> "later"
  in
  let names_s = String.concat " " (List.map Id.to_string names) in
  let used_s = String.concat " " (List.map Id.to_string d.w_used) in
  let offsets = Printf.sprintf "%d-%d" e.e_loc.Loc.bp e.e_loc.Loc.ep in
  let head =
    Printf.sprintf "Hypothesis %s %s %s generated by this tactic, and a later tactic (%s) uses %s."
      (CString.plural n "name") names_s (if n = 1 then "was" else "were") use used_s
  in
  let tail = match replacement d with
    | Some pp ->
      strbrk (Printf.sprintf "To name %s in the script, replace offsets %s with \""
                (if n = 1 then "it" else "them") offsets)
      ++ pp ++ str "\"."
    | None ->
      strbrk (Printf.sprintf "Name %s in the script (offsets %s)."
                (if n = 1 then "it" else "them") offsets)
  in
  strbrk head ++ spc () ++ tail

let quickfix ~loc d =
  match replacement d with
  | Some pp -> [Quickfix.make ~loc pp]
  | None -> []

let warn = CWarnings.create_in warn_generated_hyp_name ~quickfix pr_warning

(* Hypothesis names of goals *)

(* context of a goal, oldest hypothesis first *)
let goal_hyps sigma ev =
  match Evd.find_undefined sigma ev with
  | evi -> List.rev (Evd.evar_filtered_context evi)
  | exception Not_found -> []

let goal_hyp_names sigma ev =
  List.map Context.Named.Declaration.get_id (goal_hyps sigma ev)

(* the declarations of all goals, by name *)
let live_decls p =
  let { Proof.sigma } = Proof.data p in
  Evar.Set.fold (fun ev acc ->
      List.fold_left (fun acc d ->
          let id = Context.Named.Declaration.get_id d in
          Id.Map.update id (function None -> Some [d] | Some l -> Some (d :: l)) acc)
        acc (goal_hyps sigma ev))
    (Proof.all_goals p) Id.Map.empty

let live_names p = Id.Map.domain (live_decls p)

(* [d] is the very declaration that some goal had before the sentence: the
   tactic did not touch this hypothesis, so a generated name that happens
   to be equal to it (e.g. a binder of a case analysis) is not its name. *)
let same_as_before before_decls d =
  match Id.Map.find_opt (Context.Named.Declaration.get_id d) before_decls with
  | None -> false
  | Some l -> List.exists (fun d' -> d' == d) l

let current_state pstate =
  let name = Declare.Proof.get_name pstate in
  match !state with
  | Some st when Id.equal st.proof name -> st
  | _ -> { proof = name; entries = [] }

(* Report the generated names that this sentence uses *)
let check_uses loc text st =
  match text with
  | None -> st
  | Some text ->
    let toks = idents_of_text text in
    let entries = List.map (fun e ->
        if e.e_warned then e
        else
          let used = List.filter (fun id -> CString.Set.mem (Id.to_string id) toks) (Id.Set.elements e.e_names) in
          if CList.is_empty used then e
          else begin
            warn ~loc:e.e_loc { w_entry = e; w_used = used; w_use_loc = loc };
            { e with e_warned = true }
          end)
        st.entries
    in
    { st with entries }

let record_sentence ~pstate ~run =
  if CWarnings.warning_status warn_generated_hyp_name = CWarnings.Disabled then run ()
  else
    let loc = Loc.get_current_command_loc () in
    let text = Option.cata sentence_text None loc in
    let st = current_state pstate in
    let st = check_uses loc text st in
    let before = Declare.Proof.get pstate in
    let before_goals = Proof.all_goals before in
    let before_decls = live_decls before in
    let before_live = Id.Map.domain before_decls in
    let pstate', recorded = Namegen.with_recorded_generated_ids run in
    let after = Declare.Proof.get pstate' in
    let { Proof.sigma; goals } = Proof.data after in
    let live = live_names after in
    let generated =
      Id.Map.fold (fun id decls acc ->
          if Id.Set.mem id recorded
          && List.exists (fun d -> not (same_as_before before_decls d)) decls
          then Id.Set.add id acc else acc)
        (live_decls after) Id.Set.empty
    in
    (* names that a user-given introduction took over *)
    let user_given = Id.Set.diff (Id.Set.diff live before_live) generated in
    let entries = List.filter_map (fun e ->
        let names = Id.Set.diff (Id.Set.inter e.e_names live) user_given in
        if Id.Set.is_empty names then None else Some { e with e_names = names })
        st.entries
    in
    let entries = match loc with
      | Some e_loc when not (Id.Set.is_empty generated) ->
        let produced = List.filter (fun ev -> not (Evar.Set.mem ev before_goals)) goals in
        let e_goals = List.map (fun ev ->
            List.filter (fun id -> Id.Set.mem id generated) (goal_hyp_names sigma ev))
            produced
        in
        { e_loc; e_text = text; e_goals; e_names = generated; e_warned = false } :: entries
      | _ -> entries
    in
    state := Some { st with entries };
    pstate'
