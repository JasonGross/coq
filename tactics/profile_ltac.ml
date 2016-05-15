open Pp
open Printer
open Util


(** [is_profiling] and the profiling info ([stack]) should be synchronized with the document; the rest of the ref cells are either local to individual tactic invocations, or global flags, and need not be synchronized, since no document-level backtracking happens within tactics. *)
let is_profiling = Summary.ref false ~name:"is-profiling-ltac"
let set_profiling b = is_profiling := b

let should_display_profile_at_close = ref false
let set_display_profile_at_close b = should_display_profile_at_close := b


let new_call = ref false
let entered_call() = new_call := true
let is_new_call() = let b = !new_call in new_call := false; b

type entry = {total : float; local : float; ncalls : int; max_total : float}
let empty_entry = {total = 0.; local = 0.; ncalls = 0; max_total = 0.}
let add_entry e add_total {total; local; ncalls; max_total} =
  {total = if add_total then e.total +. total else e.total;
   local = e.local +. local;
   ncalls = e.ncalls + ncalls;
   max_total = if add_total then max e.max_total max_total else e.max_total}

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type treenode = {entry : entry;
		 current_child : (string * float (* start time *) * treenode) option;
		 children : treenode StringMap.t}
let stack = Summary.ref {entry=empty_entry; current_child=None; children=StringMap.empty} ~name:"ltac-profiling-stack"


let get_node c table =
  try StringMap.find c table
  with Not_found ->
    {entry=empty_entry; current_child=None; children=StringMap.empty}

let rec add_node node node' =
  {node with
    entry = add_entry node.entry true node'.entry;
    children =
      StringMap.mapi
	(fun s node' -> add_node (get_node s node.children) node')
	node'.children}

let time() =
  let times = Unix.times() in
  times.Unix.tms_utime +. times.Unix.tms_stime

let rec print_treenode indent (tn : treenode) =
  msgnl(str(indent^"{ entry = {"));
  msg(str(indent^"total = "));
  msgnl(str (indent^(string_of_float (tn.entry.total))));
  msg(str(indent^"local = "));
  msgnl(str (indent^(string_of_float tn.entry.local)));
  msg(str(indent^"ncalls = "));
  msgnl(str (indent^(string_of_int tn.entry.ncalls)));
  msg(str(indent^"max_total = "));
  msgnl(str (indent^(string_of_float tn.entry.max_total)));
  msgnl(str(indent^"}"));
  msg(str(indent^"current_child = "));
  (match tn.current_child with
  | None -> msgnl(str("None"))
  | Some (name, start_time, subtree) -> begin
    msgnl(str("("^name^", "^(string_of_float start_time)^", "));
    print_treenode (indent^"  ") subtree;
    msgnl(str(indent^")"));
  end);
  msgnl(str(indent^"children = {"));
  StringMap.iter
    (fun s node ->
      msgnl(str(indent^" "^s^" |-> "));
      print_treenode (indent^"  ") node
    )
    tn.children;
  msgnl(str(indent^"} }"))

let rec print_stack (st : treenode list) =
  (match st with
    | [] -> msgnl(str "[]")
    | x::xs -> print_treenode "" x; msgnl(str("::")); print_stack xs)


let string_of_call ck =
  let s =
  string_of_ppcmds
    (match ck with
       | Proof_type.LtacNotationCall s -> Names.KerName.print s
       | Proof_type.LtacNameCall cst -> Pptactic.pr_ltac_constant cst
       | Proof_type.LtacVarCall (id,t) -> Nameops.pr_id id
       | Proof_type.LtacAtomCall te ->
	 (Pptactic.pr_glob_tactic (Global.env())
	    (Tacexpr.TacAtom (Loc.ghost,te)))
       | Proof_type.LtacConstrInterp (c,_) ->
	 pr_glob_constr_env (Global.env()) c
       | Proof_type.LtacMLCall te ->
	 (Pptactic.pr_glob_tactic (Global.env())
            te)
    ) in
  for i = 0 to String.length s - 1 do if s.[i] = '\n' then s.[i] <- ' ' done;
  let s = try String.sub s 0 (CString.string_index_from s 0 "(*") with Not_found -> s in
  CString.strip s

(** given a profile, exit all of the tactics below the current one, and give the new profile *)
let rec close_tactics current_time profile =
  match profile.current_child with
  | None -> profile
  | Some (name, start_time, subtree) ->
    let subtree = close_tactics current_time subtree in
    let diff = current_time -. start_time in
    let subtree =
      {subtree with
	entry = add_entry subtree.entry true {total=diff; local=diff; ncalls=1; max_total=diff}} in
    {entry = add_entry profile.entry false {total=0.; local= -. diff; ncalls=0; max_total=0.};
     current_child = None;
     children = StringMap.add name subtree profile.children}

(** Given a reversed call trace (top-level tactic first), a profiling tree, and the name of the tactic call above us, return the total time taken by the tactics we've left since we last updated the profile, and update the profile to match the tactic trace at the current time *)
let rec sync_tactic current_time rev_call_trace (profile : treenode) (parent_name : string option) =
  match rev_call_trace with
  | (_, c) :: trace' ->
    let s = string_of_call c in
    if Some s = parent_name then (
      msgnl(str("parent "^s));
      sync_tactic current_time trace' profile parent_name
    ) else (
      match profile.current_child with
      | Some (child_name, start_time, subtree) when s = child_name ->
	msgnl(str("eq "^s));
	let subtree = sync_tactic current_time trace' subtree (Some s) in
	{profile with
	  current_child = Some (s, start_time, subtree)}
      | _ ->
	msg(str("fresh "^s));
	(match trace' with
	| [] -> msgnl(str(" ([])"))
	| (_, c) :: _ -> msgnl(str(" ("^(string_of_call c)^")"))
	);
	let profile = close_tactics current_time profile in
	let prev_child = get_node s profile.children in
	let children = sync_tactic current_time trace' prev_child (Some s) in
	{profile with
	  current_child = Some (s, current_time, children)}
    )
  | [] ->
    close_tactics current_time profile

let exit_tactic call_trace =
  let rev_call_trace = List.rev (List.tl call_trace) in (* tl, so that we close the current tactic *)
  let new_stack = sync_tactic (time()) rev_call_trace !stack None in
  msgnl(str("LEAVING"));
  print_treenode "" new_stack;
  stack := new_stack

let tclFINALLY tac (finally : unit Proofview.tactic) =
  let open Proofview.Notations in
  Proofview.tclIFCATCH
    tac
    (fun v -> finally <*> Proofview.tclUNIT v)
    (fun (exn,info) -> finally <*> Proofview.tclZERO ~info exn)

let do_profile s call_trace tac =
  let open Proofview.Notations in
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
  if !is_profiling && is_new_call() then
    match call_trace with
      | (_, c) :: _ ->
	msgnl(str("ENTERING "^(string_of_call c)^" "^s^" "^(string_of_int (List.length call_trace))));
	let new_stack = sync_tactic (time()) (List.rev call_trace) !stack None in
	print_treenode "" new_stack;
	stack := new_stack;
	true
      | [] -> false
  else false)) >>= function
  | true ->
    tclFINALLY
      tac
      (Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
	exit_tactic call_trace)))
  | false -> tac



let format_sec x = (Printf.sprintf "%.3fs" x)
let format_ratio x = (Printf.sprintf "%.1f%%" (100. *. x))
let padl n s = ws (max 0 (n - utf8_length s)) ++ str s
let padr n s = str s ++ ws (max 0 (n - utf8_length s))
let padr_with c n s =
  let ulength = utf8_length s in
  str (utf8_sub s 0 n) ++ str(String.make (max 0 (n - ulength)) c)

let rec list_iter_is_last f = function
  | []      -> ()
  | [x]     -> f true x
  | x :: xs -> f false x; list_iter_is_last f xs

let header() =
  msgnl(str" tactic                                    self  total   calls       max");
  msgnl(str"────────────────────────────────────────┴──────┴──────┴───────┴─────────┘")

let rec print_node all_total indent prefix (s,n) =
  let e = n.entry in
  msgnl(
    h 0(
      padr_with '-' 40 (prefix ^ s ^ " ")
      ++padl 7 (format_ratio (e.local /. all_total))
      ++padl 7 (format_ratio (e.total /. all_total))
      ++padl 8 (string_of_int e.ncalls)
      ++padl 10 (format_sec(e.max_total))
    )
    );
  print_table all_total indent false n.children

and print_table all_total indent first_level table =
  let ls = StringMap.fold
	     (fun s n l -> if n.entry.total /. all_total < 0.02 then l else (s, n) :: l)
      table [] in
  match ls with
  | [(s,n)]  when (not first_level) ->
     print_node all_total indent (indent^"└") (s,n)
  | _ ->
     let ls = List.sort (fun (_, n1) (_, n2) -> compare n2.entry.total n1.entry.total) ls in
     list_iter_is_last
       (fun is_last ->
	print_node
	  all_total
	  (indent^if first_level then "" else if is_last then "  " else " │")
	  (indent^if first_level then "─" else if is_last then " └─" else " ├─")
       )
       ls

let print_results() =
  let tree = !stack.children in
  let all_total = -. !stack.entry.local in
  assert (!stack.current_child = None);
  let global = ref StringMap.empty in
  let rec cumulate table =
    StringMap.iter
      (fun s node ->
	let node' = get_node s !global in
	let node' =
	  {node' with
	    entry = add_entry node'.entry true node.entry} in
	global := StringMap.add s node' !global;
	cumulate node.children
      )
      table
  in
  cumulate tree;
  msgnl(str"");
  msgnl(h 0(
      str"total time: "++padl 11 (format_sec(all_total))
    )
       );
  msgnl(str"");
  header();
  print_table all_total "" true !global;
  msgnl(str"");
  header();
  print_table all_total "" true tree
  (* FOR DEBUGGING *)
  ;
     msgnl(str"");
     print_treenode "" (!stack)


let print_results_tactic tactic =
  let tree = !stack.children in
  let table_tactic = ref StringMap.empty in
  let rec cumulate table =
    StringMap.iter
      (fun s node ->
       if String.sub (s^".") 0 (min (1+String.length s) (String.length tactic)) = tactic
       then table_tactic := StringMap.add s (add_node (get_node s !table_tactic) node) !table_tactic
       else cumulate node.children
      )
      table
  in
  cumulate tree;
  let all_total = -. !stack.entry.local in
  let tactic_total =
    StringMap.fold
      (fun _ node all_total -> node.entry.total +. all_total)
      !table_tactic 0. in
  msgnl(str"");
   msgnl(h 0(
      str"total time:           "++padl 11 (format_sec(all_total))
    )
	);
   msgnl(h 0(
      str"time spent in tactic: "++padl 11 (format_sec(tactic_total))
    )
       );
  msgnl(str"");
  header();
  print_table tactic_total "" true !table_tactic

let reset_profile() =
  stack := {entry=empty_entry; current_child=None; children=StringMap.empty}

let do_print_results_at_close () =
  if !should_display_profile_at_close
  then print_results ()
  else ()

let _ = Declaremods.append_end_library_hook do_print_results_at_close
