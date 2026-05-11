(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Production of Go syntax. *)

open Pp
open CErrors
open Util
open Names
open Table
open Miniml
open Mlutil
open Common

(*s Go keywords and built-in identifiers. *)

let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
  [ "break"; "case"; "chan"; "const"; "continue"; "default"; "defer";
    "else"; "fallthrough"; "for"; "func"; "go"; "goto"; "if"; "import";
    "interface"; "map"; "package"; "range"; "return"; "select"; "struct";
    "switch"; "type"; "var";
    (* predeclared identifiers *)
    "true"; "false"; "nil"; "iota";
    "append"; "cap"; "close"; "copy"; "delete"; "len"; "make"; "new";
    "panic"; "print"; "println"; "recover"; "real"; "imag"; "complex";
    (* types *)
    "bool"; "byte"; "int"; "int8"; "int16"; "int32"; "int64";
    "uint"; "uint8"; "uint16"; "uint32"; "uint64"; "uintptr";
    "float32"; "float64"; "complex64"; "complex128";
    "string"; "rune"; "error"; "any";
    (* extraction helpers *)
    "__"; "dummy__"; "magic__"; "init" ]
  Id.Set.empty

let pp_comment s = str "// " ++ s ++ fnl ()
let pp_block_comment s = str "/* " ++ hov 0 s ++ str " */"

(* Go identifiers cannot contain '\'' (prime/tick) which Coq uses
   for variable names like i', a', etc.  Replace them with a valid suffix. *)
let go_id_str id =
  String.map (fun c -> if c == '\'' then '0' else c) (Id.to_string id)

let go_id id = let s = go_id_str id in str s

(*s Pretty-printing of global references. *)

let pp_global table k r =
  if is_inline_custom r then str (find_custom r)
  else
    let name = Common.pp_global table k r in
    let name = match k, r.glob with
      | Cons, GlobRef.ConstructRef ((mind, i), _) ->
          let ind_ref = { r with glob = GlobRef.IndRef (mind, i) } in
          let ind_name = Common.pp_global_name table Type ind_ref in
          let cons_bare = Common.pp_global_name table Cons r in
          if String.equal cons_bare ind_name then
            (* Constructor would shadow its inductive type's Go name;
               disambiguate by prefixing with "Mk". *)
            (* The qualified [name] may have a package prefix like "pkg.Foo";
               insert "Mk" before the unqualified component. *)
            (try
               let dot = String.rindex name '.' in
               String.sub name 0 (dot + 1) ^ "Mk" ^
               String.sub name (dot + 1) (String.length name - dot - 1)
             with Not_found -> "Mk" ^ name)
          else name
      | _ -> name
    in
    str name

(* Arity table: maps global references to their number of Go parameters.
   Used to detect partial application and generate wrapper closures. *)
let arity_table : (GlobRef.t, int) Hashtbl.t = Hashtbl.create 97

let record_arity (r : GlobRef.t) def =
  let fl, _ = collect_lams def in
  Hashtbl.replace arity_table r (List.length fl)

let get_arity (r : Miniml.global) =
  Hashtbl.find_opt arity_table r.glob

(*s Pretty-printing of types. Go uses [any] for type variables and unknowns. *)

let rec pp_type table par = function
  | Tmeta _ | Tvar' _ -> assert false
  | Tvar _ -> str "any"
  | Tglob (r,[]) -> pp_global table Type r
  | Tglob (r,_) -> pp_global table Type r (* type args dropped -- no generics *)
  | Tarr (t1,t2) ->
      pp_par par
        (str "func(" ++ pp_type table false t1 ++ str ") " ++
         pp_type table false t2)
  | Tdummy _ -> str "any"
  | Tunknown -> str "any"
  | Taxiom -> str "any /* AXIOM TO BE REALIZED */"

(*s Pretty-printing of expressions. *)

(* Counter for generating unique variable names within a single pp_expr call chain *)
let var_counter = ref 0
let fresh_var () =
  let n = !var_counter in
  incr var_counter;
  "_v" ^ string_of_int n

(* Go-style function application: f(a1, a2, a3)
   All arguments are passed in a single call since top-level functions
   are emitted with all parameters. For complex heads (lambdas, etc.)
   we wrap in parens first: (expr)(a1, a2). *)
let go_apply head par args =
  match args with
  | [] -> head
  | _ ->
    let applied =
      head ++ str "(" ++
      prlist_with_sep (fun () -> str ", ") identity args ++
      str ")"
    in
    if par then str "(" ++ applied ++ str ")" else applied

let go_apply2 head par args =
  let head' = if not (List.is_empty args) || par
    then str "(" ++ head ++ str ")"
    else head
  in
  go_apply head' false args

let rec pp_expr table par env args =
  let apply st = go_apply st par args
  and apply2 st = go_apply2 st par args in
  function
    | MLrel n ->
        let id = get_db_name n env in
        let id = if Id.equal id dummy_name then Id.of_string "__" else id in
        if not (List.is_empty args) then
          (* Local variables have type [any]; function values stored in locals
             are curried (single-arg), so we chain single-arg type assertions. *)
          let head = List.fold_left (fun acc arg ->
            acc ++ str ".(func(any) any)(" ++ arg ++ str ")"
          ) (go_id id) args in
          if par then str "(" ++ head ++ str ")" else head
        else
          go_id id
    | MLapp (f,args') ->
        let stl = List.map (pp_expr table false env []) args' in
        pp_expr table par env (stl @ args) f
    | MLlam _ as a ->
        let fl,a' = collect_lams a in
        let fl,env' = push_vars (List.map id_of_mlid fl) env in
        let fl = List.rev fl in
        (* Emit curried (single-arg) lambdas so that local variable calls
           can use chained .(func(any) any) type assertions.
           Render each layer to a string to prevent Pp line breaks between
           [return] and the body (Go's automatic semicolon insertion). *)
        let body_str = Pp.string_of_ppcmds
          (pp_expr table false env' [] a') in
        let st = List.fold_right (fun id inner ->
          "func(" ^ go_id_str id ^ " any) any { return " ^ inner ^ " }"
        ) fl body_str in
        apply2 (str st)
    | MLletin _ as letchain ->
        (* Flatten chains of [let x := e in let y := e' in ...] into one
           IIFE with multiple [var] declarations, instead of nesting one
           IIFE per binding. The nested form (~30 closures deep in
           practice) drives Go's escape analysis past linear scaling
           and can OOM the compiler. *)
        let rec collect env acc = function
          | MLletin (id, a1, a2) ->
              let i, env' = push_vars [id_of_mlid id] env in
              let pp_id = go_id (List.hd i) in
              let pp_a1 = pp_expr table false env [] a1 in
              collect env' ((pp_id, pp_a1) :: acc) a2
          | body -> List.rev acc, env, body
        in
        let bindings, env', body = collect env [] letchain in
        let pp_body = pp_expr table false env' [] body in
        (* Go doesn't allow := in expression position, so wrap in IIFE.
           Declare with explicit [any] type so type switches work on the var. *)
        apply2
          (str "func() any {" ++ fnl () ++
           prlist (fun (id, a1) ->
             str "  " ++ hov 2 (str "var " ++ id ++ str " any = " ++ a1) ++ fnl ()
           ) bindings ++
           str "  " ++ hov 2 (str "return " ++ pp_body) ++ fnl () ++
           str "}()")
    | MLglob r ->
        let supplied = List.length args in
        (match get_arity r with
         | Some arity when supplied < arity && arity > 0 ->
             (* Partial application or function-as-value: wrap remaining args
                in curried closures for chained .(func(any) any) calls. *)
             let remaining = arity - supplied in
             let extra_ids = List.init remaining
               (fun i -> "_pa" ^ string_of_int i) in
             let extra_args = List.map str extra_ids in
             let all_args = args @ extra_args in
             let full_call_str = Pp.string_of_ppcmds (
               pp_global table Term r ++ str "(" ++
               prlist_with_sep (fun () -> str ", ") identity all_args ++
               str ")") in
             (* Build curried closures from inside out *)
             let curried = List.fold_right (fun id inner ->
               "func(" ^ id ^ " any) any { return " ^ inner ^ " }"
             ) extra_ids full_call_str in
             let result = str curried in
             if par then str "(" ++ result ++ str ")" else result
         | Some arity when supplied > arity ->
             (* More args than parameters: pass [arity] args directly,
                chain the rest as type assertions (the function returns
                curried closures typed as [any]). *)
             let direct_args = List.firstn arity args in
             let extra_args = List.skipn arity args in
             let head =
               if arity = 0 then
                 (* Zero-arg function: must call it to get the [any] value *)
                 pp_global table Term r ++ str "()"
               else
                 go_apply (pp_global table Term r) false direct_args
             in
             let result = List.fold_left (fun acc arg ->
               acc ++ str ".(func(any) any)(" ++ arg ++ str ")"
             ) head extra_args in
             if par then str "(" ++ result ++ str ")" else result
         | Some 0 ->
             (* Zero-arg function referenced as a value (supplied = 0):
                emit the call to obtain the [any] value rather than the
                bare function pointer. *)
             let head = pp_global table Term r ++ str "()" in
             if par then str "(" ++ head ++ str ")" else head
         | _ ->
             apply (pp_global table Term r))
    | MLcons (_,r,a) as c ->
        assert (List.is_empty args);
        begin match a with
          | _ when is_native_char c -> pp_native_char c
          | _ when is_native_string c -> pp_native_string c
          | [] -> pp_global table Cons r ++ str "{}"
          | _ ->
            let fields = List.mapi (fun i e ->
              str ("Field" ^ string_of_int i ^ ": ") ++
              pp_expr table false env [] e
            ) a in
            pp_global table Cons r ++ str "{" ++
            prlist_with_sep (fun () -> str ", ") identity fields ++
            str "}"
        end
    | MLtuple l ->
        assert (List.is_empty args);
        let n = List.length l in
        let fields = List.mapi (fun i _ ->
          str ("F" ^ string_of_int i ^ " any")
        ) l in
        let values = List.mapi (fun i e ->
          str ("F" ^ string_of_int i ^ ": ") ++
          pp_expr table false env [] e
        ) l in
        str "struct{" ++
        prlist_with_sep (fun () -> str "; ") identity fields ++
        str "}{" ++
        prlist_with_sep (fun () -> str ", ") identity values ++
        (if n > 0 then str "," else mt ()) ++
        str "}"
    | MLcase (_,t, pv) when is_custom_match pv ->
        if not (is_regular_match pv) then
          user_err Pp.(str "Cannot mix yet user-given match and general patterns.");
        let mkfun (ids,_,e) =
          if not (List.is_empty ids) then named_lams (List.rev ids) e
          else dummy_lams (ast_lift 1 e) 1
        in
        let pp_branch tr = pp_expr table true env [] (mkfun tr) ++ fnl () in
        let inner =
          str (find_custom_match pv) ++ fnl () ++
          prvect pp_branch pv ++
          pp_expr table true env [] t
        in
        apply2 (hov 2 inner)
    | MLcase (typ,t,pv) ->
        let needs_var = Array.exists (fun (ids,_,_) -> not (List.is_empty ids)) pv in
        let v_name = if needs_var then fresh_var () else "_" in
        let switch_head =
          if needs_var then
            str ("  switch " ^ v_name ^ " := ") ++
            pp_expr table false env [] t ++
            str ".(type) {"
          else
            str "  switch " ++
            pp_expr table false env [] t ++
            str ".(type) {"
        in
        apply2
          (v 0 (str "func() any {" ++ fnl () ++
                switch_head ++ fnl () ++
                pp_pat table env v_name pv ++
                str "  }" ++ fnl () ++
                str "  return nil" ++ fnl () ++
                str "}()"))
    | MLfix (i,ids,defs) ->
        let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
        pp_fix table par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
        apply (str "panic(" ++ qs s ++ str ")")
    | MLdummy k ->
        (match msg_of_implicit k with
         | "" -> str "dummy__"
         | s -> str "dummy__" ++ spc () ++ pp_block_comment (str s))
    | MLmagic a ->
        if List.is_empty args then
          go_apply (str "magic__") par [pp_expr table false env [] a]
        else
          (* magic__(a) returns any; chain single-arg type assertions *)
          let head = str "magic__(" ++ pp_expr table false env [] a ++ str ")" in
          let result = List.fold_left (fun acc arg ->
            acc ++ str ".(func(any) any)(" ++ arg ++ str ")"
          ) head args in
          if par then str "(" ++ result ++ str ")" else result
    | MLaxiom s ->
        apply (str "func() any { panic(\"AXIOM TO BE REALIZED: " ++ str s ++ str "\") }()")
    | MLuint i ->
        apply (str "uint64(" ++ str (Uint63.to_string i) ++ str ")")
    | MLfloat f ->
        apply (str "float64(" ++ str (Float64.to_string f) ++ str ")")
    | MLstring s ->
        apply (qs (Pstring.to_string s))
    | MLparray _ ->
        apply (str "panic(\"EXTRACTION OF ARRAY NOT IMPLEMENTED\")")

and pp_pat table env v_name pv =
  prvecti
    (fun i (ids,p,t) ->
       let ids',env' = push_vars (List.rev_map id_of_mlid ids) env in
       pp_one_pat table env' v_name (List.rev ids') p t ++
       fnl ())
    pv

and pp_field_binding id field_expr =
  let id_str = go_id_str id in
  if String.equal id_str "_" then
    str "    _ = " ++ field_expr ++ fnl ()
  else
    str "    " ++ go_id id ++ str " := " ++ field_expr ++ fnl ()

and pp_one_pat table env v_name ids p t =
  match p with
  | Pusual r ->
      let fields = List.mapi (fun i id ->
        pp_field_binding id (str (v_name ^ ".Field" ^ string_of_int i))
      ) ids in
      str "  case " ++ pp_global table Cons r ++ str ":" ++ fnl () ++
      prlist identity fields ++
      str "    return " ++ pp_expr table false env [] t
  | Pcons (r,pats) ->
      str "  case " ++ pp_global table Cons r ++ str ":" ++ fnl () ++
      pp_bind_pattern_fields table env v_name ids pats 0 ++
      str "    return " ++ pp_expr table false env [] t
  | Ptuple pats ->
      (* Tuple patterns -- bind fields from anonymous struct *)
      let bindings = List.mapi (fun i _ ->
        match List.nth_opt ids i with
        | Some id ->
          str "    " ++ go_id id ++
          str (" := " ^ v_name ^ ".F" ^ string_of_int i) ++ fnl ()
        | None -> mt ()
      ) pats in
      str "  default:" ++ fnl () ++
      prlist identity bindings ++
      str "    return " ++ pp_expr table false env [] t
  | Pwild ->
      str "  default:" ++ fnl () ++
      str "    return " ++ pp_expr table false env [] t
  | Prel n ->
      str "  default:" ++ fnl () ++
      str "    " ++ go_id (get_db_name n env) ++ str (" := " ^ v_name) ++ fnl () ++
      str "    return " ++ pp_expr table false env [] t

and pp_bind_pattern_fields _table _env v_name ids _pats _start_idx =
  prlist_with_sep (fun () -> mt ()) (fun (i, id) ->
    pp_field_binding id (str (v_name ^ ".Field" ^ string_of_int i))
  ) (List.mapi (fun i id -> (i, id)) ids)

(*s Fixpoint expressions *)

and pp_fix table par env i (ids,bl) args =
  pp_par par
    (v 0
       (str "func() any {" ++ fnl () ++
        (* First pass: declare variables as [any] so they can be called
           via chained .(func(any) any) type assertions *)
        prvecti (fun _j _def ->
          str "  var " ++ go_id ids.(_j) ++ str " any" ++ fnl ()
        ) bl ++
        (* Second pass: assign curried function bodies *)
        prvecti (fun j def ->
          let fl,t' = collect_lams def in
          let fl,env' = push_vars (List.map id_of_mlid fl) env in
          let fl = List.rev fl in
          let body_str = Pp.string_of_ppcmds
            (pp_expr table false env' [] t') in
          let curried = List.fold_right (fun id inner ->
            "func(" ^ go_id_str id ^ " any) any { return " ^ inner ^ " }"
          ) fl body_str in
          str "  " ++ go_id ids.(j) ++ str (" = " ^ curried) ++ fnl ()
        ) bl ++
        (* Call the i-th fixpoint function with chained type assertions *)
        (let head = List.fold_left (fun acc arg ->
           acc ^ ".(func(any) any)(" ^
           Pp.string_of_ppcmds arg ^ ")"
         ) (go_id_str ids.(i)) args in
         str ("  return " ^ head) ++ fnl ()) ++
        str "}()"))

(*s Pretty-printing of inductive types *)

let pp_logical_ind packet =
  pp_block_comment
    (Id.print packet.ip_typename ++ str " : logical inductive" ++ fnl () ++
     str "with constructors : " ++ prvect_with_sep spc Id.print packet.ip_consnames)

(* Standard sum type: interface + structs *)
let pp_standard_ind table p cv =
  let tname = pp_global table Type p.ip_typename_ref in
  let marker =
    let base = Common.pp_global_name table Type p.ip_typename_ref in
    if State.get_modular table then "Is" ^ base
    else "is" ^ base
  in
  (* Interface type *)
  str "type " ++ tname ++ str " interface{ " ++ str marker ++ str "() }" ++ fnl () ++
  (* One struct per constructor *)
  prvecti (fun i c ->
    let cname = pp_global table Cons p.ip_consnames_ref.(i) in
    let fields = List.mapi (fun j _ ->
      str ("Field" ^ string_of_int j) ++ str " any"
    ) c in
    str "type " ++ cname ++ str " struct{" ++
    (if List.is_empty fields then mt ()
     else str " " ++ prlist_with_sep (fun () -> str "; ") identity fields ++ str " ") ++
    str "}" ++ fnl () ++
    str "func (" ++ cname ++ str ") " ++ str marker ++ str "() {}" ++ fnl ()
  ) cv

let pp_record_ind table _fields p =
  let tname = pp_global table Type p.ip_typename_ref in
  let cname = pp_global table Cons p.ip_consnames_ref.(0) in
  let marker =
    let base = Common.pp_global_name table Type p.ip_typename_ref in
    if State.get_modular table then "Is" ^ base
    else "is" ^ base
  in
  (* Interface so the record can be used in type switches *)
  str "type " ++ tname ++ str " interface{ " ++ str marker ++ str "() }" ++ fnl () ++
  (match p.ip_types.(0) with
  | [] ->
    str "type " ++ cname ++ str " struct{}" ++ fnl () ++
    str "func (" ++ cname ++ str ") " ++ str marker ++ str "() {}" ++ fnl ()
  | types ->
    let fields = List.mapi (fun i _ ->
      str ("  Field" ^ string_of_int i) ++ str " any"
    ) types in
    str "type " ++ cname ++ str " struct {" ++ fnl () ++
    prlist_with_sep (fun () -> fnl ()) identity fields ++ fnl () ++
    str "}" ++ fnl () ++
    str "func (" ++ cname ++ str ") " ++ str marker ++ str "() {}" ++ fnl ())

let pp_singleton table packet =
  let name = pp_global table Type packet.ip_typename_ref in
  hov 2 (str "type " ++ name ++ str " = " ++
         pp_type table false (List.hd packet.ip_types.(0))) ++ fnl () ++
  pp_comment (str "singleton inductive, whose constructor was " ++
              Id.print packet.ip_consnames.(0))

let pp_coinductive table p =
  let tname = pp_global table Type p.ip_typename_ref in
  (* Thunk-wrapping struct *)
  str "type " ++ tname ++ str " struct{ Force func() " ++ tname ++ str "_body }" ++ fnl () ++
  (* Body struct with fields from first constructor *)
  (if Array.length p.ip_types = 0 then mt ()
   else
     let fields = List.mapi (fun i _ ->
       str ("  Field" ^ string_of_int i) ++ str " any"
     ) p.ip_types.(0) in
     str "type " ++ tname ++ str "_body struct {" ++ fnl () ++
     prlist_with_sep (fun () -> fnl ()) identity fields ++ fnl () ++
     str "}" ++ fnl ())

let rec pp_ind table first i ind =
  if i >= Array.length ind.ind_packets then
    if first then mt () else fnl ()
  else
    let p = ind.ind_packets.(i) in
    let ip = p.ip_typename_ref in
    if is_custom ip then pp_ind table first (i+1) ind
    else
      if p.ip_logical then
        pp_logical_ind p ++ fnl () ++ pp_ind table first (i+1) ind
      else begin
        (match ind.ind_kind with
         | Singleton -> pp_singleton table p
         | Record fields -> pp_record_ind table fields p
         | Coinductive -> pp_coinductive table p
         | Standard -> pp_standard_ind table p p.ip_types) ++
        fnl () ++
        pp_ind table false (i+1) ind
      end

(*s Pretty-printing of declarations. *)

let rec pp_decl table d =
  var_counter := 0;
  match d with
  | Dind i when i.ind_kind == Singleton ->
      pp_singleton table i.ind_packets.(0) ++ fnl ()
  | Dind i -> hov 0 (pp_ind table true 0 i)
  | Dtype (r, l, t) ->
      if is_inline_custom r then mt ()
      else
        let st =
          try
            let _ids,s = find_type_custom r in
            str "= " ++ str s
          with Not_found ->
            if t == Taxiom then str "= any /* AXIOM TO BE REALIZED */" ++ fnl ()
            else str "= " ++ pp_type table false t
        in
        hov 2 (str "type " ++ pp_global table Type r ++ str " " ++ st) ++ fnl2 ()
  | Dfix (rv, defs, typs) ->
      let names = Array.map
        (fun r -> if is_inline_custom r then mt () else pp_global table Term r) rv
      in
      (* Record arities for partial application detection *)
      Array.iteri (fun i r ->
        if not (is_inline_custom r) then record_arity r.glob defs.(i)
      ) rv;
      (* Check if mutual recursion (more than one non-void binding) *)
      let non_void = Array.to_list (Array.mapi (fun i r ->
        let void = is_inline_custom r ||
          (not (is_custom r) &&
           match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
        in
        not void
      ) rv) in
      let n_real = List.length (List.filter (fun x -> x) non_void) in
      if n_real > 1 then
        (* Mutual recursion: use var block + init *)
        str "var (" ++ fnl () ++
        prvecti (fun i r ->
          let void = is_inline_custom r ||
            (not (is_custom r) &&
             match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
          in
          if void then mt ()
          else
            let fl, _ = collect_lams defs.(i) in
            let nparams = List.length fl in
            let any_params = String.concat ", "
              (List.init nparams (fun _ -> "any")) in
            str "  " ++ names.(i) ++
            str (" func(" ^ any_params ^ ") any") ++ fnl ()
        ) rv ++
        str ")" ++ fnl2 () ++
        str "func init() {" ++ fnl () ++
        prvecti (fun i r ->
          let void = is_inline_custom r ||
            (not (is_custom r) &&
             match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
          in
          if void then mt ()
          else if is_custom r then
            str "  " ++ names.(i) ++ str " = " ++ str (find_custom r) ++ fnl ()
          else
            let fl,t' = collect_lams defs.(i) in
            let fl,env' = push_vars (List.map id_of_mlid fl) (empty_env table ()) in
            let pp_params =
              prlist_with_sep (fun () -> str ", ")
                (fun id -> go_id id ++ str " any") (List.rev fl)
            in
            str "  " ++ names.(i) ++ str " = func(" ++ pp_params ++ str ") any {" ++ fnl () ++
            str "    return " ++ pp_expr table false env' [] t' ++ fnl () ++
            str "  }" ++ fnl ()
        ) rv ++
        str "}" ++ fnl2 ()
      else
        (* Single or no bindings: emit as top-level func *)
        prvecti
          (fun i r ->
            let void = is_inline_custom r ||
              (not (is_custom r) &&
               match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
            in
            if void then mt ()
            else if is_custom r then
              hov 0 (str "var " ++ names.(i) ++ str " = " ++ str (find_custom r)) ++ fnl2 ()
            else
              pp_function table names.(i) defs.(i) ++ fnl2 ())
          rv
  | Dterm (r, a, t) ->
      if is_inline_custom r then mt ()
      else begin
        record_arity r.glob a;
        let e = pp_global table Term r in
        if is_custom r then
          hov 0 (str "var " ++ e ++ str " = " ++ str (find_custom r) ++ fnl2 ())
        else
          pp_function table e a ++ fnl2 ()
      end

and pp_function table name def =
  let fl,t' = collect_lams def in
  let fl,env' = push_vars (List.map id_of_mlid fl) (empty_env table ()) in
  let pp_params =
    prlist_with_sep (fun () -> str ", ")
      (fun id -> go_id id ++ str " any") (List.rev fl)
  in
  let body = match t' with
    | MLaxiom s ->
        str "  panic(\"AXIOM TO BE REALIZED: " ++ str s ++ str "\")"
    | _ ->
        str "  return " ++ hov 2 (pp_expr table false env' [] t')
  in
  str "func " ++ name ++ str "(" ++ pp_params ++ str ") any {" ++ fnl () ++
  body ++ fnl () ++
  str "}"

(*s Module structure *)

let rec pp_structure_elem table = function
  | (l,SEdecl d) -> pp_decl table d
  | (l,SEmodule m) -> pp_module_expr table m.ml_mod_expr
  | (l,SEmodtype m) -> mt ()
      (* module types are dropped *)

and pp_module_expr table = function
  | MEstruct (mp,sel) -> prlist_strict (fun e -> pp_structure_elem table e) sel
  | MEfunctor _ ->
      pp_comment (str "functor omitted") (* Go has no functors *)
  | MEident _ | MEapply _ -> assert false

let pp_struct table =
  let pp_sel (mp,sel) = State.with_visibility table mp [] begin fun table ->
    prlist_strict (fun e -> pp_structure_elem table e) sel
  end in
  prlist_strict pp_sel

(*s Preamble *)

let preamble table mod_name comment used_modules usf =
  let modular = State.get_modular table in
  let pkg_name =
    if modular then
      go_safe_pkg_name (Id.to_string mod_name)
    else
      Id.to_string mod_name
  in
  (match comment with
    | None -> mt ()
    | Some com -> pp_block_comment com ++ fnl2 ())
  ++
  str "package " ++ str pkg_name ++ fnl2 ()
  ++
  (* Import block for cross-package imports *)
  (let pkg_imports =
     if modular && not (DirPath.Set.is_empty used_modules) then
       let prefix = go_module_prefix () in
       List.map (fun dp ->
         let pkg = go_safe_pkg_name
           (string_of_modfile (State.get_table table) dp) in
         "  \"" ^ prefix ^ "/" ^ pkg ^ "\""
       ) (DirPath.Set.elements used_modules)
     else []
   in
   if pkg_imports <> [] then
     str "import (" ++ fnl () ++
     prlist (fun s -> str s ++ fnl ()) pkg_imports ++
     str ")" ++ fnl2 ()
   else mt ())
  ++
  (if usf.mldummy then
     str "var dummy__ any = nil" ++ fnl2 ()
   else mt ())
  ++
  (if usf.magic then
     str "func magic__(x any) any {" ++ fnl () ++
     str "  return x" ++ fnl () ++
     str "}" ++ fnl2 ()
   else mt ())

let file_naming state mp =
  let base = file_of_modfile (State.get_table state) mp in
  if State.get_modular state then
    let pkg = go_safe_pkg_name base in
    Filename.concat pkg pkg  (* → "nat_utils/nat_utils" → "nat_utils/nat_utils.go" *)
  else
    base

(*s go.mod generation for modular extraction *)

let write_go_mod dir module_prefix =
  let path = Filename.concat dir "go.mod" in
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
    Printf.fprintf oc "module %s\n\ngo 1.21\n" module_prefix)

(*s The [go_descr] record. *)

let go_descr = {
  keywords = keywords;
  file_suffix = ".go";
  file_naming = file_naming;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ _ _ -> mt ());
  pp_sig = (fun _ _ -> mt ());
  pp_decl = pp_decl;
}
