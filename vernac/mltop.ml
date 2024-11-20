(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp

(* Code to interact with ML "toplevel", in particular, handling ML
   plugin loading.

   We use Fl_dynload to load plugins, which can correctly track
   dependencies, and manage path for us.

   A bit of infrastructure is still in place to support a "legacy"
   mode where Coq used to manage the OCaml include paths and directly
   load .cmxs/.cma files itself.

   We also place here the required code for interacting with the
   Summary and Libobject, and provide an API so plugins can interact
   with this loading/unloading for Coq-specific purposes adding their
   own init functions, given that OCaml cannot unlink a dynamic module.

*)


module Fl_internals = struct

  (* Fl_split.in_words is not exported *)
  let fl_split_in_words s =
    (* splits s in words separated by commas and/or whitespace *)
    let l = String.length s in
    let rec split i j =
      if j < l then
        match s.[j] with
        | (' '|'\t'|'\n'|'\r'|',') ->
          if i<j then (String.sub s i (j-i)) :: (split (j+1) (j+1))
          else split (j+1) (j+1)
        |	_ ->
          split i (j+1)
      else
      if i<j then [ String.sub s i (j-i) ] else []
    in
    split 0 0

  (* simulate what fl_dynload does *)
  let fl_find_plugins lib =
    let base = Findlib.package_directory lib in
    let preds = Findlib.recorded_predicates () in
    let archive = try Findlib.package_property preds lib "plugin"
      with Not_found ->
      try fst (Findlib.package_property_2 ("plugin"::preds) lib "archive")
      with Not_found -> ""
    in
    fl_split_in_words archive |> List.map (Findlib.resolve_path ~base)

  (* We register errors at for Dynlink and Findlib, it is possible to
     do so Symtable too, as we used to do in the bytecode init code.
     *)
  let () = CErrors.register_handler (function
      | Dynlink.Error msg ->
        Some (hov 0 (str "Dynlink error: " ++ str (Dynlink.error_message msg)))
      | Fl_package_base.No_such_package(p,msg) ->
        let paths = Findlib.search_path () in
        Some (hov 0 (str "Findlib error: " ++ str p ++
                     str " not found in:" ++ cut () ++ v 0 (prlist_with_sep cut str paths) ++ fnl() ++ str msg))
      | _ ->
        None
    )

end

module PluginSpec : sig

  type t

  (* Main constructor, takes the format used in Declare ML Module.
     With [usercode:true], warn instead of error on legacy syntax. *)
  val of_package : ?usercode:bool -> string -> t

  val to_package : t -> string

  (* Load a plugin, low-level, that is to say, will directly call the
     loading mechanism in OCaml/findlib *)
  val load : t -> unit

  (* Compute a digest, a findlib library name have more than one
     plugin .cmxs, however this is not the case in Coq. Maybe we
     should strengthen this invariant. *)
  val digest : t -> Digest.t list

  val pp : t -> string

  module Set : CSet.ExtS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

end = struct

  type t = { lib : string }

  module Errors = struct

    let warn_legacy_loading =
      let name = "legacy-loading-removed" in
      CWarnings.create ~name (fun name ->
          Pp.(str "Legacy loading plugin method has been removed from Coq, \
                   and the `:` syntax is deprecated, and its first \
                   argument ignored; please remove \"" ++
              str name ++ str ":\" from your Declare ML"))

    let plugin_name_invalid_format m =
      CErrors.user_err
        Pp.(str Format.(asprintf "%s is not a valid plugin name." m) ++ spc () ++
            str "It should be a public findlib name, e.g. package-name.foo." ++ spc () ++
            str "Legacy names followed by a findlib public name, e.g. "++ spc () ++
            str "legacy_plugin:package-name.plugin," ++ spc() ++
            str "are not supported anymore.")

  end

  let of_package ?(usercode=false) m =
    match String.split_on_char ':' m with
    | [ lib ] ->
      { lib }
    | [cmxs; lib] when usercode ->
      Errors.warn_legacy_loading cmxs;
      { lib }
    | _ -> Errors.plugin_name_invalid_format m

  let to_package { lib } = lib

  let load = function
    | { lib } ->
      Fl_dynload.load_packages [lib]

  let digest s =
    match s with
    | { lib } ->
      let plugins = Fl_internals.fl_find_plugins lib in
      List.map Digest.file plugins

  let compare { lib = l1 } { lib = l2 } = String.compare l1 l2

  let pp = function
    | { lib } -> lib

  module Self = struct
      type nonrec t = t
      let compare = compare
    end

  module Set = CSet.Make(Self)
  module Map = CMap.Make(Self)

end

(* If there is a toplevel under Coq *)
type toplevel =
  { load_plugin : PluginSpec.t -> unit
  (** Load a findlib library, given by public name *)
  ; load_module : string -> unit
  (** Load a cmxs / cmo module, used by the native compiler to load objects *)
  ; add_dir  : string -> unit
  (** Adds a dir to the module search path *)
  ; ml_loop  : ?init_file:string -> unit -> unit
  (** Run the OCaml toplevel with given initialisation file *)
  }

(* Determines the behaviour of Coq with respect to ML files (compiled
   or not) *)
type kind_load =
  | WithTop of toplevel
  | WithoutTop

(* Must be always initialized *)
let load = ref WithoutTop

(* Sets and initializes a toplevel (if any) *)
let set_top toplevel = load :=
  WithTop toplevel;
  Nativelib.load_obj := toplevel.load_module

(* Removes the toplevel (if any) *)
let remove () =
  load := WithoutTop;
  Nativelib.load_obj := (fun x -> () : string -> unit)

(* Tests if an Ocaml toplevel runs under Coq *)
let is_ocaml_top () =
  match !load with
    | WithTop _ -> true
    |_ -> false

(* Tests if we can load ML files *)
let has_dynlink = Coq_config.has_natdynlink || not Sys.(backend_type = Native)

(* Runs the toplevel loop of Ocaml *)
let ocaml_toploop ?init_file () =
  match !load with
    | WithTop t -> t.ml_loop ?init_file ()
    | _ -> ()

let ml_load p =
  match !load with
  | WithTop t -> t.load_plugin p
  | WithoutTop ->
    PluginSpec.load p

let load_module x = match !load with
  | WithTop t -> t.load_module x
  | WithoutTop -> ()

(* Adds a path to the ML paths *)
let add_ml_dir s =
  match !load with
    | WithTop t -> t.add_dir s
    | WithoutTop when has_dynlink -> ()
    | _ -> ()

(** Is the ML code of the standard library placed into loadable plugins
    or statically compiled into coqtop ? For the moment this choice is
    made according to the presence of native dynlink : even if bytecode
    coqtop could always load plugins, we prefer to have uniformity between
    bytecode and native versions. *)

(* [known_loaded_module] contains the names of the loaded ML modules
 * (linked or loaded with load_object). It is used not to load a
 * module twice. It is NOT the list of ML modules Coq knows. *)

(* TODO: Merge known_loaded_module and known_loaded_plugins *)
let known_loaded_modules : PluginSpec.Set.t ref = ref PluginSpec.Set.empty

let add_known_module mname =
  if not (PluginSpec.Set.mem mname !known_loaded_modules) then
    known_loaded_modules := PluginSpec.Set.add mname !known_loaded_modules

let module_is_known mname = PluginSpec.Set.mem mname !known_loaded_modules
let plugin_is_known mname = PluginSpec.Set.mem mname !known_loaded_modules

(** Init time functions *)

let initialized_plugins = Summary.ref ~stage:Synterp ~name:"inited-plugins" PluginSpec.Set.empty

let plugin_init_functions : (unit -> unit) list PluginSpec.Map.t ref = ref PluginSpec.Map.empty

let add_init_function name f =
  let name = PluginSpec.of_package name in
  if PluginSpec.Set.mem name !initialized_plugins
  then CErrors.anomaly Pp.(str "Not allowed to add init function for already initialized plugin " ++ str (PluginSpec.pp name));
  plugin_init_functions := PluginSpec.Map.update name (function
      | None -> Some [f]
      | Some g -> Some (f::g))
      !plugin_init_functions

(** Registering functions to be used at caching time, that is when the Declare
    ML module command is issued. *)

let cache_objs = ref PluginSpec.Map.empty

let declare_cache_obj f name =
  let name = PluginSpec.of_package name in
  let objs = try PluginSpec.Map.find name !cache_objs with Not_found -> [] in
  let objs = f :: objs in
  cache_objs := PluginSpec.Map.add name objs !cache_objs

let perform_cache_obj name =
  let objs = try PluginSpec.Map.find name !cache_objs with Not_found -> [] in
  let objs = List.rev objs in
  List.iter (fun f -> f ()) objs

(** ml object = ml module or plugin *)
let dinit = CDebug.create ~name:"mltop-init" ()

let init_ml_object mname =
  if PluginSpec.Set.mem mname !initialized_plugins
  then dinit Pp.(fun () -> str "already initialized " ++ str (PluginSpec.pp mname))
  else  begin
    dinit Pp.(fun () -> str "initing " ++ str (PluginSpec.pp mname));
    let n = match PluginSpec.Map.find mname !plugin_init_functions with
      | l -> List.iter (fun f -> f()) (List.rev l); List.length l
      | exception Not_found -> 0
    in
    initialized_plugins := PluginSpec.Set.add mname !initialized_plugins;
    dinit Pp.(fun () -> str "finished initing " ++ str (PluginSpec.pp mname) ++ str " (" ++ int n ++ str " init functions)")
  end

let load_ml_object mname =
  ml_load mname;
  add_known_module mname

let add_known_module name =
  let name = PluginSpec.of_package name in
  add_known_module name

let module_is_known mname =
  let mname = PluginSpec.of_package mname in
  module_is_known mname

(* Summary of declared ML Modules *)

(* List and not String.Set because order is important: most recent first. *)

let loaded_modules = ref []

let get_loaded_modules () = List.rev !loaded_modules

(* XXX: It seems this should be part of trigger_ml_object, and
   moreover we should check the guard there *)
let add_loaded_module md =
  if not (List.mem md !loaded_modules) then
    loaded_modules := md :: !loaded_modules

let reset_loaded_modules () = loaded_modules := []

let if_verbose_load verb f name =
  if not verb then f name
  else
    let info = str "[Loading ML file " ++ str (PluginSpec.pp name) ++ str " ..." in
    try
      let path = f name in
      Feedback.msg_info (info ++ str " done]");
      path
    with reraise ->
      Feedback.msg_info (info ++ str " failed]");
      raise reraise

(** Load a module for the first time (i.e. dynlink it) *)

let trigger_ml_object ~verbose plugin =
  let () =
    if not @@ plugin_is_known plugin then begin
      if not has_dynlink then
        CErrors.user_err
          (str "Dynamic link not supported (module " ++ str (PluginSpec.pp plugin) ++ str ").")
      else
        if_verbose_load (verbose && not !Flags.quiet) load_ml_object plugin
    end
  in
  add_loaded_module plugin

let unfreeze_ml_modules x =
  reset_loaded_modules ();
  List.iter
    (fun name ->
       let name = PluginSpec.of_package name in
       trigger_ml_object ~verbose:false name) x

let () =
  Summary.declare_ml_modules_summary
    { stage = Summary.Stage.Synterp
    ; Summary.freeze_function = (fun () ->
          get_loaded_modules () |> List.map PluginSpec.to_package)
    ; Summary.unfreeze_function = unfreeze_ml_modules
    ; Summary.init_function = reset_loaded_modules }

(* Liboject entries of declared ML Modules *)
type ml_module_object =
  { mlocal : Vernacexpr.locality_flag
  ; mnames : PluginSpec.t list
  ; mdigests : Digest.t list
  }

let cache_ml_objects mnames =
  let iter obj =
    trigger_ml_object ~verbose:true obj;
    init_ml_object obj;
    perform_cache_obj obj
  in
  List.iter iter mnames

let load_ml_objects _ {mnames; _} =
  let iter obj =
    trigger_ml_object ~verbose:true obj;
    init_ml_object obj
  in
  List.iter iter mnames

let classify_ml_objects {mlocal=mlocal} =
  if mlocal then Libobject.Dispose else Libobject.Substitute

let inMLModule : ml_module_object -> Libobject.obj =
  let open Libobject in
  declare_object
    {(default_object "ML-MODULE") with
      object_stage = Summary.Stage.Synterp;
      cache_function = (fun _ -> ());
      load_function = load_ml_objects;
      subst_function = (fun (_,o) -> o);
      classify_function = classify_ml_objects }

let declare_ml_modules local mnames =
  let mnames = List.map (PluginSpec.of_package ~usercode:true) mnames in
  if Lib.sections_are_opened()
  then CErrors.user_err Pp.(str "Cannot Declare ML Module while sections are opened.");
  (* List.concat_map only available in 4.10 *)
  let mdigests = List.map PluginSpec.digest mnames |> List.concat in
  Lib.add_leaf (inMLModule {mlocal=local; mnames; mdigests});
  (* We can't put this in cache_function: it may declare other
     objects, and when the current module is required we want to run
     the ML-MODULE object before them. *)
  cache_ml_objects mnames

(* Printing of loaded ML modules *)

let print_ml_modules () =
  let l = get_loaded_modules () in
  str"Loaded ML Modules: " ++ pr_vertical_list str (List.map PluginSpec.pp l)

let print_gc () =
  let stat = Gc.stat () in
  let msg =
    str "minor words: " ++ real stat.Gc.minor_words ++ fnl () ++
    str "promoted words: " ++ real stat.Gc.promoted_words ++ fnl () ++
    str "major words: " ++ real stat.Gc.major_words ++ fnl () ++
    str "minor_collections: " ++ int stat.Gc.minor_collections ++ fnl () ++
    str "major_collections: " ++ int stat.Gc.major_collections ++ fnl () ++
    str "heap_words: " ++ int stat.Gc.heap_words ++ fnl () ++
    str "heap_chunks: " ++ int stat.Gc.heap_chunks ++ fnl () ++
    str "live_words: " ++ int stat.Gc.live_words ++ fnl () ++
    str "live_blocks: " ++ int stat.Gc.live_blocks ++ fnl () ++
    str "free_words: " ++ int stat.Gc.free_words ++ fnl () ++
    str "free_blocks: " ++ int stat.Gc.free_blocks ++ fnl () ++
    str "largest_free: " ++ int stat.Gc.largest_free ++ fnl () ++
    str "fragments: " ++ int stat.Gc.fragments ++ fnl () ++
    str "compactions: " ++ int stat.Gc.compactions ++ fnl () ++
    str "top_heap_words: " ++ int stat.Gc.top_heap_words ++ fnl () ++
    str "stack_size: " ++ int stat.Gc.stack_size
  in
  hv 0 msg
