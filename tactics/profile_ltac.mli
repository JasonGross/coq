val do_profile : string -> ('a * 'b * Proof_type.ltac_call_kind) list -> (unit -> 'c) -> 'c

val set_profiling : bool -> unit

val get_profiling : unit -> bool

val set_display_profile_at_close : bool -> unit

val entered_call : unit -> unit

val print_results : unit -> unit

val print_results_tactic : string -> unit

val reset_profile : unit -> unit

val do_print_results_at_close : unit -> unit
