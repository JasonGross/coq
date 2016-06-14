(*i camlp4deps: "parsing/grammar.cma" i*)

open Profile_ltac

let tclSET_PROFILING b = fun gl ->
   set_profiling b; Tacticals.tclIDTAC gl

TACTIC EXTEND start_profiling
  | [ "start" "ltac" "profiling" ] -> [ tclSET_PROFILING true  ]
END

TACTIC EXTEND stop_profiling
  | [ "stop" "ltac" "profiling" ] ->  [ tclSET_PROFILING false ]
END;;

let _ =
  Goptions.declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "Ltac Profiling";
      optkey   = ["Ltac"; "Profiling"];
      optread  = get_profiling;
      optwrite = set_profiling }

VERNAC COMMAND EXTEND ResetLtacProfiling
 [ "Reset" "Ltac" "Profile" ] -> [ reset_profile() ]
END

VERNAC COMMAND EXTEND ShowLtacProfile
 [ "Show" "Ltac" "Profile" ] -> [ print_results() ]
END


VERNAC COMMAND EXTEND ShowLtacProfileTactic
 [ "Show" "Ltac" "Profile" string(s) ] -> [ print_results_tactic s ]
END
