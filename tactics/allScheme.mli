open Names
open Declarations
open EConstr
open LibBinding

  (** {6 Lookup All Predicate and its Theorem } *)

(** Lookup the partial [all] predicate and its theorem for [ind_nested] for [args_are_nested].
    If they are not found, lookup the general [all] predicate and its theorem.
    Returns if the partial [all] was found, and the global references.
    Raise a warning if none is found. *)
val lookup_all_theorem : inductive -> inductive -> bool list -> (bool * GlobRef.t * GlobRef.t) option

  (** {6 Instantiate the All Predicate and its Theorem } *)

(** Make the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate [constr option array], using [fun ... => True]
      if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
val make_all_predicate : partial_nesting:bool -> GlobRef.t -> bool list -> constr array ->
  constr option array -> constr array -> constr -> constr State.t

(** Make the theorem for the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate and the proofs they hold [constr option array],
      using [fun ... => True] and [fun _ => I] if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
val make_all_theorem : partial_nesting:bool -> GlobRef.t ->  bool list -> constr array -> constr option array ->
  constr option array -> constr array -> constr -> constr State.t

  (** {6 View for Arguments } *)

type head_argument =
  | ArgIsSPUparam of int * constr array
  (** constant context, position of the uniform parameter, args *)
  | ArgIsInd of int * constr array * constr array
  (** constant context, position of the one_inductive body, inst_nuparams inst_indices *)
  | ArgIsNested of MutInd.t * int * mutual_inductive_body * bool list
                    * one_inductive_body * constr array * constr array
  (** constant context, ind_nested, mutual and one body, strictly positivity of its uniform parameters,
      instantiation uniform paramerters, and of both non_uniform parameters and indices *)
  | ArgIsCst

(** View to decompose arguments as [forall locs, X] where [X] is further decomposed
    as a uniform parameter, the inductive, a nested argument or a constant. *)
type argument = rel_context * head_argument

(** Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is a uniform parameter, Ind, nested or a constant *)
val view_argument : MutInd.t -> mutual_inductive_body -> State.access_key list ->
  bool list -> constr -> argument State.t
