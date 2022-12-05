(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open EConstr
open Vars
open Tacmach
open Tactics
open Tacticals
open Proofview.Notations
open Termops
open Formula
open Sequent

module NamedDecl = Context.Named.Declaration

type tactic = unit Proofview.tactic

type seqtac= (Sequent.t -> tactic) -> Sequent.t -> tactic

type lseqtac= GlobRef.t -> seqtac

type 'a with_backtracking = tactic -> 'a

let wrap ~flags n b continue seq =
  Proofview.Goal.enter begin fun gls ->
  Control.check_for_interrupt ();
  let nc = Proofview.Goal.hyps gls in
  let env=pf_env gls in
  let sigma = project gls in
  let rec aux i nc ctx=
    if i<=0 then seq else
      match nc with
          []->anomaly (Pp.str "Not the expected number of hyps.")
        | nd::q->
            let id = NamedDecl.get_id nd in
            if occur_var env sigma id (pf_concl gls) ||
              List.exists (occur_var_in_decl env sigma id) ctx then
                (aux (i-1) q (nd::ctx))
            else
              add_formula ~flags env sigma Hyp (FormulaId (GlobRef.VarRef id)) (NamedDecl.get_type nd) (aux (i-1) q (nd::ctx)) in
  let seq1=aux n nc [] in
  let seq2=if b then
    add_formula ~flags env sigma Concl GoalId (pf_concl gls) seq1 else seq1 in
    continue seq2
  end

let clear_global=function
  | GlobRef.VarRef id-> clear [id]
  | _->tclIDTAC

(* connection rules *)

let axiom_tac seq =
  Proofview.Goal.enter begin fun gl ->
  match Sequent.find_goal (project gl) seq with
  | gr -> pf_constr_of_global gr >>= fun c -> exact_no_check c
  | exception Not_found -> tclFAIL (Pp.str "No axiom link")
  end

let ll_atom_tac ~flags a backtrack id continue seq =
  let open EConstr in
  tclIFTHENELSE
      (tclTHENLIST
        [(Proofview.tclEVARMAP >>= fun sigma ->
          let gr =
            try Proofview.tclUNIT (find_left sigma a seq)
            with Not_found -> tclFAIL (Pp.str "No link")
          in
          gr >>= fun gr ->
          pf_constr_of_global gr >>= fun left ->
          pf_constr_of_global id >>= fun id ->
            generalize [(mkApp(id, [|left|]))]);
         clear_global id;
         intro])
    (wrap ~flags 1 false continue seq) backtrack

(* right connectives rules *)

let and_tac ~flags backtrack continue seq=
  tclIFTHENELSE simplest_split (wrap ~flags 0 true continue seq) backtrack

let or_tac ~flags backtrack continue seq=
  tclORELSE
    (any_constructor false (Some (tclCOMPLETE (wrap ~flags 0 true continue seq))))
    backtrack

let arrow_tac ~flags backtrack continue seq=
  tclIFTHENELSE intro (wrap ~flags 1 true continue seq)
    (tclORELSE
       (tclTHEN introf (tclCOMPLETE (wrap ~flags 1 true continue seq)))
       backtrack)
(* left connectives rules *)

let left_and_tac ~flags ind backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
  let n=(construct_nhyps (pf_env gl) ind).(0) in
   tclIFTHENELSE
     (tclTHENLIST
      [(pf_constr_of_global id >>= simplest_elim);
       clear_global id;
       tclDO n intro])
     (wrap ~flags n false continue seq)
     backtrack
  end

let left_or_tac ~flags ind backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
  let v=construct_nhyps (pf_env gl) ind in
  let f n=
    tclTHENLIST
      [clear_global id;
       tclDO n intro;
       wrap ~flags n false continue seq] in
    tclIFTHENSVELSE
      (pf_constr_of_global id >>= simplest_elim)
      (Array.map f v)
      backtrack
  end

let left_false_tac id=
  Tacticals.pf_constr_of_global id >>= simplest_elim

(* left arrow connective rules *)

(* We use this function for false, and, or, exists *)

let ll_ind_tac ~flags (ind,u as indu) largs backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
     let rcs=ind_hyps (pf_env gl) (project gl) 0 indu largs in
     let vargs=Array.of_list largs in
             (* construire le terme  H->B, le generaliser etc *)
     let myterm idc i=
       let rc=rcs.(i) in
       let p=List.length rc in
       let u = EInstance.make u in
       let cstr=mkApp ((mkConstructU ((ind,(i+1)),u)),vargs) in
       let vars=Array.init p (fun j->mkRel (p-j)) in
       let capply=mkApp ((lift p cstr),vars) in
       let head=mkApp ((lift p idc),[|capply|]) in
         EConstr.it_mkLambda_or_LetIn head rc in
       let lp=Array.length rcs in
       let newhyps idc =List.init lp (myterm idc) in
         tclIFTHENELSE
           (tclTHENLIST
              [(pf_constr_of_global id >>= fun idc -> generalize (newhyps idc));
               clear_global id;
               tclDO lp intro])
           (wrap ~flags lp false continue seq) backtrack
  end

let ll_arrow_tac ~flags a b c backtrack id continue seq=
  let open EConstr in
  let open Vars in
  let cc=mkProd(Context.make_annot Anonymous Sorts.Relevant,a,(lift 1 b)) in
  let d idc = mkLambda (Context.make_annot Anonymous Sorts.Relevant,b,
                  mkApp (idc, [|mkLambda (Context.make_annot Anonymous Sorts.Relevant,(lift 1 a),(mkRel 2))|])) in
    tclORELSE
      (tclTHENS (cut c)
         [tclTHENLIST
            [introf;
             clear_global id;
             wrap ~flags 1 false continue seq];
          tclTHENS (cut cc)
            [(pf_constr_of_global id >>= fun c -> exact_no_check c);
             tclTHENLIST
               [(pf_constr_of_global id >>= fun idc -> generalize [d idc]);
                clear_global id;
                introf;
                introf;
                tclCOMPLETE (wrap ~flags 2 true continue seq)]]])
      backtrack

(* quantifier rules (easy side) *)

let forall_tac ~flags backtrack continue seq=
  tclORELSE
    (tclIFTHENELSE intro (wrap ~flags 0 true continue seq)
       (tclORELSE
          (tclTHEN introf (tclCOMPLETE (wrap ~flags 0 true continue seq)))
          backtrack))
    (if flags.qflag then
       tclFAIL (Pp.str "reversible in 1st order mode")
     else
       backtrack)

let left_exists_tac ~flags ind backtrack id continue seq =
  Proofview.Goal.enter begin fun gl ->
  let n=(construct_nhyps (pf_env gl) ind).(0) in
    tclIFTHENELSE
      (Tacticals.pf_constr_of_global id >>= simplest_elim)
      (tclTHENLIST [clear_global id;
                    tclDO n intro;
                    (wrap (n-1) ~flags false continue seq)])
      backtrack
  end

let ll_forall_tac ~flags prod backtrack id continue seq=
  tclORELSE
    (tclTHENS (cut prod)
       [tclTHENLIST
          [intro;
           (pf_constr_of_global id >>= fun idc ->
           Proofview.Goal.enter begin fun gls->
              let open EConstr in
              let id0 = List.nth (pf_ids_of_hyps gls) 0 in
              let term=mkApp(idc,[|mkVar(id0)|]) in
              tclTHEN (generalize [term]) (clear [id0])
           end);
           clear_global id;
           intro;
           tclCOMPLETE (wrap ~flags 1 false continue (deepen seq))];
        tclCOMPLETE (wrap ~flags 0 true continue (deepen seq))])
    backtrack

(* rules for instantiation with unification moved to instances.ml *)
