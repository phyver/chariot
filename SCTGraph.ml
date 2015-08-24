(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
adequacy checker for recursive definitions involving nested least and
greatest fixed points.

This software is governed by the CeCILL-B license under French law and
abiding by the rules of distribution of free software.  You can  use,
modify and/ or redistribute the software under the terms of the CeCILL-B
license as circulated by CEA, CNRS and INRIA at the following URL
"http://www.cecill.info".

As a counterpart to the access to the source code and  rights to copy,
modify and redistribute granted by the license, users are provided only
with a limited warranty  and the software's author,  the holder of the
economic rights,  and the successive licensors  have only  limited
liability.

In this respect, the user's attention is drawn to the risks associated
with loading,  using,  modifying and/or developing or reproducing the
software by the user in light of its specific status of free software,
that may mean  that it is complicated to manipulate,  and  that  also
therefore means  that it is reserved for developers  and  experienced
professionals having in-depth computer knowledge. Users are therefore
encouraged to load and test the software's suitability as regards their
requirements in conditions enabling the security of their systems and/or
data to be ensured and,  more generally, to use and operate it in the
same conditions as regards security.

The fact that you are presently reading this means that you have had
knowledge of the CeCILL-B license and that you accept its terms.
========================================================================*)


open Misc
open Env
open Utils
open State
open Pretty
open SCTCalls

(*****************************
 * Sets of calls and graphs. *
 *****************************)

(* Sets of clauses *)
module ClauseSet = Set.Make (struct type t=sct_clause let compare=compare end)
type clauseSet = ClauseSet.t

(* Call graphs: maps indexed by pairs of function names *)
module CallGraph = Map.Make (struct type t=var_name*var_name let compare=compare end)
type call_graph = clauseSet CallGraph.t


let print_callgraph graph
  = CallGraph.iter (fun fg cs ->
      msg "calls from %s to %s:" (fst fg) (snd fg);
      ClauseSet.iter (function clause ->
        msg  "    %s" (string_of_sct_clause clause)) cs) graph
    ; print_newline(); flush_all()

(*
 * Adding a call to a set, keeping only maximal elements for the approximation
 * order.
 * It would be better if we could do this at the same time as the following
 * function: try to add the element, and raise an exception if it already
 * appears (or an approximation appears). This requires to use a custom map
 * module...
 *)
let add_call_set clause s =
  if option "use_subsumption"
  then
    if ClauseSet.exists (fun cl -> approximates cl clause) s
    then s
    else ClauseSet.add clause (ClauseSet.filter (fun cl -> not (approximates clause cl)) s)
  else
    ClauseSet.add clause s

(* Checks if a call brings new information. *)
let new_call_set clause s =
    if option "use_subsumption"
    then not (ClauseSet.exists (fun cl -> approximates cl clause) s)
    else not (ClauseSet.mem clause s)  (* FIXME something might be wrong here *)

(* collapse a whole graph *)
let collapse_graph b d graph
  = CallGraph.map (fun s ->
                ClauseSet.fold (fun clause2 s ->
                  add_call_set (collapse_clause b d clause2) s)
                  s ClauseSet.empty)
                  graph

(* computing the call graph *)
(* NOTE: hack, I will need to use Proj variants to register constructors
 * applied to the result of a call, and Const variants to register destructor
 * in argument position... *)
let callgraph_from_definitions
  (functions : (var_name * type_expression * 't function_clause list) list)
  : call_graph
  =
    let function_names = List.map (function f,_,_ -> f) functions
    in

    let clauses = List.concat (List.map (function _,_,cls -> cls) functions)
    in

    let graph = CallGraph.empty
    in

    let rec extract_params_aux d
      = match d with
            | Var(x,_) -> [x]
            | App(u1,u2,_) -> (extract_params_aux u1) @ (extract_params_aux u2)
            | Const _ -> []
            | Proj _ | Angel _ -> assert false
            | Special(s,_) -> s.bot
    in

    let rec extract_params d
      = match get_head d,get_args d with
            | Var(f,_),args -> List.concat (List.map extract_params_aux args)
            | Proj _,u::args -> (extract_params u) @ (List.concat (List.map extract_params_aux args))
            | Proj _,[] | Const _,_ | Angel _,_ | App _,_ -> assert false
            | Special(s,_),_ -> s.bot
    in

    let rec process_clause graph (lhs,rhs)
      : call_graph
      =
        let lhs = pattern_to_approx_term lhs
        in

        let caller = get_function_name lhs
        in

        let params = extract_params lhs
        in

        (* let top = todo "top" (1* the greatest element, ie the least informative *1) *)
        let top = Special(ApproxConst (List.map (fun x -> (None,Infty,x)) params),())
        in

        let rec process_arg (p:'t term)
          : approx_term
          = match get_head p,get_args p with
                | Var(x,t),_ when List.mem x params -> Var(x,t)   (* TODO: check if some function appears in the arguments... *)
                | Var(x,_),_ -> top
                | Angel t,_ -> Angel t
                | Const(c,prio,t),args -> app (Const(c,prio,t)) (List.map process_arg args)
                | Proj(d,prio,t), args -> Special(ApproxConst (collapse0 (pattern_to_approx_term p)),t)
                | Special(s,_),_ -> s.bot
                | App _,_ -> assert false
        in

        let rec process_rhs graph rhs calling_context
          : call_graph
          = match get_head rhs, get_args rhs with
                | Var(called,t), args when List.mem called function_names ->
                    let _args = List.map process_arg args
                    in
                    let call = lhs, app_all (Var(called,t)) (_args@calling_context)
                    in
                    let graph = CallGraph.add (caller,called) (add_call_set call (try CallGraph.find (caller,called) graph with Not_found -> ClauseSet.empty)) graph
                    in
                    List.fold_left (fun graph rhs -> process_rhs graph rhs [Special(ApproxProj(None,Infty),())]) graph args

                | Var _, args | Angel _, args ->
                    List.fold_left (fun graph rhs -> process_rhs graph rhs [Special(ApproxProj(None,Infty),())]) graph args

                | Const(c,p,t),args ->
                    List.fold_left (fun graph rhs -> process_rhs graph rhs ((Special(ApproxProj(p,Num 1),t))::calling_context)) graph args

                | Proj(d,p,t),u::args ->
                    let _args = List.map process_arg args
                    in
                    let graph = process_rhs graph u (Proj(d,p,t)::_args@calling_context)
                    in
                    List.fold_left (fun graph rhs -> process_rhs graph rhs [Special(ApproxProj(None,Infty),t)]) graph args

                | Special(s,_), _ -> s.bot

                | App _, _ -> assert false
                | Proj _,[] -> assert false
        in
        process_rhs graph rhs []
    in

    let graph = List.fold_left (fun graph clause -> process_clause graph clause) graph clauses
    in
    graph


(* Counts the number of calls in a graph.  *)
let count_edges g = CallGraph.fold (fun _ s n -> n+(ClauseSet.cardinal s)) g 0

(* Computing the transitive closure of a graph. *)
let transitive_closure initial_graph b d =

  (* references to keep some info about the graph *)
  let new_arcs = ref false in
  let nb_steps = ref 0 in

  (* single step for the TC. "ig" is the initial graph, "g" is the current graph *)
  let one_step_TC ig g =
    (*
     * local reference for the resulting graph: this is initialized to the
     * starting graph
     *)
    let result = ref g in

    CallGraph.iter (fun fg a ->
      CallGraph.iter (fun fg' a' ->
        let f,g = fg in
        let f',g' = fg' in
        if g=f'
        then begin
          ClauseSet.iter (fun clause2 ->
            ClauseSet.iter (fun clause2' ->
              let all_calls = try CallGraph.find (f,g') !result
                              with Not_found -> ClauseSet.empty
              in
              try
                (* ifDebug "show_all_compositions" *)
                (* begin fun _ -> *)
                (*   print_string "** Composing: **\n"; *)
                (*   print_call clause2; *)
                (*   print_string "    with\n"; *)
                (*   print_call clause2'; *)
                (*   print_string "    with B="; print_int b; print_string " and D="; print_int d; print_string "\n** to give\n"; *)
                (* end; *)
                let clause1 : sct_clause = collapsed_compose b d clause2 clause2' in
                (* ifDebug "show_all_compositions" *)
                (* begin fun _ -> *)
                (*   print_call clause1; *)
                (*   print_newline(); *)
                (*   print_newline() *)
                (* end; *)
                if (new_call_set clause1 all_calls)
                then begin
                  new_arcs := true;
                  result := CallGraph.add (f,g') (add_call_set clause1 all_calls) !result;
                end
              with Impossible_case ->
                (* ifDebug "show_all_compositions" *)
                (* begin fun _ -> *)
                (*   print_string "    IMPOSSIBLE CASE..."; *)
                (*   print_newline(); *)
                (*   print_newline() *)
                (* end; *)
                ()
            ) a'
          ) a
        end
      ) ig
    ) g;
    !result
  in

  (*
   * Computing the actual closure. We know we've reached the TC when no new
   * edge was added.
   *)
  let rec closure ig g =
    new_arcs := false;
    if option "show_all_steps"
    then begin
        msg "Graph of paths at iteration %d" !nb_steps;
        print_callgraph g
    end;
    let g = one_step_TC ig g in
    if not !new_arcs
    then g
    else begin
      nb_steps := !nb_steps+1;
      closure ig g
    end
  in

  if option "show_initial_graph" && not (option "show_all_steps")
  then begin
      msg "initial callgraph:";
      print_callgraph initial_graph
   end;

  let graph_of_paths = closure initial_graph initial_graph in

  if option "show_final_graph" && not (option "show_all_steps")
  then begin
      msg "Graph of paths of the final control-flow graph:";
      print_callgraph graph_of_paths
  end;
  (* ifDebug "show_summary_TC" *)
  (* begin fun _ -> *)
  (*   print_string "* the initial control-flow graph contained "; print_int (count_edges initial_graph); print_string " edge(s) *\n"; *)
  (*   print_string "* its graph of paths contains "; print_int (count_edges graph_of_paths); print_string " edge(s) *\n"; *)
  (*   print_string "* "; print_int !nb_steps; print_string " iteration(s) were necessary to compute the graph of paths. *\n"; *)
  (*   print_newline() *)
  (* end; *)

  (* Returns the value of the TC. *)
  graph_of_paths


(**********************************************************************
 * Putting everything together: the size-change termination principle *
 **********************************************************************)

let size_change_termination_bounds graph b d =
  assert (d>=0 && b>0) ;
  let tc_graph = transitive_closure graph b d in
    CallGraph.for_all
      (fun fg s ->
        let f,g = fg in
        f<>g ||
        ClauseSet.for_all
          (fun clause1 ->
            try
              let clause11 = collapsed_compose b d clause1 clause1 in
              not (compatible clause1 clause11) ||
              begin
                if option "show_coherent_loops"
                then begin
                    msg "Found coherent loop from \"%s\" to itself:" f;
                    msg "  %s" (string_of_sct_clause clause1)
                end;
                decreasing clause1 ||
                (
                    if option "show_bad_loops"
                    then begin
                        msg "Found non-decreasing coherent loop from \"%s\" to itself" f;
                        msg "  %s" (string_of_sct_clause clause1)
                end;
                false)
              end
            with Impossible_case -> true
          ) s
      ) tc_graph


(*****************************************
 * The functions called from the outside *
 *****************************************)

let size_change_termination graph =

  let rec test = function
      [] -> false
    | d::ds ->
        (* ifDebug "show_summary_TC" *)
        (* begin fun _ -> *)
        (*   print_string "** Incremental test: using d = "; *)
        (*   print_int d; *)
        (*   print_string " **"; *)
        (*   print_newline() *)
        (* end; *)
        let t = size_change_termination_bounds graph current_state.bound d in
        if t
        then (
          (* ifDebug "show_summary_TC" *)
          (* begin fun _ -> *)
          (*   print_string "** These functions are size change terminating for d="; *)
          (*   print_int d; print_string " and b="; *)
          (*   print_int current_state.bound;print_string ". **\n\n" *)
          (* end; *)
          true)
        else
          test ds
  in
  (* FIXME: use this once it works *)
  (* let rec ds n acc = *)
  (*   if (current_state.depth <= n) *)
  (*   then List.rev (current_state.depth::acc) *)
  (*   else ds (2*n) (n::acc) *)
  (* in *)
  (* let t = test (ds 1 [0]) in *)
  let t = test [current_state.depth] in
  if t
  then true
  else (
    (* ifDebug "show_summary_TC" *)
    (* begin fun _ -> *)
    (*   print_string "** These functions are NOT size change terminating for d="; *)
    (*   print_int (current_state.depth); print_string " and b="; *)
    (*   print_int (current_state.bound);print_string ". **\n\n" *)
    (* end; *)
    false)
