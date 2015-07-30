open Misc
open Base
open State
open SCTCalls

(*****************************
 * Sets of calls and graphs. *
 *****************************)

(* Sets of clauses *)
module Calls_Set = Set.Make (struct type t=sct_clause let compare=compare end)
type calls_set = Calls_Set.t

(* Call graphs: maps indexed by pairs of function names *)
module Call_Graph = Map.Make (struct type t=string*string let compare=compare end)
type call_graph = calls_set Call_Graph.t



(*
 * Adding a call to a set, keeping only maximal elements for the approximation
 * order.
 * It would be better if we could do this at the same time as the following
 * function: try to add the element, and raise an exception if it already
 * appears (or an approximation appears). This requires to use a custom map
 * module...
 *)
let add_call_set tau s =
  if (option "use_subsumption")
  then
    if Calls_Set.exists (fun sigma -> approximates sigma tau) s
    then s
    else Calls_Set.add tau (Calls_Set.filter (fun sigma -> not (approximates tau sigma)) s)
  else
    Calls_Set.add tau s

(* Checks if a call brings new information. *)
let new_call_set tau s =
    if (option "use_subsumption")
    then not (Calls_Set.exists (fun sigma -> approximates sigma tau) s)
    else not (Calls_Set.mem tau s)  (* FIXME something might be wrong here *)


(* computing the call graph *)
(* NOTE: hack, I will need to use Proj variants to register constructors
 * applied to the result of a call, and Const variants to register destructor
 * in argument position... *)
(* TODO *)



(* Counts the number of calls in a graph.  *)
let count_edges g = Call_Graph.fold (fun _ s n -> n+(Calls_Set.cardinal s)) g 0

(* Computing the transitive closure of a graph. *)
let transitive_closure initial_graph d b =

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

    Call_Graph.iter (fun fg a ->
      Call_Graph.iter (fun fg' a' ->
        let f,g = fg in
        let f',g' = fg' in
        if g=f'
        then begin
          Calls_Set.iter (fun tau ->
            Calls_Set.iter (fun tau' ->
              let all_calls = try Call_Graph.find (f,g') !result
                              with Not_found -> Calls_Set.empty
              in
              try
                (* ifDebug "show_all_compositions" *)
                (* begin fun _ -> *)
                (*   print_string "** Composing: **\n"; *)
                (*   print_call tau; *)
                (*   print_string "    with\n"; *)
                (*   print_call tau'; *)
                (*   print_string "    with B="; print_int b; print_string " and D="; print_int d; print_string "\n** to give\n"; *)
                (* end; *)
                let sigma : sct_clause = collapsed_compose d b tau tau' in
                (* ifDebug "show_all_compositions" *)
                (* begin fun _ -> *)
                (*   print_call sigma; *)
                (*   print_newline(); *)
                (*   print_newline() *)
                (* end; *)
                if (new_call_set sigma all_calls)
                then begin
                  new_arcs := true;
                  result := Call_Graph.add (f,g') (add_call_set sigma all_calls) !result;
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
    (* if (option "show_all_steps") *)
    (* begin fun _ -> *)
    (*   print_string ("** Graph of paths at iteration "^(string_of_int (!nb_steps))^" **\n"); *)
    (*   print_graph g; *)
    (*   print_newline() *)
    (* end; *)
    let g = one_step_TC ig g in
    if not !new_arcs
    then g
    else begin
      nb_steps := !nb_steps+1;
      closure ig g
    end
  in

  (* collapse all substitutions *)
  (* if (option "show_initial_call_graph") *)
  (* begin fun _ -> *)
  (*   print_string "** Control-flow graph given by the static analysis: **\n"; *)
  (*   print_graph initial_graph *)
  (* end; *)
  (* if (option "initial_collapse_of_graph") *)
  (* then begin fun _ -> *)
  (* let initial_graph = Call_Graph.map (fun s -> *)
  (*               Calls_Set.fold (fun tau s -> *)
  (*                 add_call_set (collapse_call d b tau) s) *)
  (*                 s Calls_Set.empty) *)
  (*                 initial_graph in *)
  (* if (option "show_initial_call_graph") *)
  (* begin fun _ -> *)
  (*   print_string "** Control-flow graph after collapse: **\n"; *)
  (*   print_graph initial_graph *)
  (* end *)
  (* end; *)
  let graph_of_paths = closure initial_graph initial_graph in

  (* ifDebug "show_final_call_graph" *)
  (* begin fun _ -> *)
  (*   print_string "** Graph of paths of the initial control-flow graph: **\n"; *)
  (*   print_graph graph_of_paths *)
  (* end; *)
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

let size_change_termination_bounds graph d b =
  assert (d>=0 && b>0) ;
  let tc_graph = transitive_closure graph d b in
    Call_Graph.for_all
      (fun fg s ->
        let f,g = fg in
        f<>g ||
        Calls_Set.for_all
          (fun sigma ->
            try
              not (compatible sigma (collapsed_compose d b sigma sigma)) ||
              begin
                (* ifDebug "show_coherents" *)
                (* begin fun _ -> *)
                (*   print_string ("** Found coherent loop from \"" ^ f ^ "\" to itself: **\n"); *)
                (*   print_call sigma *)
                (* end; *)
                decreasing sigma ||
                (
                (* ifDebug "show_nondecreasing_coherents" begin fun _ -> *)
                (*   print_string ("** Found non-decreasing coherent loop from \"" ^ f ^ "\" to itself: **\n"); *)
                (*   print_call sigma; *)
                (*   print_newline() *)
                (* end; *)
                false)
              end
            with Impossible_case -> true
          ) s
      ) tc_graph


(*****************************************
 * The functions called from the outside *
 *****************************************)

let size_change_termination graph =

  let rec ds n acc =
    if (current_state.depth <= n)
    then List.rev (current_state.depth::acc)
    else ds (2*n) (n::acc)
  in
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
        let t = size_change_termination_bounds graph d current_state.bound in
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
  let t = test (ds 1 [0]) in
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
