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

type state =
    {
        mutable current_bloc: int                           ;  (* counter for blocs of function definitions and type definitions (odd for data and even for codata) *)
        mutable env: environment                            ;

        mutable prompt: string                              ;
        mutable verbose: int                                ;
        mutable boolean_options: (string*bool*string) list  ;
        mutable depth: int                                  ;
        mutable bound: int                                  ;

        mutable last_term: type_expression term option      ;
        mutable last_explore: explore_term option           ;
    }

let current_state =
    {
        current_bloc     = 0                    ;
        env = {
                types                 = []      ;
                constants             = []      ;
                functions             = []      ;
              }                                 ;
        prompt = "# "                           ;
        verbose = 0                             ;
        boolean_options = [
            "show_type_struct",        false    , "show type of lazy structures in explore mode" ;
            "show_term_struct",        false    , "show lazy terms in explore mode" ;
            "show_nats",               true     , "use decimal notation for displaying natural numbers" ;
            "show_lists",              true     , "use standard notations for displaying lists" ;
            "show_tuples",             true     , "use standard notations for displaying tuples" ;

            "allow_incomplete_defs",   false    , "allow incomplete definitions";
            "use_priorities",          true     , "use priorities for checking termination (unsound if false)" ;  (* FIXME -> only check termination *)
            "show_priorities",         true     , "display priorities when showing function definitions" ;
            "continue_on_error",       false    , "do not quit on errors (only for non-interactive use)" ;
            "squash_priorities",       false    , "consecutive types of same polarity get the same priority" ;
            "use_ansi_codes",          false    , "use ANSI color codes to display various information" ;
            "use_subsumption",         true     , "use subsumption to simplify sets of clauses" ;
            "collapse_graph",          true     , "collapse initial call-graph" ;
            "check_adequacy",          false    , "use the SCT to check adequacy of definitions" ;      (* FIXME: allow_non_adequate_definitions *)

(* various debuging options *)
            "show_initial_graph",      false    , "show initial call graph when checking adequacy" ;
            "show_final_graph",        false    , "show final call graph when checking adequacy" ;
            "show_all_steps",          false    , "show all successive graphs when checking adequacy" ;
            "show_coherent_loops",     false    , "show coherent loops found in the final graph when checking adequacy" ;
            "show_bad_loops",          false    , "show the first non-decreasing coherent loop found when checking adequacy" ;
        ]                                       ;
        depth = 2                               ;
        bound = 2                               ;
        last_term = None                        ;
        last_explore = None                     ;
    }

(* get boolean option in current state *)
let option (s:string) : bool
  = try List.assoc s (List.map (function o,v,h -> o,v) current_state.boolean_options)
    with Not_found -> error ("option " ^ s ^ " doesn't exist")

(* return true if current verbosity is greater than k *)
let verbose (k:int) : bool
  = current_state.verbose >= k

(* various helper function to print messages *)
let msg ?(indent=0) fmt
  = let prefix = "--" ^ (String.make indent ' ') ^ " " in
    print_prefix stdout prefix fmt

let warning ?(indent=2) fmt
  = let prefix = "--" ^ (String.make indent '!') ^ " " in
    let prefix = if option "use_ansi_codes" then ansi_code "cyan" prefix else prefix in
    print_prefix stdout prefix fmt

let errmsg ?(indent=2) fmt
  = let prefix = "--" ^ (String.make indent '*') ^ " " in
    let prefix = if option "use_ansi_codes" then ansi_code "red" prefix else prefix in
    print_prefix stdout prefix fmt

let debug ?(indent=2) fmt
  = let prefix = "--" ^ (String.make indent '=') ^ " " in
    let prefix = if option "use_ansi_codes" then ansi_code "yellow" prefix else prefix in
    print_prefix stdout prefix fmt


let show_options ()
  = msg "options:";
    msg "    %-20s: %-10s  %s" "prompt"     current_state.prompt    "prompt for interactive use";
    msg "    %-20s: %-10d  %s" "verbose"    current_state.verbose   "verbosity level";
    msg "    %-20s: %-10d  %s" "depth"      current_state.depth     "depth of terms when checking adequacy";
    msg "    %-20s: %-10d  %s" "bound"      current_state.bound     "bound for the weights of terms when checking adequacy";
    List.iter (function o,v,h -> msg "    %-20s: %-10s  %s" o (if v then "true" else "false") h) current_state.boolean_options

let set_option s v
  = let rec set_option_aux options s v =
        match options with
            | [] -> error ("option " ^ s ^ " doesn't exist")
            | (s',_,h)::options when s'=s -> (s',v,h)::options
            | x::options -> x::(set_option_aux options s v)
    in
    match s with
        | "prompt" -> current_state.prompt <- v
        | "verbose" -> (try current_state.verbose <- int_of_string v with Failure _ -> error "%s is not an integer")
        | "depth" ->
            begin
                try
                    let d = int_of_string v in
                    if d < 0
                    then error "depth cannot be strictly negative"
                    else current_state.depth <- d
                with Failure _ -> error "%s is not an integer"
            end
        | "bound" -> 
            begin
                try
                    let b = int_of_string v in
                    if b <= 0
                    then error "bound must be strictly positive"
                    else current_state.bound <- b
                with Failure _ -> error "%s is not an integer"
            end
        | "" -> show_options ()
        | s -> current_state.boolean_options <- set_option_aux current_state.boolean_options s (bool_of_string v)


