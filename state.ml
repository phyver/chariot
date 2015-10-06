(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
totality checker for recursive definitions involving nested least and
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

type opt = | OptBool of bool | OptString of string | OptInt of int

type state =
    {
        mutable current_bloc: int                                           ;  (* counter for blocs of function definitions and type definitions *)
        mutable env: environment                                            ;

        mutable options: (string*opt*string) list                           ;

        mutable last_explore: (int*plain_term) frozen_term option           ;
    }


let current_state =
    {
        current_bloc     = 0                    ;
        env = {
                types                 = []      ;
                constants             = []      ;
                functions             = []      ;
              }                                 ;
        options = [
            "depth",                 OptInt 2,       "depth of exploration during the SCP"                              ;
            "bound",                 OptInt 2,       "bound for weight during the SCP"                              ;

            "prompt",                OptString "# ", "prompt for the interactive toplevel"                          ;
            "verbose",               OptInt 0,       "verbosity level"                           ;
            "use_utf8",              OptBool true,   "use UTF8 symbols" ;
            "use_ansi_codes",        OptBool false,  "use ANSI color codes to display various information" ;

            "show_priorities",       OptBool true,   "display priorities when showing function definitions" ;
            "show_frozen_terms",     OptBool false,  "show frozen terms in reduced terms" ;
            "show_nats",             OptBool true,   "use decimal notation for displaying natural numbers" ;
            "show_lists",            OptBool true,   "use standard notations for displaying lists" ;
            "show_tuples",           OptBool true,   "use standard notations for displaying tuples" ;

            "unary_constants",       OptBool false,   "enforce that all constructors / destructors are unary" ;  (* TODO *)
            "only_termination",      OptBool false,   "only check termination and not totality (unsound)" ;  (* TODO *)
            "allow_incomplete_defs", OptBool true,   "allow incomplete definitions";
            "keep_useless_clauses",  OptBool false,  "keep useless clauses in function definitions";
            "continue_on_error",     OptBool false,  "do not quit on errors (only for non-interactive use)" ;
            "squash_priorities",     OptBool false,  "consecutive types of same polarity get the same priority" ;
            "use_subsumption",       OptBool true,   "use subsumption to simplify sets of clauses" ;
            "collapse_graph",        OptBool true,   "collapse initial call-graph" ;
            "allow_unsafe_defs",     OptBool true,   "allow definition that do not pass the SCP" ;
            "expand_clauses",        OptBool false,  "use the case expansion of the clauses to regenerate the clauses";
            (* "allow_structs",         OptBool true,   "allow structures inside terms"; *)
            (* "use_priorities",        OptBool true,   "use priorities for checking termination (unsound if false)" ;  (1* FIXME -> only check termination *1) *)

            (* various debuging options *)
            "show_initial_graph",    OptBool false,  "show initial call graph when checking totality" ;
            "show_final_graph",      OptBool false,  "show final call graph when checking totality" ;
            "show_all_steps",        OptBool false,  "show all successive graphs when checking totality" ;
            "show_coherent_loops",   OptBool false,  "show coherent loops found in the final graph when checking totality" ;
            "show_bad_loops",        OptBool false,  "show the first non-decreasing coherent loop found when checking totality" ;
            "incremental_SCP",       OptBool true,   "do not try the SCP at smaller depth";
        ]                                       ;
        last_explore = None                     ;
    }

let get_option (s:string) : opt
  = let opts = List.map (function o,v,h -> o,v) current_state.options in
    try List.assoc s opts
    with Not_found -> error ("option " ^ s ^ " doesn't exist")

(* get boolean option in current state *)
let option s
  = match get_option s with | OptBool v -> v | _ -> error (fmt "option %s is not boolean" s)

(* return true if current verbosity is greater than k *)
let verbose (k:int) : bool
  = match get_option "verbose" with | OptInt v -> v >= k | _ -> assert false

let prompt ()
  = match get_option "prompt" with OptString p -> p | _ -> assert false

let get_int_option s
  = match get_option s with OptInt n -> n | _ -> assert false

(* various helper function to print messages *)
let msg ?(indent=2) fmt
  (* = let prefix = "--" ^ (String.make indent ' ') ^ " " in *)
  = let prefix = (String.make indent '>') ^ " " in
    let prefix = if option "use_ansi_codes" then ansi_code "green" prefix else prefix in
    print_prefix stdout prefix fmt

let warning ?(indent=2) fmt
  (* = let prefix = "--" ^ (String.make indent '!') ^ " " in *)
  = let prefix = (String.make indent '!') ^ " warning: " in
    let prefix = if option "use_ansi_codes" then ansi_code "yellow" prefix else prefix in
    print_prefix stdout prefix fmt

let errmsg ?(indent=2) fmt
  (* = let prefix = "--" ^ (String.make indent '*') ^ " " in *)
  = let prefix = (String.make indent '*') ^ " error: " in
    let prefix = if option "use_ansi_codes" then ansi_code "red" prefix else prefix in
    print_prefix stdout prefix fmt

let debug ?(indent=2) fmt
  (* = let prefix = "--" ^ (String.make indent '=') ^ " " in *)
  = let prefix = (String.make indent '=') ^ " debug: " in
    let prefix = if option "use_ansi_codes" then ansi_code "blue" prefix else prefix in
    print_prefix stdout prefix fmt


let show_options ()
  =
    let string_of_option_val v
      = match v with
            | OptBool v -> string_of_bool v
            | OptString v -> v
            | OptInt v -> string_of_int v
    in
    msg "options:";
    List.iter (function o,v,h -> msg "    %-20s: %-10s  %s" o (string_of_option_val v) h) current_state.options

let set_option s v
  =
    let option_val_of_string old_value v
      = match old_value with
            | OptBool _ -> OptBool (bool_of_string v)
            | OptString _ -> OptString v
            | OptInt _ -> OptInt (int_of_string v)
    in

    let rec set_option_aux options s v =
        match options with
            | [] -> error ("option " ^ s ^ " doesn't exist")
            | (s',old_value,h)::options when s'=s -> (s',option_val_of_string old_value v,h)::options
            | x::options -> x::(set_option_aux options s v)
    in
    let akn () = if verbose 1 then msg "option %s is set to %s" s v
    in
    match s with
        | "" -> show_options ()
        | s ->
            begin
                    current_state.options <- set_option_aux current_state.options s v;
                    akn()
            end


