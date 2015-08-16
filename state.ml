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
open Base

type state =
    {
        mutable current_type_bloc: int      ;         (* counter for blocs of type definitions: odd for data and even for codata *)
        mutable current_function_bloc: int  ;
        mutable env:     environment        ;
        mutable prompt:  string             ;
        mutable verbose: int                ;
        mutable options: (string*bool) list ;
        mutable depth: int                  ;
        mutable bound: int                  ;
    }

let current_state =
    {
        current_type_bloc     = 0               ;
        current_function_bloc = 0               ;
        env = {
                types                 = []      ;
                constants             = []      ;
                functions             = []      ;
              }                                 ;
        prompt = "# "                           ;
        verbose = 0                             ;
        options = [
            "show_type_struct",        false    ;
            "show_term_struct",        false    ;
            "show_nats",               true     ;
            "show_lists",              true     ;
            "show_tuples",             true     ;
            "check_completeness",      true     ;
            "use_priorities",          true     ;
            "show_priorities",         true     ;
            "continue_on_error",       false    ;
            "squash_priorities",       false    ;
            "use_ansi_codes",          false    ;
            "use_subsumption",         true     ;
            "collapse_graph",          true     ;
            "check_adequacy",          false    ;

(* various debuging options *)
            "show_initial_graph",      false    ;
            "show_final_graph",        false    ;
            "show_all_steps",          false    ;
            "show_coherent_loops",     false    ;
            "show_bad_loops",          false    ;
        ]                                       ;
        depth = 2                               ;
        bound = 2                               ;
    }


let message k m
  = if current_state.verbose > k
    then (print_string (" " ^ (String.make k '-') ^ " "); m ())

let bool_of_string = function
    | "true" | "True" | "TRUE" | "1" -> true
    | "false" | "False" | "FALSE" | "0" -> false
    | s -> raise (Invalid_argument ("bool_of_int: " ^ s))

let showOptions ()
  = msg "options:";
    msg "\t- %s: %s" "prompt" current_state.prompt;
    msg "\t- %s: %d" "verbose" current_state.verbose;
    msg "\t- %s: %d" "depth" current_state.depth;
    msg "\t- %s: %d" "bound" current_state.bound;
    List.iter (function o,v -> msg "\t- %s: %b" o v) current_state.options

let setOption s v
  = let rec setOption_aux options s v acc =
        match options with
            | [] -> error ("option " ^ s ^ " doesn't exist")
            | (s',_)::options when s'=s -> (s',v)::List.rev_append options acc
            | x::options -> setOption_aux options s v (x::acc)
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
        | "" -> showOptions ()
        | s -> current_state.options <- setOption_aux current_state.options s (bool_of_string v) []



let option s
  = try List.assoc s current_state.options
    with Not_found -> error ("option " ^ s ^ " doesn't exist")

