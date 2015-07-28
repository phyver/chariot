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
        | "depth" -> (try current_state.depth <- int_of_string v with Failure _ -> error "%s is not an integer")
        | "bound" -> (try current_state.bound <- int_of_string v with Failure _ -> error "%s is not an integer")
        | "" -> showOptions ()
        | s -> current_state.options <- setOption_aux current_state.options s (bool_of_string v) []



let option s
  = try List.assoc s current_state.options
    with Not_found -> error ("option " ^ s ^ " doesn't exist")

