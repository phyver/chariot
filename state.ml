open Misc
open Base

type state = {
    mutable prompt: string ;
    mutable env:environment;
    mutable verbose: int ;
    mutable options: (string*bool) list;
}

let current_state = {
    prompt = "# "                                                                                     ;
    env = { current_type_bloc = 0; current_function_bloc = 0; types = []; constants = []; functions = [] }        ;
    verbose = 0                                                                                         ;
    options = [
        "show_type_struct", false;
        "show_term_struct", false;
        "dont_show_nats",   false;
        "dont_show_lists",   false;
    ]                                                                                                   ;
    }


let message k m = if current_state.verbose > k then (print_string (" " ^ (String.make k '-') ^ " "); m ())

let setOption s v
  = let rec aux options s v acc = match options with
        | [] -> error ("option " ^ s ^ " doesn't exist")
        | (s',_)::options when s'=s -> (s',v)::List.rev_append options acc
        | x::options -> aux options s v (x::acc)
    in
    current_state.options <- aux current_state.options s v []


let showOptions options =
    print_string "options:\n";
    List.iter (function o,v -> print_string ("  " ^ o ^ ": "); print_bool v; print_newline()) options


let option s
  = try List.assoc s current_state.options
    with Not_found -> error ("option " ^ s ^ " doesn't exist")

