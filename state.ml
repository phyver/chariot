open Base

type state = {
    mutable verbose: int ;
    mutable prompt: string ;
    mutable env:environment;
    mutable debug: (string*bool) list;
}

let current_state = {
    verbose = 0                                                                                         ;
    prompt = "# "                                                                                     ;
    env = { current_priority = 0; current_bloc = 0; types = []; constants = []; functions = [] }        ;
    debug = [
        "show_type_struct", false;
        "show_term_struct", false;
        "dont_show_nats",   false;
        "dont_show_lists",   false;
    ]                                                                                                   ;
    }


let message k m = if current_state.verbose > k then (print_string (" " ^ (String.make k '-') ^ " "); m ())

let setDebugOption s v
  = let rec aux options s v acc = match options with
        | [] -> error ("option " ^ s ^ " doesn't exist")
        | (s',_)::options when s'=s -> (s',v)::List.rev_append options acc
        | x::options -> aux options s v (x::acc)
    in
    current_state.debug <- aux current_state.debug s v []

let debugOption s
  = let b = try List.assoc s current_state.debug with Not_found -> assert false
    in b


let ifDebug (s:string) (c:unit->unit) : unit
  = let b = debugOption s in
    if b then c()

