open Base

type state = {
    mutable verbose: int ;
    mutable prompt: string ;
    mutable env:environment;
}

let current_state = {
    verbose = 0                                                                                         ;
    prompt = ">>> "                                                                                     ;
    env = { current_priority = 0; current_bloc = 0; types = []; constants = []; functions = [] }        ;
    }


let message k m = if current_state.verbose > k then (print_string (" " ^ (String.make k '-') ^ " "); m ())


