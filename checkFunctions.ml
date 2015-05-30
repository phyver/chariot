open Base
open Misc

(* check tha all the functions are different *)
let check_uniqueness_functions funs =
    match uniq funs with
        | None -> ()
        | Some(f) -> raise @$ Error ("*** function " ^ f ^ " is defined more than once")


let check_new_funs_different_from_old new_funs old_funs =
    match common new_funs old_funs with
        | None -> ()
        | Some f -> raise @$ Error ("*** function " ^ f ^ " already exists")

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression * (term * term) list) list)
  =
    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    let process_single_clause (f:var_name) (t:type_expression) (clauses:term*term) =
        (* get function from LHS and check it is equal to f *)

        (* get variables *)

        (* add types *)


        ()
    in


    let process_single_def (f:var_name) (t:type_expression) (clauses:(term*term) list) =
        (* make type parameters non unifiable *)

        ()
    in




      env
