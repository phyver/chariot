open Base
open Misc
open Pretty
open Typing

let var_counter = ref 0


(* check tha all the functions are different *)
let check_uniqueness_functions funs =
    match uniq funs with
        | None -> ()
        | Some(f) -> error ("function " ^ f ^ " is defined more than once")


let check_new_funs_different_from_old new_funs old_funs =
    match common new_funs old_funs with
        | None -> ()
        | Some f -> error ("function " ^ f ^ " already exists")

let rec get_function_name = function
    | Var(f) -> f
    | Constant c -> error (c ^ " is not a function name")
    | Daimon -> error ("you cannot redefine the daimon")
    | Apply(Constant _, p) -> get_function_name p
    | Apply(p,_) -> get_function_name p

let rec get_variables = function
    | Daimon -> []
    | Var(x) -> [x]
    | Constant _ -> []
    | Apply(t1,t2) -> (get_variables t1) @ (get_variables t2)

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression * (term * term) list) list)
  =
    (* bloc number *)
    let new_bloc_nb = env.current_bloc + 1 in

    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    let new_functions_with_types = List.rev_map (function f,t,_ -> f,t) defs in

    let check_single_clause (f:var_name) (t:type_expression) (lhs_pattern,rhs_term:term*term) =
        (* get function from LHS and check it is equal to f *)
        let _f = get_function_name lhs_pattern in
        if not (_f = f) then error ("function names " ^ f ^ " and " ^ _f ^ " do not match");

        (* get variables *)
        let lhs_vars = get_variables lhs_pattern in
        (match uniq lhs_vars with
            | None -> ()
            | Some(x) -> error ("variable " ^ x ^ " appears more than once"));

        (* infer type of LHS, getting the type constraints on the variables (and the function itself) *)
        let infered_type_lhs, type_of_vars1 = infer_type lhs_pattern env [] in
        (* infer type of RHS *)
        let infered_type_rhs, type_of_vars2 = infer_type rhs_term env type_of_vars1 in
(* print_string "type_of_vars1, after "; print_list "-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) type_of_vars1; print_newline(); *)
(* print_string "type_of_vars2, after "; print_list "-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type env t) type_of_vars2; print_newline(); *)


        let infered_type_function = List.assoc f type_of_vars1 in
(* print_string "infered type of function:  "; print_type env infered_type_function; print_newline(); *)
(* print_string "           expected type:  "; print_type env t; print_newline(); *)
        if not (is_instance t infered_type_function) then error "the LHS pattern doesn't type check";

        (* check that all the constraints we got concern the remaining functions being defined *)
        List.iter (function x,t ->
                    if not (List.mem_assoc x type_of_vars1)
                    then begin
                        assert (not (x=f));
                        try
                            if not (is_instance (List.assoc x new_functions_with_types) t)
                            then error ("function " ^ x ^ " doesn't have appropriate type")
                        with Not_found -> error ("variable " ^ x ^ " is free!")
                    end
                  ) type_of_vars2;
(* print_newline(); *)
        ()
    in


    let process_single_def (f:var_name) (t:type_expression) (clauses:(term*term) list) =
        List.iter (check_single_clause f t) clauses;
        (f, env.current_bloc, t, clauses)
    in

    let functions = List.map (function f,t,clauses -> process_single_def f t clauses) defs in

    { env with current_bloc = new_bloc_nb; functions = functions @ env.functions }
