open Base
open Misc
open Pretty
open Typing
open CheckCoverage

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

let rec get_variables (App(u,args)) =
    let vars = List.concat (List.map get_variables args) in
    match u with
    | Angel | Const _ -> vars
    | Proj(v,_,_) -> (get_variables v)@vars
    | Var(x) -> [x]

let rec put_priority env (App(u,args):unit term) : priority term =
    let args = List.map (put_priority env) args in
    match u with
        | Angel -> App(Angel,args)
        | Var(x) -> App(Var(x),args)
        | Proj(v,d,()) -> let v = put_priority env v in App(Proj(v,d,get_constant_priority env d),args)
        | Const(c,()) -> App(Const(c,get_constant_priority env c), args)

let rec get_rightmost t = match t with
    | TVar _ | Data _ -> t
    | Arrow(_,t) -> get_rightmost t

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression option * (unit term * unit term) list) list)
  : environment
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

    let check_single_clause (f:var_name) (t:type_expression) (lhs_pattern,rhs_term:unit term*unit term) : type_expression =
(* print_string ("\nCHECK SINGLE CLAUSE OF FUNCTION " ^ f ^ "\n"); *)
(* print_string "given type:  "; print_type t; print_newline(); *)
        (* get function from LHS and check it is equal to f *)
        let _f = get_function_name lhs_pattern in
        if not (_f = f) then error ("function names " ^ f ^ " and " ^ _f ^ " do not match");

        (* get variables *)
        let lhs_vars = get_variables lhs_pattern in
        (match uniq lhs_vars with
            | None -> ()
            | Some(x) -> error ("variable " ^ x ^ " appears more than once"));

        (* infer type of LHS, getting the type constraints on the variables (and the function itself) *)
        reset_fresh();
        let infered_type_lhs, type_of_vars1 = infer_type env lhs_pattern [] in
(* print_string "infered type of lhs:  "; print_type infered_type_lhs; print_newline(); *)
(* print_string "type_of_vars1:  "; print_list "-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type t) type_of_vars1; print_newline(); *)
        (* infer type of RHS *)
        let infered_type_rhs, type_of_vars2 = infer_type env rhs_term type_of_vars1 in
(* print_string "infered type of rhs:  "; print_type infered_type_rhs; print_newline(); *)
(* print_string "type_of_vars2:  "; print_list "-" "" " ; " "" (function x,t -> print_string (x ^ ":"); print_type t) type_of_vars2; print_newline(); *)
        if not (is_instance infered_type_rhs infered_type_lhs)
        then error ("rhs and lhs do not have the same type");

(* print_string "infered type of function:  "; print_type env infered_type_function; print_newline(); *)
(* print_string "           expected type:  "; print_type env t; print_newline(); *)
        let infered_type_function = List.assoc f type_of_vars2 in
(* print_string "infered type of function:  "; print_type infered_type_function; print_newline(); *)
        let sigma = unify_type infered_type_rhs infered_type_lhs in
(* print_string "SIGMA "; print_list "" "" " ; " "" (function x,t -> print_string ("'" ^ x ^ "="); print_type t) sigma; print_newline(); *)
        let infered_type_function = subst_type sigma infered_type_function in

        (* check that the function is applied to all its arguments *)
        (* let sigma = unify_type t infered_type_function in *)
        (* match subst_type sigma infered_type_rhs with *)
        (*     | arrow _ -> error "functions should be η-expanded" *)
        (*     | _ -> (); *)

        (* check that all the constraints we got concern the remaining functions being defined *)
        List.iter (function x,t ->
                    if not (List.mem_assoc x type_of_vars1)
                    then begin
                        assert (not (x=f));
                        try
                            match List.assoc x new_functions_with_types with
                                | None -> ()
                                | Some tx -> if not (is_instance tx t)
                                             then error ("function " ^ x ^ " doesn't have appropriate type")
                        with Not_found -> error (x ^ " is free!")
                    end
                  ) type_of_vars2;
        infered_type_function
    in


    let process_single_def (f:var_name) (t:type_expression option) (clauses:(unit term*unit term) list) =
        let t = match t with None -> TVar("type_" ^ f) | Some t -> t in

        let t = List.fold_left
                        (fun t clause ->
                            let t2 = check_single_clause f t clause in

(* print_string "t:  "; print_type t; print_string "  and  "; *)
(* print_string "t2:  "; print_type t2; *)
(* print_newline(); *)
                            subst_type (unify_type t2 t) t)
                        t
                        clauses
        in

        (* check coverage *)
        if exhaustive env clauses
        then (f, env.current_bloc, t, List.map (function p,v -> put_priority env p, put_priority env v) clauses)
        else error ("function " ^ f ^ " is not exhaustive")

    in

    let functions = List.map (function f,t,clauses -> process_single_def f t clauses) defs in

    { env with current_bloc = new_bloc_nb; functions = functions @ env.functions }
