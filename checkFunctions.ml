open Base
open Misc
open Pretty
open Typing
open CheckCoverage

(* check that all the functions are different *)
let check_uniqueness_functions funs =
    match find_dup funs with
        | None -> ()
        | Some(f) -> error ("function " ^ f ^ " is defined more than once")

let check_new_funs_different_from_old new_funs old_funs =
    match find_common new_funs old_funs with
        | None -> ()
        | Some f -> error ("function " ^ f ^ " already exists")

let rec get_variables = function
    | Angel | Const _ | Proj _ -> []
    | Var(x) -> [x]
    | App(v1,v2) -> (get_variables v1) @ (get_variables v2)

let rec put_priority env = function
        | Angel -> Angel
        | Var(x) -> Var(x)
        | Proj(d,k)  when k<0 -> Proj(d,get_constant_priority env d)
        | Proj _  -> error "priority is already present"
        | Const(c,k)  when k<0 -> Const(c,get_constant_priority env c)
        | Const _ -> error "priority is already present"
        | App(v1,v2) -> App(put_priority env v1,put_priority env v2)

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression option * (term * term) list) list)
  : environment
  =

      (* TODO: I shouldn't look at the types of functions anywhere but should
       * keep accumulating constrainst about the functions type, and check that
       * they coincide with the given types at the very end *)

    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    (* gather the constraints on the functions by looking at a single clause *)
    let type_single_clause (f:var_name) (lhs_pattern,rhs_term:term*term) 
      : (var_name*type_expression) list
        =
        reset_fresh_variable_generator ();

        (* get function from LHS and check it is equal to f *)
        let _f = get_function_name lhs_pattern in
        if not (_f = f) then error ("function names " ^ f ^ " and " ^ _f ^ " do not match");

        (* get variables *)
        let lhs_vars = get_variables lhs_pattern in
        (match find_dup lhs_vars with
            | None -> ()
            | Some(x) -> error ("pattern is not linear: variable " ^ x ^ " appears more than once"));

        (* infer type of LHS, getting the type constraints on the variables (and the function itself) *)
        let infered_type_lhs, constraints_lhs = infer_type env lhs_pattern [] in

        (* infer type of RHS *)
        let infered_type_rhs, constraints = infer_type env rhs_term constraints_lhs in

        (* check that all the variables appearing on the RHS were also on the LHS *)
        List.iter (function x,t ->
                    if not (List.mem_assoc x constraints_lhs) && not (List.mem x new_functions)
                    then error (x ^ " is free!")
                  ) constraints;

        (* unify types of LHS and RHS *)
        let sigma = unify_type_mgu infered_type_rhs infered_type_lhs in

        (* the type of the RHS should be an instance of the type of the LHS *)
        (* oups: val s.Tail = ??? doesn't work with this... *)
        (* if not (infered_type_rhs = subst_type sigma infered_type_rhs) *)
        (* then error ("rhs and lhs do not have the same type"); *)

        let constraints = List.filter (function x,_ -> List.mem x new_functions) constraints in

        let constraints = List.rev_map (second (subst_type sigma)) constraints in

       constraints
    in


    let process_single_def (f:var_name) (clauses:(term*term) list)
      : (var_name*type_expression) list
      = 
        let constraints = List.fold_left
                        (fun constraints clause -> merge_constraints constraints (type_single_clause f clause))
                        []
                        clauses
        in

        (* check coverage *)
        if not (exhaustive env clauses)
        then error ("function " ^ f ^ " is not exhaustive");

        constraints
    in

    let process_all_defs defs =
        (* gather all the constraints on the functions *)
        let constraints = List.fold_left
                        (fun constraints def ->
                            let f, _, clauses = def in
                            merge_constraints constraints (process_single_def f clauses))
                        []
                        defs
        in
       constraints
    in
    let constraints : (var_name*type_expression) list = process_all_defs defs in

    let choose_type f t =
        reset_fresh_variable_generator ();
        let infered = instantiate_type (List.assoc f constraints) in
        match t with
        | None -> infered
        | Some t ->
            if (is_instance (instantiate_type t) infered)
            then t
            else error ("function " ^ f ^ "doesn't have appropriate type")
    in

    let functions = List.rev_map
        (function f,t,clauses -> (f,env.current_bloc+1,choose_type f t,List.map (function p,v -> put_priority env p, put_priority env v) clauses)) defs
    in

    { env with current_bloc = env.current_bloc+1; functions = functions @ env.functions }
