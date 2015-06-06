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

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression option * (unit term * unit term) list) list)
  : environment
  =

      (* TODO: I shouldn't look at the types of functions anywhere but should
       * keep accumulating constrainst about the functions type, and check that
       * they coincide with the given types at the very end *)

    (* bloc number *)
    let new_bloc_nb = env.current_bloc + 1 in

    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    let new_functions_with_types = List.rev_map (function f,t,_ -> f,t) defs in

    let type_single_clause (f:var_name) (lhs_pattern,rhs_term:priority term*priority term) : type_expression =

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

        (* unify types of LHS and RHS *)
        let sigma = unify_type_mgu infered_type_rhs infered_type_lhs in

        (* the type of the RHS should be an instance of the type of the LHS *)
        if not (infered_type_rhs = subst_type sigma infered_type_rhs)
        then error ("rhs and lhs do not have the same type");

        (* we can now get the infered type of the function by looking at the constraints *)
        let infered_type_function = List.assoc f constraints in
        let infered_type_function = subst_type sigma infered_type_function in

        (* check that all the variables appearing on the RHS were also on the LHS *)
        List.iter (function x,t ->
                    if not (List.mem_assoc x constraints_lhs)
                    then begin
                        assert (not (x=f));
                        try
                            match List.assoc x new_functions_with_types with
                                | None -> ()
                                | Some tx -> if not (is_instance tx t)
                                             then error ("function " ^ x ^ " doesn't have appropriate type")
                        with Not_found -> error (x ^ " is free!")
                    end
                  ) constraints;
        infered_type_function
    in


    let process_single_def (f:var_name) (t:type_expression option) (clauses:(unit term*unit term) list)
      : var_name * bloc_nb * type_expression * function_clause list =

        (* put actual priorities in terms *)
        let clauses = List.map (function p,v -> put_priority env p, put_priority env v) clauses in

        reset_fresh_variable_generator();
        let t = match t with None -> TVar("type_" ^ f) | Some t -> t in
        let t = instantiate_type t in 

        let t = List.fold_left
                        (fun t clause ->
                            let t2 = type_single_clause f clause in
                            unify_type t2 t)
                        t
                        clauses
        in

        reset_fresh_variable_generator();
        let t = instantiate_type t in

        (* check coverage *)
        if not (exhaustive env clauses)
        then error ("function " ^ f ^ " is not exhaustive");

        (f, env.current_bloc, t, clauses)

    in

    let functions = List.map (function f,t,clauses -> process_single_def f t clauses) defs in

    { env with current_bloc = new_bloc_nb; functions = functions @ env.functions }
