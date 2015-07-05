open Base
open Misc
open State
open Pretty
open Typing
open CheckCoverage
open InferPriorities

(* check that a type is correct *)
let rec check_type env = function
    | TVar _ -> ()
    | Arrow(t1,t2) -> check_type env t1 ; check_type env t2
    | Data(tname,_) -> try ignore (is_inductive env tname) with Not_found -> error ("type " ^ tname ^ " doesn't exist")

(* check that all the functions are different *)
let check_uniqueness_functions funs =
    match find_dup funs with
        | None -> ()
        | Some(f) -> error ("function " ^ f ^ " is defined more than once")

let check_new_funs_different_from_old new_funs old_funs =
    match find_common new_funs old_funs with
        | None -> ()
        | Some f -> error ("function " ^ f ^ " already exists")

let rec get_variables (v:term) = match v with
    | Angel | Const _ | Proj _ -> []
    | Var(x) -> [x]
    | App(v1,v2) -> (get_variables v1) @ (get_variables v2)
    | Special v -> v.bot

let process_function_defs (env:environment)
                          (defs:(var_name * type_expression option * (term * term) list) list)
  : environment
  =

    (* TODO: I shouldn't look at the types of functions anywhere but should
     * keep accumulating constraints about the functions type, and check that
     * they coincide with the given types at the very end *)

    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    (* gather the constraints on the functions by looking at a single clause *)
    let type_single_clause (f:var_name) (lhs_pattern,rhs_term:pattern*term) 
      : (var_name*type_expression) list * type_expression list
      =
        (* get function from LHS and check it is equal to f *)
        let _f = get_function_name lhs_pattern in
        if not (_f = f) then error ("function names " ^ f ^ " and " ^ _f ^ " do not match");

        (* get variables *)
        let lhs_vars = get_variables lhs_pattern in
        (match find_dup lhs_vars with
            | None -> ()
            | Some(x) -> error ("pattern is not linear: variable " ^ x ^ " appears more than once"));

        (* infer type and gather datatypes *)
        let constraints,datatypes = infer_type_clause env lhs_pattern rhs_term in

        (* remove constraints on pattern variables *)
        let constraints = List.filter (function x,_ -> (x = f) || (not (List.mem x lhs_vars))) constraints in

        (* check that all the variables appearing on the RHS were also on the LHS *)
        List.iter (function x,t ->
                    if not (List.mem x new_functions)
                    then error (x ^ " is free!")
                  ) constraints;

       constraints,datatypes
    in

    let rec process_defs constraints datatypes = function
        | [] -> constraints, datatypes
        | (f,k,[])::defs -> process_defs constraints datatypes defs
        | (f,k,clause::clauses)::defs ->
            let rconstraints,rdatatypes = process_defs constraints datatypes ((f,k,clauses)::defs) in
            let constraints,datatypes = type_single_clause f clause in
            let constraints, sigma = merge_constraints rconstraints constraints in
            let datatypes = uniq (List.map (subst_type sigma) datatypes @ rdatatypes) in
            (constraints , datatypes)
    in

    let constraints,datatypes = process_defs [] [] defs in

    if not (option "dont_check_completeness")
    then
        List.iter (function f,_,clauses ->
                if not (exhaustive env clauses)
                then error ("function " ^ f ^ " is not complete"))
            defs;

    (* choose the substitution that will make the final type of the definition a good choice:
     *   - either use the given type
     *   - or rename the type variables
     *)
    let choose_type f t =
        let infered = List.assoc f constraints in
        match t with
        | None ->
            reset_fresh_variable_generator [];
            let infered_new = instantiate_type infered in
            unify_type_mgu infered_new infered (* don't swap arguments... *)
        | Some t ->
            check_type env t;
            let sigma = unify_type_mgu t infered in
            if (t = subst_type sigma t)
            then sigma
            else error ("function " ^ f ^ " doesn't have appropriate type")
    in

    (* FIXME: I need to add the actual type of the function into the datatypes *)

    (* let functions = List.rev_map *)
    (*     (function f,t,clauses -> (f,env.current_function_bloc+1,subst_type (choose_type f t) (List.assoc f constraints), clauses)) defs *)
    (* in *)

    let functions, datatypes =
        List.fold_left (fun r f ->
            let functions,datatypes = r in
            let f,t,clauses = f in
            let sigma = choose_type f t in
            (f,env.current_function_bloc+1,subst_type sigma (List.assoc f constraints),clauses)::functions , List.map (subst_type sigma) datatypes
        )
        ([],datatypes)
        defs
    in

    let functions = if not (option "dont_use_priorities")
                    then infer_priorities env functions datatypes
                    else functions
    in

    { env with current_function_bloc = env.current_function_bloc+1; functions = functions @ env.functions }
