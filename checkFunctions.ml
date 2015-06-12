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


let put_priorities (env:environment)
                   (defs:(var_name * bloc_nb * type_expression * (term * term) list) list)
  : (var_name * bloc_nb * type_expression * (term * term) list) list
  =

    (* specialize the type of a constant so that the corresponding (co)data type is t*)
    let specialize_constant t c =
          match t with
            | Data(tname,_,_) ->
                begin
                    let bdata = is_data env tname in
                    let tc = instantiate_type (if bdata then get_constructor_type env c else get_projection_type env c) in
                    let _t = if bdata
                             then get_result_type tc
                             else (match tc with Arrow(t,_) -> t | _ -> assert false)
                    in
                    let tau = unify_type_mgu t _t in
                    let tc = subst_type tau tc in
                    tc
                end
            | _ -> assert false
    in

    let rec get_subtypes acc = function
        | t when List.mem t acc -> acc
        | TVar _ -> acc
        | Data(tname,params,_) as t ->
            let stparams = List.concat (List.map (get_subtypes acc) params) in
            let consts = get_type_constants env tname in
            let acc=t::stparams@acc in
            let stconst = List.concat (List.map (fun c -> get_subtypes acc (specialize_constant t c)) consts) in
            stconst@acc
        | Arrow(t1,t2) -> (get_subtypes acc t1)@(get_subtypes acc t2)
      in

    (* check if a datatype occurs inside another type and return +1 / -1 *)
    let rec occur dt = function
        | t when dt=t -> -1
        | TVar _ -> +1
        | Arrow(t1,t2) -> min (occur dt t1) (occur dt t2)
        | Data(_,params,_) -> List.fold_left (fun r t -> min r (occur dt t)) 1 params
    in

    (* replace every _exact_ occurence of a datatype by another *)
    let rec replace_type t_before t_after = function
        | t when t=t_before -> t_after
        | Arrow(t1,t2) -> Arrow(replace_type t_before t_after t1, replace_type t_before t_after t2)
        | Data(t,params,p) -> Data(t,List.map (replace_type t_before t_after) params,p)
        | TVar(x) -> TVar(x)
    in

    (* find the constants corresponding to a type, and add the corresponding specialized type *)
    (* TODO: should I put better priority ? *)
    let find_consts t = match t with
          | Data(tname,_,_) ->
                let consts = get_type_constants env tname in
                List.map (fun c -> (c,is_data env tname,specialize_constant t c)) consts
          | _ -> assert false
    in

    (* add the real priority into the list of types (which is supposed to be sorted) and the types of constants *)
    let rec add_priorities_to_types k consts types = function
        | [] -> consts,types
        | (Data(tname,params,None) as t)::ts ->
                let p = is_data env tname in
                let newt,k = if p = (k mod 2 = 1)
                             then Data(tname,params,Some(k)),k+1
                             else Data(tname,params,Some(k+1)),k+2
                in
                let consts = List.map (function c,p,tc -> c,p,replace_type t newt tc) consts in
                let types = List.map (replace_type t newt) types in
                let ts = List.map (replace_type t newt) ts in
                add_priorities_to_types k consts types ts
        | _ -> assert false
    in

    (* add the real priorities to the constants themselves *)
    let rec add_priorities_to_consts = function
        | [] -> []
        | (c,bdata,t)::consts ->
              begin
                  let td = if bdata
                           then get_result_type t
                           else (match t with Arrow(t,_) -> t | _ -> assert false)
                  in
                  match td with
                      | Data(_,_,Some(p)) -> (c,p,t)::add_priorities_to_consts consts
                      | _ -> print_string "OUPS "; print_type td; print_newline(); assert false
              end
    in


    let local_types = List.sort occur (uniq (List.concat (List.map (function _,_,t,_ -> get_subtypes [] t) defs))) in
    let local_constants = List.concat (List.map find_consts local_types) in

    let local_constants, local_types = add_priorities_to_types 1 local_constants local_types local_types in
    print_list "" "types for " ", " "" print_string (List.map (function f,_,_,_ -> f) defs);
    print_list "" ": " ", " "\n" print_type local_types;

    let local_constants = add_priorities_to_consts local_constants in

    print_list "" "types for " ", " "" print_string (List.map (function f,_,_,_ -> f) defs);
    print_list "" ": " ", " "\n" print_type local_types;
    print_list "" "local constants: " ", " "\n\n\n" (function c,p,t -> print_string c; print_exp p; print_string ":"; print_type t; ) local_constants;

    (* let rec put_prioritie_term v t = *)
    (*     match v,t with *)
    (*       | Const(c,_), t -> find_const c t *)
    (* in *)



(*       let put_priorities_single_clause pattern,def = *)
(*           let fun_pattern = get_function_name pattern in *)
(*           let fun_type = List.assoc fun_pattern function_types in *)
(*           let args_pattern = get_args pattern in *)


(*           pattern,def *)





      defs


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
        let infered_type_lhs, constraints_lhs,sigma = infer_type env lhs_pattern [] [] in

        (* infer type of RHS *)
        let infered_type_rhs, constraints,sigma = infer_type env rhs_term constraints_lhs sigma in

        (* check that all the variables appearing on the RHS were also on the LHS *)
        List.iter (function x,t ->
                    if not (List.mem_assoc x constraints_lhs) && not (List.mem x new_functions)
                    then error (x ^ " is free!")
                  ) constraints;

        (* unify types of LHS and RHS *)

        let tau = unify_type_mgu infered_type_rhs infered_type_lhs in
        let sigma = tau @ (List.map (second (subst_type tau)) sigma) in

        message 4 (fun () ->
            print_string "infered type of pattern: ";
            print_type infered_type_lhs;
            print_string " and infered type of definition: ";
            print_type infered_type_rhs;
            print_string "\n\t\tgiving "; print_type (subst_type sigma infered_type_rhs); print_newline();
            print_string "types: ";
            print_list "none\n" "" "," "\n" (function x,t -> print_string ("'"^x^ "="); print_type t) sigma;
            print_string "\n\t\twith constraints ";
            print_list "none" "" " , " "" (function x,t -> print_string (x^":"); print_type t) constraints;
            );

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
        (function f,t,clauses -> (f,env.current_function_bloc+1,choose_type f t, clauses)) defs
    in

    put_priorities env functions;

    { env with current_function_bloc = env.current_function_bloc+1; functions = functions @ env.functions }
