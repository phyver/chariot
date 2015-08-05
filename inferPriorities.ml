open Misc
open Base
open State
open Typing
open Pretty

(* specialize the type of a constant so that the corresponding (co)data type is t*)
let specialize_constant (env:environment)
                        (t:type_expression)
                        (c:const_name)
  : type_expression
  =
     match t with
      | Data(tname,_) ->
          begin
              reset_fresh_variable_generator [t];
              let tc = instantiate_type (get_constant_type env c) in
              let _t = if is_inductive env tname
                       then get_result_type tc
                       else get_first_arg_type tc
              in
              let tau = unify_type_mgu t _t in
              let tc = subst_type tau tc in
              tc
          end
      | _ -> raise (Invalid_argument "specialize_constant: not a (co)data type")

let find_types_priorities env ts
  =
    let nodes = ts in

    (* wether a type appears inside another *)
    let rec subtype_of t1 t2
      = match t1,t2 with
            | t1,t2 when t1=t2 -> false
            | t1,Data(tname2,params2) -> List.mem t1 params2 || List.exists (subtype_of t1) params2
            | Data _, TVar _ | TVar _, TVar _ -> false
            | _,_ -> assert false
    in

    let graph = List.map (fun x -> x,List.filter (subtype_of x) nodes) nodes in

    (* see http://stackoverflow.com/questions/4653914/topological-sort-in-ocaml *)
    let rec dfs path seen n =
        if List.mem n path then raise (Invalid_argument "dfs: found loop") else
        if List.mem n seen then seen else
        let path = n::path in
        let next = List.assoc n graph in
        let seen = List.fold_left (dfs path) seen next in
        n::seen
    in

    (* order the nodes by dfs, to get subtypes later in the list *)
    let nodes = List.fold_left (fun seen n -> dfs [] seen n) [] nodes
    in

    (* computes the priority for type t
     *   - acc is the list of types with priorities already computed
     *   - on_hold contains the types whose priority has been delayed, pending some priorities for some other types
     *
     * NOTE: we need to consider atomic types first and composite types later:
     * this ensures that Rose trees (and similar mutual types) get appropriate priorities:
     *   rtree needs list(rtree)
     * but if we start by computing the priority of list(rtree), we will assign priority 1 to rtree and 3 to list(rtree)
     *)
    let rec order t acc on_hold
      =
        try List.assoc t acc, acc
        with Not_found ->
            match t with
                | Data(tname,params) ->
                    let consts = get_type_constants env tname in
                    let type_consts = uniq (List.concat (List.map (fun c -> extract_datatypes (specialize_constant env t c)) consts)) in
                    let n,acc = List.fold_left
                                    (fun nacc _t ->
                                        if _t = t || List.mem _t on_hold then nacc else
                                        let n,acc = nacc in
                                        let _n,_acc = order _t acc (t::on_hold) in
                                        (max n _n), _acc
                                    )
                                    (0,acc)
                                    type_consts
                    in
                    if is_inductive env tname = odd n
                    then if (option "squash_priorities") then (n, (t,n)::acc) else (n+2, (t,n+2)::acc)
                    else (n+1, (t,n+1)::acc)
                | _ -> assert false
    in
    let datatypes = List.filter (function Data _ -> true | _ -> assert false) nodes in

    List.fold_left (fun acc t -> let n,acc = order t acc [] in acc) [] datatypes

let infer_priorities (env:environment)
                     (defs:(var_name * type_expression * (term * term) list) list)
                     (datatypes:type_expression list)
  : (var_name * type_expression * (term * term) list) list
  =

    let local_types = datatypes in
    (* msg "local types: %s" (string_of_list " , " string_of_type local_types); *)
    (* let local_types = find_types_priorities env local_types in *)
    (* let local_types = find_types_priorities_graph env local_types in *)
    let local_types = find_types_priorities env local_types in
    (* msg "priorities: %s" (string_of_list " , " (function t,p -> (string_of_type t) ^ ":" ^ (string_of_int p)) local_types); *)
    let functions_types = List.map (function f,t,_ -> f,t) defs in

    let get_priority t =
        let rec aux = function
            | [] -> assert false
            | (_t,_p)::_ when equal_type _t t -> _p
            | _::l -> aux l
        in
        aux local_types
    in

    (* print_list "" "\ntypes for " ", " "" print_string (List.map (function f,_,_,_ -> f) defs); *)
    (* print_list "" "local types: " ", " "\n" (function t,k -> print_type t; print_exp k) local_types; *)
    (* print_list "" "functions types: " ", " "\n\n\n" (function f,t -> print_string f; print_string ":"; print_type t ) functions_types; *)

    let get_function_type f =
        let rec aux = function
            | [] -> raise Not_found
            | (_f,t,_)::_ when _f=f -> t
            | _::fs -> aux fs
        in aux defs
    in

    let rec check_type_and_put_priorities (vars:(var_name*type_expression) list) (v:term) (t:type_expression option)
      : term * type_expression option
      =
        match get_head v , get_args v with
            | Angel,args -> v,t
            | Var(f),args ->
                begin
                    (* we can infer the type, the argument "t" isn't used in this case *)
                    (* FIXME: check that if t is Some(t), this t is the same as the infered type? *)
                    try
                        let tf = List.assoc f vars in
                        let targs = get_args_type tf in
                        let ttargs,trest = combine_suffix args targs in
                        let args = List.map (function v,t -> fst (check_type_and_put_priorities vars v (Some t))) ttargs in
                        let trest = List.fold_right (fun t r -> Arrow(t,r)) trest (get_result_type tf) in
                        app (Var(f)) args, Some trest

                    with Not_found -> app (Var(f)) (List.map (fun arg -> fst (check_type_and_put_priorities vars  arg None)) args), None
                end
            | Const(c,None),args ->
                begin
                    match t with
                        (* if we need to infer the type of a constructor, it
                         * means this constructor is not in "pattern" position.
                         * It won't be used by the termination checker and we
                         * do not need to put a prority *)
                        (* FIXME: is that right? *)
                        | None -> v,t
                        | Some t ->
                            try
                                let tc = get_result_type t in
                                (* print_string "looking for type "; print_type tc; print_newline(); *)
                                let p = get_priority tc in
                                let targs = get_args_type (specialize_constant env tc c) in
                                let ttargs,_ = combine_suffix args targs in
                                let args = List.map (function v,t -> fst (check_type_and_put_priorities vars  v (Some t))) ttargs in
                                app (Const(c,Some p)) args, Some t
                            with Not_found -> assert false
                end
            | Proj(d,None),args ->
                begin
                    try
                        let arg = List.hd args in
(* print_string "arg = "; print_term arg; print_newline(); *)
                        let arg,td = check_type_and_put_priorities vars arg None in
                        match td with
                            | None ->
(* print_string ("need to infer type for proj " ^ d ^ "\n"); *)
                                    v,t
                            | Some td ->
                                try
                                    (* print_string ("proj " ^ d ^ " of type "); print_type td; print_newline(); *)
                                    let p = get_priority td in
                                    let targs = get_args_type (specialize_constant env td d) in
                                    let ttargs,trest = combine_suffix (List.tl args) (List.tl targs) in
                                    let args = List.map (function v,t -> fst (check_type_and_put_priorities vars v (Some t))) ttargs in
                                    let trest = List.fold_right (fun t r -> Arrow(t,r)) trest (get_result_type td) in
                                    app (Proj(d,Some p)) (arg::args), Some trest
                                with Not_found -> assert false
                    with Exit -> v,t
                end
            | App _,_ -> assert false
            | _ -> print_term v; print_string "\nOOPS\n"; assert false
    in

    let put_priorities_single_clause clause =
        let pattern,def = clause in

        (* infer type of LHS, getting the type constraints on the variables (and the function itself) *)
        reset_fresh_variable_generator (List.map snd functions_types);
        let infered_type_lhs, constraints_lhs,sigma,datatypes = infer_type { env with functions=[] } pattern functions_types [] [] in

        (* infer type of RHS *)
        let infered_type_rhs, constraints,sigma,datatypes = infer_type env def constraints_lhs sigma datatypes in

        let tau = unify_type_mgu infered_type_rhs infered_type_lhs in
        let sigma = tau @ (List.map (second (subst_type tau)) sigma) in

        let constraints = List.rev_map (second (subst_type sigma)) constraints in

        (* let function_types = List.map (function f,_,t,_ -> f,t) defs in *)

        let sigma = List.fold_left
            (fun sigma xt ->
                let x,tx = xt in
                try
                    let tau = unify_type_mgu tx (get_function_type x) in
                    tau @ (List.map (second (subst_type tau)) tau)
                with Not_found -> sigma
            )
            sigma
            constraints
        in

        let constraints = List.map (second (subst_type sigma)) constraints in

        (* print_string "for\t\t"; *)
        (* print_term pattern ; print_string " = "; print_term def; print_newline(); *)
        (* print_string "constraints: "; print_list "none" "" " , " "\n\n" (function x,t -> print_string (x^":"); print_type t) constraints; *)


        (* print_string "type rhs:" ;print_type infered_type_rhs; print_newline(); *)
        (* print_string "type lhs:" ;print_type infered_type_lhs; print_newline(); *)
        let t = subst_type sigma infered_type_lhs in
        (* print_string "type t:" ;print_type t; print_newline(); *)

        let pattern = fst (check_type_and_put_priorities (functions_types @ constraints) pattern (Some t)) in
        let def = fst (check_type_and_put_priorities (functions_types @ constraints) def (Some t)) in

        pattern, def

    in List.map (function f,t,clauses -> f,List.assoc f functions_types,List.map put_priorities_single_clause clauses) defs

