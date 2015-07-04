open Misc
open Base
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

(* gather all the subtype of a type, together with the subtypes of the types of
 * the corresponding constructors and destructors *)
let get_subtypes (env:environment)
                 (t:type_expression)
  : type_expression list
  =
    let rec get_subtypes_aux acc = function
        | t when List.mem t acc -> acc
        | TVar _ -> acc
        | Data(tname,params) as t ->
            let stparams = List.concat (List.map (get_subtypes_aux acc) params) in
            let consts = get_type_constants env tname in
            let acc=t::stparams@acc in
            let stconst = List.concat (List.map (fun c -> get_subtypes_aux acc (specialize_constant env t c)) consts) in
            stconst@acc
        | Arrow(t1,t2) -> (get_subtypes_aux acc t1)@(get_subtypes_aux acc t2)
    in
    get_subtypes_aux [] t

(* gather all the subtypes of a list of types *)
let get_subtypes_list env ts
  = uniq (List.concat (List.map (get_subtypes env) ts))



(* check if two types are equal, up renaming of free variables *)
let equal_type t1 t2 = (is_instance t1 t2) && (is_instance t2 t1)


(* check if type t1 should be defined earlier than type t2, ie if the priority
 * of t1 should be less than the priority of t2 *)
let earlier_type env t1 t2 =
    match t1,t2 with
        | t1,t2 when t1=t2 -> false
        | Data(tname1,_),Data(tname2,_) ->
            let consts = get_type_constants env tname2 in
            let consts_types = List.map (fun c -> specialize_constant env t2 c) consts in
            let types = List.concat (List.map extract_atomic_types consts_types) in
            List.mem t1 types
        | Data _, TVar x2 -> true
        | TVar x1, Data _ -> false
        | TVar x1, TVar x2 -> false
        | _,_ -> assert false

let compute_edges env ts =
    let rec edges_aux ts1 ts2 =
        match ts1,ts2 with
            | _,[] -> []
            | [],_::ts2 -> edges_aux ts ts2
            | t1::ts1,t2::ts2 ->
                    if earlier_type env t1 t2
                    then (t1,t2)::(edges_aux ts1 (t2::ts2))
                    else edges_aux ts1 (t2::ts2)
    in
    edges_aux ts ts

(* see http://stackoverflow.com/questions/4653914/topological-sort-in-ocaml *)
let order_types env ts =
    let nodes = ts in
    let edges = compute_edges env nodes in

    let rec explore path seen n =
        if List.mem n path then seen else (* then raise (Invalid_argument "order_types: loop") else *) (* deal correctly with loops *)
        if List.mem n seen then seen else
        let path = n::path in
        let next = List.map snd (List.filter (function n1,_ -> n1=n) edges) in
        let seen = List.fold_left (explore path) seen next in
        n::seen
    in

    List.rev (List.fold_left (fun seen n -> explore [] seen n) [] nodes)


(* check if a datatype occurs inside another type and return +1 / -1 *)
let rec compare_occur (dt:type_expression)
                      (t:type_expression)
 : int
 = match t with
    | t when equal_type dt t -> -1
    | TVar _ -> +1
    | Data(_,params) -> List.fold_left (fun r t -> min r (compare_occur dt t)) 1 params
    | Arrow(t1,t2) -> assert false


let infer_priorities (env:environment)
                     (defs:(var_name * bloc_nb * type_expression * (term * term) list) list)
                     (datatypes:type_expression list)
  : (var_name * bloc_nb * type_expression * (term * term) list) list
  =
    let rec add_priorities k acc = function
        | [] -> acc
        | (Data(tname,_) as t)::ts ->
            if (is_inductive env tname) = (k mod 2 = 0)
            then add_priorities (k+1) ((t,k+1)::acc) ts
            else add_priorities (k+2) ((t,k)::acc) ts
        | _ -> assert false
    in


    let local_types = get_subtypes_list env datatypes in
    let local_types = List.rev (order_types env local_types) in
    let local_types = add_priorities 1 [] local_types in
    let functions_types = List.map (function f,_,t,_ -> f,t) defs in

    let get_priority t =
        let rec aux = function
            | [] -> assert false
            | (_t,_p)::_ when equal_type _t t -> _p  (* FIXME: we can probably use equality of types *)
            | _::l -> aux l
        in
        aux local_types
    in
    (* let get_priority t = print_string "looking for type "; print_type t; print_list "" "in [" "," "]\n" print_type (List.map fst local_types); get_priority t in *)

    (* print_list "" "\ntypes for " ", " "" print_string (List.map (function f,_,_,_ -> f) defs); *)
    (* print_list "" "local types: " ", " "\n" (function t,k -> print_type t; print_exp k) local_types; *)
    (* print_list "" "functions types: " ", " "\n\n\n" (function f,t -> print_string f; print_string ":"; print_type t ) functions_types; *)


    let get_function_type f =
        let rec aux = function
            | [] -> raise Not_found
            | (_f,_,t,_)::_ when _f=f -> t
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
        let infered_type_lhs, constraints_lhs,sigma,datatypes = infer_type env pattern functions_types [] [] in

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

        (* print_string "*************\n"; *)
        (* print_term pattern; *)
        (* print_string " = "; *)
        (* print_term def; *)
        (* print_string "\n*************\n"; *)

        pattern, def

    in List.map (function f,k,t,clauses -> f,k,List.assoc f functions_types,List.map put_priorities_single_clause clauses) defs

