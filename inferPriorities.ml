open Misc
open Base
open Typing
open Pretty

(* specialize the type of a constant so that the corresponding (co)data type is t*)
let specialize_constant (env:environment)
                        (t:type_expression)
                        (c:const_name)
 : type_expression
 = match t with
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
        | Data(tname,params,_) as t ->
            let stparams = List.concat (List.map (get_subtypes_aux acc) params) in
            let consts = get_type_constants env tname in
            let acc=t::stparams@acc in
            let stconst = List.concat (List.map (fun c -> get_subtypes_aux acc (specialize_constant env t c)) consts) in
            stconst@acc
        | Arrow(t1,t2) -> (get_subtypes_aux acc t1)@(get_subtypes_aux acc t2)
    in
    get_subtypes_aux [] t

let equal_type t1 t2 = (is_instance t1 t2) && (is_instance t2 t1)

(* check if a datatype occurs inside another type and return +1 / -1 *)
let rec compare_occur (dt:type_expression)
                      (t:type_expression)
 : int
 = match t with
    | t when equal_type dt t -> -1
    | TVar _ -> +1
    | Data(_,params,_) -> List.fold_left (fun r t -> min r (compare_occur dt t)) 1 params
    | Arrow(t1,t2) -> assert false

(* replace every **exact** occurence of a datatype by another inside a type *)
let rec replace_datatype (t_before:type_expression)
                         (t_after:type_expression)
                         (t:type_expression)
 : type_expression
 = match t with
    | t when t=t_before -> t_after
    | Arrow(t1,t2) -> Arrow(replace_datatype t_before t_after t1, replace_datatype t_before t_after t2)
    | Data(t,params,p) -> Data(t,List.map (replace_datatype t_before t_after) params,p)
    | TVar(x) -> TVar(x)


let infer_priorities (env:environment)
                     (defs:(var_name * bloc_nb * type_expression * (term * term) list) list)
  : (var_name * bloc_nb * type_expression * (term * term) list) list
  =
    (* find the constants corresponding to a type, and add the corresponding specialized type
     * return also a boolean to indicate if each constant is a constructor or a projection *)
    (* TODO: rename *)
    let find_consts (env:environment)
                    (t:type_expression)
     : (const_name * bool * type_expression) list
     = match t with
        | Data(tname,_,_) ->
            let consts = get_type_constants env tname in
            List.map (fun c -> (c,is_data env tname,specialize_constant env t c)) consts
        | _ -> assert false
    in

    (* add the priorities into the types:
     *     - in the types of constants
     *     - in the types of functions
     *     - in the types themselves *)
    let rec add_priorities_to_types k types consts functions_types = function
        | [] -> consts,types,functions_types
        | (Data(tname,params,None) as t)::rest ->
                let newt,k = if (is_data env tname) = (k mod 2 = 1)
                             then Data(tname,params,Some(k)),k+1
                             else Data(tname,params,Some(k+1)),k+2
                in
                let types = List.map (replace_datatype t newt) types in
                let consts = List.map (function c,p,tc -> c,p,replace_datatype t newt tc) consts in
                let functions_types = List.map (second (replace_datatype t newt)) functions_types in
                let rest = List.map (replace_datatype t newt) rest in
                add_priorities_to_types k types consts functions_types rest
        | _ -> assert false
    in

    (* add the priority to a constant *)
    let rec add_priority_to_const ((c,bdata,t):const_name*bool*type_expression)
     : const_name*int*type_expression
     = let td = if bdata
               then get_result_type t
               else get_first_arg_type t
       in
       match td with
           | Data(_,_,Some(p)) -> (c,p,t)
           | _ -> assert false
    in

    let local_types = List.sort compare_occur (uniq (List.concat (List.map (function _,_,t,_ -> get_subtypes env t) defs))) in
    let local_constants = List.concat (List.map (find_consts env) local_types) in
    let functions_types = List.map (function f,_,t,_ -> f,t) defs in

    let local_constants, local_types, functions_types = add_priorities_to_types 1 local_types local_constants functions_types local_types in
    let local_constants = List.map add_priority_to_const local_constants in

    print_list "" "types for " ", " "" print_string (List.map (function f,_,_,_ -> f) defs);
    print_list "" ": " ", " "\n" print_type local_types;
    print_list "" "local constants: " ", " "\n" (function c,p,t -> print_string c; print_exp p; print_string ":"; print_type t; ) local_constants;
    print_list "" "functions types: " ", " "\n\n\n" (function f,t -> print_string f; print_string ":"; print_type t ) functions_types;


    let get_constructor_type_priority c t =
        let rec aux = function
            | [] -> raise Not_found
            | (_c,p,_t)::_ when _c=c && equal_type (get_result_type _t) t -> _t,p
            | _::cs -> aux cs
        in aux local_constants
    in
    let get_projection_type_priority d t =
        let rec aux = function
            | [] -> raise Not_found
            | (_d,p,_t)::_ when _d=d && get_first_arg_type _t=t -> _t,p
            | _::cs -> aux cs
        in aux local_constants
    in
    let get_function_type f =
        let rec aux = function
            | [] -> raise Not_found
            | (_f,_,t,_)::_ when _f=f -> t
            | _::fs -> aux fs
        in aux defs
    in
    let rec extract_args_type t = match t with
        | Data _ | TVar _ -> []
        | Arrow (t1,t2) -> t1::(extract_args_type t2)
    in

    (* let get_priority c t = *)
    (*     let rec aux = function *)
    (*         | [] -> assert false *)
    (*         | (_c,_p,_t)::_ when _c=c && _t=t -> _p *)
    (*         | _::l -> aux l *)
    (*     in *)
    (*     aux local_constants *)
    (* in *)

    let rec check_type_and_put_priorities (v:term) (t:type_expression option)
      : term * type_expression option
      =
        match get_head v , get_args v with
            | Angel,args -> v,t
            | Var(f),args ->
                begin
                    try
                        let tf = List.assoc f functions_types in
                        let targs = extract_args_type tf in
                        let ttargs,trest = combine_suffix args targs in
                        let args = List.map (function v,t -> fst (check_type_and_put_priorities v (Some t))) ttargs in
                        let trest = List.fold_right (fun t r -> Arrow(t,r)) trest (get_result_type tf) in
                        app (Var(f)) args, Some trest

                    with Not_found -> app (Var(f)) (List.map (fun arg -> fst (check_type_and_put_priorities arg None)) args), None
                end
            | Const(c,None),args ->
                begin
                    match t with
                        | None -> v,t
                        | Some t ->
                            try
                                let tc = get_result_type t in
                                let tc,p = get_constructor_type_priority c tc in
                                let targs = extract_args_type tc in
                                let ttargs,_ = combine_suffix args targs in
                                let args = List.map (function v,t -> fst (check_type_and_put_priorities v (Some t))) ttargs in
                                app (Const(c,Some p)) args, Some t
                            with Not_found -> assert false
                end
            | Proj(d,None),args ->
                begin
                    try
                        let arg = List.hd args in
                        let arg,td = check_type_and_put_priorities arg None in
                        match td with
                            | None -> v,t
                            | Some td ->
                                try
                                    let td,p = get_projection_type_priority d td in
                                    let targs = extract_args_type td in
                                    let ttargs,trest = combine_suffix (List.tl args) (List.tl targs) in
                                    let args = List.map (function v,t -> fst (check_type_and_put_priorities v (Some t))) ttargs in
                                    let trest = List.fold_right (fun t r -> Arrow(t,r)) trest (get_result_type td) in
                                    app (Proj(d,Some p)) (arg::args), Some trest
                                with Not_found -> assert false
                    with Exit -> v,t
                end
            | App _,_ -> assert false
            | _ -> assert false
    in


    let put_priorities_single_clause clause =
        let pattern,def = clause in

        (* infer type of LHS, getting the type constraints on the variables (and the function itself) *)
        let infered_type_lhs, constraints_lhs,sigma = infer_type env pattern functions_types [] in

        (* infer type of RHS *)
        let infered_type_rhs, constraints,sigma = infer_type env def constraints_lhs sigma in

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


        let pattern = fst (check_type_and_put_priorities pattern (Some t)) in
        let def = fst (check_type_and_put_priorities def (Some t)) in

        (* print_string "*************\n"; *)
        (* print_term pattern; *)
        (* print_string " = "; *)
        (* print_term def; *)
        (* print_string "\n*************\n"; *)

        pattern, def

    in List.map (function f,k,t,clauses -> f,k,List.assoc f functions_types,List.map put_priorities_single_clause clauses) defs

