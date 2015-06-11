open Misc
open Base
open Typing
open Pretty

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
    let rec add_priorities_to_types k consts types functions_types = function
        | [] -> consts,types,functions_types
        | (Data(tname,params,None) as t)::ts ->
                let p = is_data env tname in
                let newt,k = if p = (k mod 2 = 1)
                             then Data(tname,params,Some(k)),k+1
                             else Data(tname,params,Some(k+1)),k+2
                in
                let consts = List.map (function c,p,tc -> c,p,replace_type t newt tc) consts in
                let types = List.map (replace_type t newt) types in
                let functions_types = List.map (second (replace_type t newt)) functions_types in
                let ts = List.map (replace_type t newt) ts in
                add_priorities_to_types k consts types functions_types ts
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
    let functions_types = List.map (function f,_,t,_ -> f,t) defs in

    let local_constants, local_types, functions_types = add_priorities_to_types 1 local_constants local_types functions_types local_types in
    let local_constants = add_priorities_to_consts local_constants in

    print_list "" "types for " ", " "" print_string (List.map (function f,_,_,_ -> f) defs);
    print_list "" ": " ", " "\n" print_type local_types;
    print_list "" "local constants: " ", " "\n" (function c,p,t -> print_string c; print_exp p; print_string ":"; print_type t; ) local_constants;
    print_list "" "functions types: " ", " "\n\n\n" (function f,t -> print_string f; print_string ":"; print_type t ) functions_types;

    let get_constructor_type_priority c t =
        let rec aux = function
            | [] -> raise Not_found
            | (_c,p,_t)::_ when _c=c && get_result_type _t=t -> _t,p
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

    (* NOTE: we probably don't need to put priorities on constructors that do not have a variable below them... *)
    let get_priority c t =
        let rec aux = function
            | [] -> assert false
            | (_c,_p,_t)::_ when _c=c && _t=t -> _p
            | _::l -> aux l
        in
        aux local_constants
    in

    let rec get_f_args v args = match v with
        | Var _ -> v,args
        | Const _ -> v,args
        | Proj _ -> v,args
        | Angel -> v,args
        | App(v,arg) -> get_f_args v (arg::args)
    in

    let rec type_and_put_priorities (v:term) (t:type_expression option)
      : term * type_expression option
      =
(match t with None -> (print_string "type_and_put_priorities for ";print_term v; print_string ":??"; print_newline())
    | Some t -> (print_string "type_and_put_priorities for ";print_term v; print_string ":"; print_type t; print_newline()));

        match get_f_args v [] with
            | Angel,args -> v,t
            | Var(f),args ->
                begin
                    try
                        let tf = List.assoc f functions_types in
                        let targs = extract_args_type tf in
                        let ttargs,trest = combine_suffix args targs in
                        let args = List.map (function v,t -> fst (type_and_put_priorities v (Some t))) ttargs in
                        List.fold_left (fun r t -> App(r,t)) (Var(f)) args, t

                    with Not_found -> v,t      (* if f isn't one of the function being defined,
                                                * we don't put priorities (it's going to disappear
                                                * in the SCT anyway) *)
                end
            | Const(c,None),args ->
                begin
                    try
                        match t with
                        | None -> v,t
                        | Some t ->
                            let tc = get_result_type t in
                            print_string "oops "; print_term v; print_string ":"; print_type t; print_newline(); 
                            let tc,p = get_constructor_type_priority c tc in
                            let targs = extract_args_type tc in
                            let ttargs,trest = combine_suffix args targs in
                            List.fold_left (fun r t -> App(r,t)) (Const(c,Some p)) args, Some t
                    with Not_found -> assert false
                end
            | Proj(d,None),args ->
                begin
                    try
                        let arg = List.hd args in
                        let arg,td = type_and_put_priorities (List.hd args) t in
                        match td with
                        | None -> v,t
                        | Some td ->
                            try
                                let td,p = get_projection_type_priority d td in

                                let targs = extract_args_type td in
                                let ttargs,trest = combine_suffix args targs in
                                let trest = List.fold_left (fun r t -> Arrow(r,t)) (List.hd trest) (List.tl trest) in
                                let args = List.map (function v,t -> fst (type_and_put_priorities v (Some t))) ttargs in
                                List.fold_left (fun r t -> App(r,t)) (Proj(d,Some p)) args, Some trest
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

        let function_types = List.map (function f,_,t,_ -> f,t) defs in

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

        print_string "for\t\t";
        print_term pattern ; print_string " = "; print_term def; print_newline();
        print_string "constraints: "; print_list "none" "" " , " "\n\n" (function x,t -> print_string (x^":"); print_type t) constraints;


        print_string "type rhs:" ;print_type infered_type_rhs; print_newline();
        print_string "type lhs:" ;print_type infered_type_lhs; print_newline();
        let t = subst_type sigma infered_type_lhs in
        print_string "type t:" ;print_type t; print_newline();


        let pattern = fst (type_and_put_priorities pattern (Some t)) in
        let def = fst (type_and_put_priorities def (Some t)) in

        print_string "*************\n";
        print_term pattern;
        print_string " = ";
        print_term def;
        print_string "\n*************\n";

        pattern, def

    in List.map (function f,k,t,clauses -> f,k,t,List.map put_priorities_single_clause clauses) defs

