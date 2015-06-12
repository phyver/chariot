open Base
open Misc

(* check that all the type parameters of a definition are different *)
let check_uniqueness_parameters params =
    match find_dup params with
        | None -> ()
        | Some(TVar(x)) -> error ("parameter " ^ x ^ " appears more than once")
        | _ -> assert false

(* check that all new types are different *)
let check_new_types_different types =
    match find_dup types with
        | None -> ()
        | Some(t) -> error ("type " ^ t ^ " is defined more than once")

(* check that new types are different from old ones *)
let check_new_types_different_from_old new_types old_types =
    match find_common new_types old_types with
        | None -> ()
        | Some t -> error ("type " ^ t ^ " already exists")


(* check that all new constants are different *)
let check_new_consts_different consts =
    match find_dup consts with
        | None -> ()
        | Some(c) -> error ("constant " ^ c ^ " appears more than once")

(* check that new constants are different from old ones *)
let check_new_consts_different_from_old new_consts old_consts =
    match find_common new_consts old_consts with
        | None -> ()
        | Some t -> error ("constant " ^ t ^ " already exists")

(* check that all the types being defined only appear with exactly the same parameters
 * and the other types have the appropriate arity
 * check also that the types do not contain "static" parameters... *)
let rec check_parameters (env:environment) (defs:(type_name*type_expression list) list) = function
    | TVar(_) -> ()
    | Arrow(t1,t2) -> check_parameters env defs t1; check_parameters env defs t2
    | Data(t,params) ->
            begin
                try
                    if not (params = List.assoc t defs)
                    then error("type " ^ t ^ " should always use the same parameters in the definition")
                with Not_found ->
                    try
                        let a = get_type_arity env t in
                        if not (a = List.length params)
                        then error ("type " ^ t ^ " should has arity" ^ (string_of_int a))
                    with Not_found -> error ("type " ^ t ^ " doesn't exist")
            end

(* check that a type doesn't contain an instance of some other type *)
let check_doesnt_contain (t:type_expression) (x:type_name) =
    let rec check_doesnt_contain_aux = function
        | TVar(_) -> ()
        | Data(c,_) when x = c -> error ("type " ^ x ^ " appears in non strictly positive position")
        | Data(c,_) -> ()
        | Arrow(t1,t2) -> check_doesnt_contain_aux t1 ; check_doesnt_contain_aux t2
    in check_doesnt_contain_aux t

(* check that a type only appears strictly positively in another *)
let rec check_is_strictly_positive (t:type_expression) (x:type_name) =
    let rec check_is_strictly_positive_aux = function 
        | TVar(_) -> ()
        | Data _ -> ()
        | Arrow(t1,t2) -> check_doesnt_contain t1 x; check_is_strictly_positive_aux t2
    in check_is_strictly_positive_aux t

(* check that a type only appears strictly positively in all the arguments of a constant *)
let rec check_is_strictly_positive_arguments (t:type_expression) (x:type_name) =
    let rec check_is_strictly_positive_arguments_aux t = match t with
        | TVar(_) -> check_is_strictly_positive t x
        | Data _ -> check_is_strictly_positive t x
        | Arrow(t1,t2) -> check_is_strictly_positive t1 x; check_is_strictly_positive_arguments_aux t2
    in check_is_strictly_positive_arguments_aux t

(* check the type of a destructor: it should be of the form T(...) -> ...
 * where "T(...)" is the type being defined *)
let check_destructor (t:type_name) (d:const_name*type_expression) = match d with
    | (_,Arrow(Data(_t,_args), _)) when _t=t -> ()
    | (d,_) -> error ("destructor " ^ d ^ " doesn't appropriate type")

(* check the type of a constructor: it should be of the form ... -> T(...)
 * where "T(...)" is the type being defined *)
let rec check_constructor (t:type_name) (c:const_name*type_expression) = match c with
    | (_,Data(_t,_args)) when _t=t -> ()
    | (c,Arrow(_,_t)) -> check_constructor t (c,_t)
    | (c,_) -> error ("constructor " ^ c ^ " doesn't appropriate type")

let process_type_defs (env:environment)
                      (priority:priority)
                      (defs:(type_name * (type_expression list) * (const_name * type_expression) list) list)
  : environment
    =
    (* all the types, with parameters, that were mutually defined by this definition *)
    let new_types_with_params = List.rev_map (function (t,params,_) -> (t,params)) defs
    in

    (* the real priority of this bunch of mutual type definitions *)
    let priority = if (env.current_priority - priority) mod 2 = 0
                   then env.current_priority+2
                   else env.current_priority+1
    in

    (* we check that all the new types are different *)
    let new_types_without_params = List.rev_map (function (t,_,_) -> t) defs in
    check_new_types_different new_types_without_params;

    (* we check that new types are different from old types *)
    let old_types = List.rev_map (function (t,_,_,_) -> t) env.types in
    check_new_types_different_from_old new_types_without_params old_types;

    (* we check that all the new constants are different *)
    let new_consts = List.concat @$ List.rev_map (function (_,_,consts) -> List.rev_map fst consts) defs in
    check_new_consts_different new_consts;

    (* we check that all the new constants are different from the old ones *)
    let old_consts = List.map (function c,_,_ -> c) env.constants in
    check_new_consts_different_from_old new_consts old_consts;
    (* and the old functions *)
    let old_functions = List.map (function f,_,_,_ -> f) env.functions in
    check_new_consts_different_from_old new_consts old_functions;

    let process_single_type (tname:type_name)
                            (params:type_expression list)
                            (consts:(const_name*type_expression) list)
      : (type_name * type_name list * priority * const_name list) * (const_name * priority * type_expression) list
        =
        (* we check that all the parameters are different *)
        check_uniqueness_parameters params;

        (* we check that all instances of defined type appear with the same parameters *)
        List.iter (function _,t -> check_parameters env new_types_with_params t) consts;

        (* we check that the type comes from a strictly positive functor *)
        List.iter (function _,t -> check_is_strictly_positive_arguments t tname) consts;

        (* we check the shapes of types of constructors / destructors *)
        if priority mod 2 = 0
        then List.iter (check_destructor tname) consts
        else List.iter (check_constructor tname) consts;

        let params = List.map (function TVar(x) -> x | _ -> assert false) params in
        (tname, params, priority, List.map fst consts) , (List.map (function c,t -> c,priority, t) consts)

    in

    (* process all the definitions *)
    let types,consts = List.fold_left
                            (fun r def ->
                                let tname, params,consts = def in
                                let t,consts = process_single_type tname params consts in
                                let rtypes,rconsts = r in
                                ((t::rtypes), (consts@rconsts)))
                            ([],[])
                            defs
    in

    { env with  current_priority = priority;
                types = types @ env.types;
                constants = consts @ env.constants }
