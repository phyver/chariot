open Base
open Misc

(* look for a value with at least two occurences *)
let uniq l =
    let rec aux = function
        | [] -> None
        | [a] -> None
        | a::b::_ when a=b -> Some a
        | a::b::l -> aux (b::l)
    in aux (List.sort compare l)

(* look for a value that appears in the two lists *)
let common l1 l2 =
    let rec aux l1 l2 = match l1,l2 with
        | [],_ | _,[] -> None
        | x1::_,x2::_ when x1=x2 -> Some x1
        | x1::l1,x2::_ when x1<x2 -> aux l1 l2
        | x1::_,x2::l2 (*when x1>x2*) -> aux l1 l2
    in aux (List.sort compare l1) (List.sort compare l2)

(* check that all the type parameters of a definition are different *)
let check_uniqueness_parameters params =
    match uniq params with
        | None -> ()
        | Some(TVar(true,x)) -> raise @$ Error ("*** parameter " ^ x ^ " appears more than once")
        | _ -> assert false

(* check that all new types are different *)
let check_new_types_different types =
    match uniq types with
        | None -> ()
        | Some(t) -> raise @$ Error ("*** type " ^ t ^ " is defined more than once")

(* check that new types are different from old ones *)
let check_new_types_different_from_old new_types old_types =
    match common new_types old_types with
        | None -> ()
        | Some t -> raise @$ Error ("*** type " ^ t ^ " already exists")


(* check that all new constants are different *)
let check_new_consts_different consts =
    match uniq consts with
        | None -> ()
        | Some(c) -> raise @$ Error ("*** constant " ^ c ^ " appears more than once")

(* check that new constants are different from old ones *)
let check_new_consts_different_from_old new_consts old_consts =
    match common new_consts old_consts with
        | None -> ()
        | Some t -> raise @$ Error ("*** constant " ^ t ^ " already exists")

(* While parsing, we don't know if nullary types correspond to type parameters or other type constants.
 * The Parser uses the "TVar" constructor with the boolean field set to false for those...
 * We can later replace them by a type parameter (if it is one), or a nullary type constant.
 * (Checking that the nullary type constant actually exists is done later. *)
let rec replace_unknown_TVar params = function
    | Arrow(t1,t2) -> Arrow(replace_unknown_TVar params t1, replace_unknown_TVar params t2)
    | TVar(true,x) -> TVar(true,x)
    | Data(t, args) -> Data(t, List.map (replace_unknown_TVar params) args)
    | TVar(false,x) -> if List.mem (TVar(true,x)) params
                then TVar(true,x)
                else Data(x, [])

(* check that all the types being defined only appear with exactly the same parameters
 * and the other types have the appropriate arity *)
let rec check_parameters (env:environment) (defs:(type_name*type_expression list) list) = function
    | TVar(true,_) -> ()
    | Arrow(t1,t2) -> check_parameters env defs t1; check_parameters env defs t2
    | Data(t,params) ->
            begin
                try
                    if not (params = List.assoc t defs)
                    then raise @$ Error("*** type " ^ t ^ " should always use the same parameters in the definition")
                with Not_found ->
                    try
                        let a = get_arity t env in
                        if not (a = List.length params)
                        then raise @$ Error("*** type " ^ t ^ " should has arity" ^ (string_of_int a))
                    with Not_found -> raise @$ Error("*** type " ^ t ^ " doesn't exist")
            end
    | TVar(false,_) -> assert false


(* check that a type doesn't contain an instance of some other type *)
let check_doesnt_contain (t:type_expression) (x:type_name) =
    let rec check_doesnt_contain_aux = function
        | TVar(false,_) -> assert false
        | TVar(true,_) -> ()
        | Data(c,_) when x = c -> raise @$ Error ("*** type " ^ x ^ " appears in non strictly positive position")
        | Data(c,_) -> ()
        | Arrow(t1,t2) -> check_doesnt_contain_aux t1 ; check_doesnt_contain_aux t2
    in check_doesnt_contain_aux t

(* check that a type only appears strictly positively in another *)
let rec check_is_strictly_positive (t:type_expression) (x:type_name) =
    let rec check_is_strictly_positive_aux = function 
        | TVar(true,_) -> ()
        | Data _ -> ()
        | Arrow(t1,t2) -> check_doesnt_contain t1 x; check_is_strictly_positive_aux t2
        | _ -> assert false
    in check_is_strictly_positive_aux t

(* check that a type only appears strictly positively in all the arguments of a constant *)
let rec check_is_strictly_positive_arguments (t:type_expression) (x:type_name) =
    let rec check_is_strictly_positive_arguments_aux t = match t with
        | TVar(true,_) -> check_is_strictly_positive t x
        | Data _ -> check_is_strictly_positive t x
        | Arrow(t1,t2) -> check_is_strictly_positive t1 x; check_is_strictly_positive_arguments_aux t2
        | _ -> assert false
    in check_is_strictly_positive_arguments_aux t

(* check the type of a destructor: it should be of the form T(...) -> ...
 * where "T(...)" is the type being defined *)
let check_destructor (t:type_name) (d:const_name*type_expression) = match d with
    | (_,Arrow(Data(_t,_args), _)) when _t=t -> ()
    | (d,_) -> raise (Error ("*** destructor " ^ d ^ " doesn't appropriate type"))

(* check the type of a constructor: it should be of the form ... -> T(...)
 * where "T(...)" is the type being defined *)
let rec check_constructor (t:type_name) (c:const_name*type_expression) = match c with
    | (_,Data(_t,_args)) when _t=t -> ()
    | (c,Arrow(_,_t)) -> check_constructor t (c,_t)
    | (c,_) -> raise (Error ("*** constructor " ^ c ^ " doesn't appropriate type"))

let process_type_defs (env:environment)
                      (priority:priority)
                      (defs:(type_name * (type_expression list) * (const_name * type_expression) list) list) =
    (* all the types, with parameters, that were mutually defined by this definition *)
    let new_types_with_params = List.rev_map (function (t,params,_) -> (t,params)) defs in

    (* the real priority of this bunch of mutual type definitions *)
    let priority = if (env.current_priority - priority) mod 2 = 0
                   then env.current_priority+2
                   else env.current_priority+1
    in

    let types = ref [] in
    let constants = ref [] in

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

    let process_single_type tname params consts =
        types := (tname, List.map (function TVar(true, x) -> x
                                          | _ -> assert false) params, priority, List.map fst consts) :: !types;

        (* we check that all the parameters are different *)
        check_uniqueness_parameters params;

        (* we replace the inapropriate TVar parts in types of new constants *)
        let consts =  (List.map (function c,t -> c, replace_unknown_TVar params t) consts) in

        (* we check that all instances of defined type appear with the same parameters *)
        List.iter (function _,t -> check_parameters env new_types_with_params t) consts;

        constants := (List.map (function c,t -> c,priority, t) consts) @ !constants;

        (* we check that the type comes from a strictly positive functor *)
        List.iter (function _,t -> check_is_strictly_positive_arguments t tname) consts;

        (* we check the shapes of types of constructors / destructors *)
        if priority mod 2 = 0
        then List.iter (check_destructor tname) consts
        else List.iter (check_constructor tname) consts;

    in List.iter (function tname,params,consts -> process_single_type tname params consts) defs;

    { env with  current_priority = priority;
                types = List.rev_append !types env.types;
                constants = List.rev_append !constants env.constants }
