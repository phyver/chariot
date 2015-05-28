open Base
open Misc


(* check that all the type parameters of a definition are different *)
let check_type_parameters params =
    let rec uniq = function
        | [] -> ()
        | [a] -> ()
        | a::b::params when a=b -> raise (Error ("Type parameters should be all different."))
        | a::b::params -> uniq (b::params)
    in
    uniq (List.sort compare params)


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

(* check that all the types being defined only appear with exactly the same parameters *)
let rec check_parameters_of_defined_types (defs:(type_name*type_expression list) list) = function
    | TVar(true,_) -> ()
    | Arrow(t1,t2) -> check_parameters_of_defined_types defs t1; check_parameters_of_defined_types defs t2
    | Data(t,params) ->
            begin
                try
                    if not (params = List.assoc t defs)
                    then raise @$ Error("type " ^ t ^ " should always use the same parameters in the definition")
                with Not_found -> ()
            end
    | TVar(false,_) -> assert false


(* check that a type doesn't contain an instance of some other type *)
let check_doesnt_contain (t:type_expression) (x:type_name) =
    let rec check_doesnt_contain_aux = function
        | TVar(false,_) -> assert false
        | TVar(true,_) -> ()
        | Data(c,_) when x = c -> raise @$ Error ("type " ^ x ^ " appears in non strictly positive position")
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

(* FIXME:clean *)
(* check the type of a destructor: it should be of the form T(...) -> ...
 * where "T(...)" is the type being defined *)
let check_destructor (t:type_name) (d:const_name*type_expression) = match d with
    | (_,Arrow(Data(_t,_args), _)) when _t=t -> ()
    | (d,_) -> raise (Error ("Destructor " ^ d ^ " doesn't appropriate type"))

(* FIXME:clean *)
(* check the type of a constructor: it should be of the form ... -> T(...)
 * where "T(...)" is the type being defined *)
let rec check_constructor (t:type_name) (c:const_name*type_expression) = match c with
    | (_,Data(_t,_args)) when _t=t -> ()
    | (c,Arrow(_,_t)) -> check_constructor t (c,_t)
    | (c,_) -> raise (Error ("Constructor " ^ c ^ " doesn't appropriate type"))


let process_type_defs (env:environment) (priority:priority) (defs:(type_name * (type_expression list) * (const_name * type_expression) list) list) =
    (* all the types, with parameters, that were mutually defined by this definition *)
    let new_types_with_params = List.map (function (t,params,_) -> (t,params)) defs in

    (* the real priority of this bunch of mutual type definitions *)
    let priority = if (env.current_priority - priority) mod 2 = 0 then env.current_priority+2 else env.current_priority+1 in

    let types = ref [] in
    let constants = ref [] in

    (* we check that all the new types are different *)
    (* TODO *)

    (* we check that all the new constants are different *)
    (* TODO *)

    let process_single_type tname params consts =
        types := (tname, List.map (function TVar(true, x) -> x | _ -> assert false) params, priority, List.map fst consts) :: !types;

        (* we check that all the parameters are different *)
        check_type_parameters params;

        (* we replace the inapropriate TVar parts in types of new constants *)
        let consts =  (List.map (function c,t -> c, replace_unknown_TVar params t) consts) in

        (* we check that all instances of defined type appear with the same parameters *)
        List.iter (function _,t -> check_parameters_of_defined_types new_types_with_params t) consts;

        constants := (List.map (function c,t -> c,priority, t) consts) @ !constants;

        (* we check that the type comes from a strictly positive functor *)
        List.iter (function _,t -> check_is_strictly_positive_arguments t tname) consts;

        (* we check the shapes of types of constructors / destructors *)
        if priority mod 2 = 0
        then List.iter (check_destructor tname) consts
        else List.iter (check_constructor tname) consts;

        (* check that new types don't already exist *)
        if List.exists (function _t,_,_,_ -> _t=tname) env.types
        then raise (Error ("*** there is a type named " ^ tname));

        (* we check that new constants don't already exist *)
        (* TODO *)

        (* we check that all the atomic types already exist and have the appropriate arity *)
        (* TODO *)


    in List.iter (function tname,params,consts -> process_single_type tname params consts) defs;

    { env with current_priority = priority; types = env.types @ !types; constants = env.constants @ !constants }
