(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
totality checker for recursive definitions involving nested least and
greatest fixed points.

This software is governed by the CeCILL-B license under French law and
abiding by the rules of distribution of free software.  You can  use,
modify and/ or redistribute the software under the terms of the CeCILL-B
license as circulated by CEA, CNRS and INRIA at the following URL
"http://www.cecill.info".

As a counterpart to the access to the source code and  rights to copy,
modify and redistribute granted by the license, users are provided only
with a limited warranty  and the software's author,  the holder of the
economic rights,  and the successive licensors  have only  limited
liability.

In this respect, the user's attention is drawn to the risks associated
with loading,  using,  modifying and/or developing or reproducing the
software by the user in light of its specific status of free software,
that may mean  that it is complicated to manipulate,  and  that  also
therefore means  that it is reserved for developers  and  experienced
professionals having in-depth computer knowledge. Users are therefore
encouraged to load and test the software's suitability as regards their
requirements in conditions enabling the security of their systems and/or
data to be ensured and,  more generally, to use and operate it in the
same conditions as regards security.

The fact that you are presently reading this means that you have had
knowledge of the CeCILL-B license and that you accept its terms.
========================================================================*)


open Misc
open Env
open Utils
open State
open Pretty

(* check that all the type parameters of a definition are different *)
let check_uniqueness_parameters (params:type_name list) : unit
  = match find_dup params with
        | None -> ()
        | Some x -> error (fmt "type parameter %s appears more than once" x)

(* check that all new types are different *)
let check_new_types_different (types:type_name list) : unit
  = match find_dup types with
        | None -> ()
        | Some(t) -> error (fmt "type %s is defined more than once" t)

(* check that new types are different from old ones *)
let check_new_types_different_from_old (new_types:type_name list) (old_types:type_name list) : unit
  = match find_common new_types old_types with
        | None -> ()
        | Some t -> error (fmt "type %s already exists" t)


(* check that all new constants are different *)
let check_new_consts_different (consts:const_name list) : unit
  = match find_dup consts with
        | None -> ()
        | Some(c) -> error (fmt "constant %s appears more than once" c)

(* check that new constants are different from old ones *)
let check_new_consts_different_from_old (new_consts:const_name list) (old_consts:const_name list) : unit
  = match find_common new_consts old_consts with
        | None -> ()
        | Some t -> error (fmt "constant %s already exists" t)

(* check that all the types being defined only appear with exactly the same parameters
 * and the other types have the appropriate arity
 * check also that the types do not contain "static" parameters... *)
let rec check_parameters (env:environment) (defs:(type_name*type_expression list) list) (t:type_expression) : unit
  = match t with
    | TVar(_) -> ()
    | Arrow(t1,t2) -> check_parameters env defs t1; check_parameters env defs t2
    | Data(t,params) ->
            begin
                try
                    if not (params = List.assoc t defs)
                    then error(fmt "type %s should always use the same parameters in the definition" t)
                with Not_found ->
                    try
                        let a = get_type_arity env t in
                        if not (a = List.length params)
                        then error (fmt "type %s should has arity %d" t a);
                        List.iter (check_parameters env defs) params
                    with Not_found -> error (fmt "type %s doesn't exist" t)
            end

(* check that a type doesn't contain an instance of some other type *)
let check_doesnt_contain (t:type_expression) (x:type_name) : unit
  = let rec check_doesnt_contain_aux = function
        | TVar(_) -> ()
        | Data(c,_) when x = c -> error (fmt "type %s appears in non strictly positive position" x)
        | Data(c,_) -> ()
        | Arrow(t1,t2) -> check_doesnt_contain_aux t1 ; check_doesnt_contain_aux t2
    in check_doesnt_contain_aux t

(* check that a type only appears strictly positively in another *)
let rec check_is_strictly_positive (t:type_expression) (x:type_name) : unit
  = let rec check_is_strictly_positive_aux = function
        | TVar(_) -> ()
        | Data _ -> ()
        | Arrow(t1,t2) -> check_doesnt_contain t1 x; check_is_strictly_positive_aux t2
    in check_is_strictly_positive_aux t

(* check that a type only appears strictly positively in all the arguments of a constant *)
let rec check_is_strictly_positive_arguments (t:type_expression) (x:type_name) : unit
  = let rec check_is_strictly_positive_arguments_aux t = match t with
        | TVar(_) -> check_is_strictly_positive t x
        | Data _ -> check_is_strictly_positive t x
        | Arrow(t1,t2) -> check_is_strictly_positive t1 x; check_is_strictly_positive_arguments_aux t2
    in check_is_strictly_positive_arguments_aux t

(* check the type of a destructor: it should be of the form T(...) -> ...
 * where "T(...)" is the type being defined *)
let check_destructor (t:type_name) (d:const_name*type_expression) : unit
  = match d with
    | (_,Arrow(Data(_t,_args), _)) when _t=t -> ()
    | (d,_) -> error (fmt "destructor %s doesn't appropriate type" d)

(* check the type of a constructor: it should be of the form ... -> T(...)
 * where "T(...)" is the type being defined *)
let check_constructor (t:type_name) (c:const_name*type_expression) : unit
  = let rec check_constructor_aux c = match c with
    | (_,Data(_t,_args)) when _t=t -> ()
    | (c,Arrow(_,_t)) -> check_constructor_aux (c,_t)
    | (c,_) -> error (fmt "constructor %s doesn't appropriate type" c)
  in
  if option "unary_constants"
  then match c with
    | (_,Arrow(_,Data(_t,_args))) when _t=t -> ()
    | (c,_) -> error (fmt "constructor %s is not unary" c)
  else check_constructor_aux c



let check_empty_unit env n (t:type_name) params consts
  = match params,consts with
        | [],[] ->
            begin
                try
                    if odd n
                    then
                        let tname = get_empty_type env in
                        error (fmt "there already is an empty type: %s" tname)
                    else
                        let tname = get_unit_type env in
                        error (fmt "there already is a unit type: %s" tname)
                with Not_found -> ()
            end
        | _,[] -> error "types with no constants are not allowed to have parameters"
        | _,_ -> ()

let process_type_defs (env:environment)
                      (n:bloc_nb)
                      (defs:(type_name * (type_expression list) * (const_name * type_expression) list) list)
  : environment
    =
    (* all the types, with parameters, that were mutually defined by this definition *)
    let new_types_with_params = List.rev_map (function (t,params,_) -> (t,params)) defs
    in

    (* we check that all the new types are different *)
    let new_types_without_params = List.rev_map (function (t,_,_) -> t) defs in
    check_new_types_different new_types_without_params;

    (* we check that new types are different from old types *)
    let old_types = List.rev_map (function (t,_,_,_) -> t) env.types in
    check_new_types_different_from_old new_types_without_params old_types;

    (* we check that all the new constants are different *)
    let new_consts = List.concat (List.rev_map (function (_,_,consts) -> List.rev_map fst consts) defs) in
    check_new_consts_different new_consts;

    (* we check that all the new constants are different from the old ones *)
    let old_consts = List.map (function c,_,_ -> c) env.constants in
    check_new_consts_different_from_old new_consts old_consts;
    (* and the old functions *)
    let old_functions = List.map (function f,_,_,_,_ -> f) env.functions in
    check_new_consts_different_from_old new_consts old_functions;

    let process_single_type (tname:type_name)
                            (params:type_expression list)
                            (consts:(const_name*type_expression) list)
      : (type_name * bloc_nb * type_name list * const_name list) * (const_name * int * type_expression) list
        =
        let params = List.map (function TVar(x) -> x | _ -> assert false) params in

        (* we check that we are not redefining an empty / unit type *)
        check_empty_unit env n tname params consts;

        (* we check that all the parameters are different *)
        check_uniqueness_parameters params;

        (* we check that all the type parameters are indeed parameters *)
        List.iter (function _,t ->
            let params' = extract_type_variables t in
            match diff_uniq params' params with
                | [] -> ()
                | x::_ -> error (fmt "type parameter %s is free" x)
        ) consts;

        (* we check that all instances of defined type appear with the same parameters *)
        List.iter (function _,t -> check_parameters env new_types_with_params t) consts;

        (* we check that the type comes from a strictly positive functor *)
        List.iter (function _,t -> check_is_strictly_positive_arguments t tname) consts;

        (* we check the shapes of types of constructors / destructors *)
        if even n
        then List.iter (check_destructor tname) consts
        else List.iter (check_constructor tname) consts;

        (tname, n, params, List.map fst consts) , (List.map (function c,t -> c,n,t) consts)
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

    if (verbose 1)
    then
        begin
            msg "%s type%s %s %s succesfully defined"
                (if even n then "coinductive" else "inductive")
                (plural defs "" "s")
                (string_of_list  " and " (function (t,_,_) -> t) defs)
                (plural defs "was" "were")
        end;

    current_state.current_bloc <- n;
    { env with  types = types @ env.types;
                constants = consts @ env.constants }

