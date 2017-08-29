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
open Typing

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

let find_types_priorities env (ts:type_expression list)
  : (type_expression*int) list
  =
    let nodes = ts in

    (* wether a type appears inside another *)
    let subtype_of0 t1 t2
      = match t1,t2 with
            | t1,t2 when t1=t2 -> false
            | t1,Data(tname2,params2) -> List.mem t1 params2
            | Data _, TVar _ | TVar _, TVar _ -> false
            | _,_ -> assert false
    in

    let graph = List.map (fun x -> x,List.filter (subtype_of0 x) nodes) nodes in

    (* computes the priority for type t
     * acc is the list of types with priorities already computed
     *)
    let rec order (n:int) (graph:(type_expression*(type_expression list)) list) (acc:(type_expression*int) list)
      =
        (* debug "n:%d and acc:%s" n (string_of_list "\n    " (function t,p -> (string_of_type t) ^ ":" ^ (string_of_int p)) acc); *)
        match graph with
            | [] -> acc
            | graph ->
                let terminals,graph =
                    List.partition (function Data(tname,_),[] -> (is_inductive env tname) = (even n)
                                           | Data _,_ -> false
                                           | _ -> assert false
                                   ) graph in
                let terminals = List.map fst terminals in
                let graph = List.map (second (List.filter (fun t -> not (List.mem t terminals)))) graph in
                let terminals = List.map (fun t -> t,n+1) terminals in
                let n =
                    if terminals = [] then n+1
                    else if option "squash_priorities" then n
                    else n+1
                in
                order n graph (terminals@acc)
    in

    order (-1) graph []

let infer_priorities (env:environment)
                     (defs:(var_name * type_expression * (typed_term*typed_term) list * 'x) list)
  : (var_name * type_expression * (term*term) list * 'x) list
  =

    let datatypes = List.fold_left
        (fun ds ftcls ->
            let _,_,cls,_ = ftcls in
            List.fold_left
                (fun ds lhsrhs ->
                    let lhs,rhs = lhsrhs in
                    let ds = union_uniq ds (extract_datatypes_from_typed_term lhs) in
                    let ds = union_uniq ds (extract_datatypes_from_typed_term rhs) in
                    ds
                )
                ds
                cls
        )
        []
        defs
    in

    let local_types = find_types_priorities env datatypes in
    let local_types = List.sort (fun x y -> compare (snd x) (snd y)) local_types in
    (* debug "priorities:\n    %s" (string_of_list "\n    " (function t,p -> (string_of_type t) ^ ":" ^ (string_of_int p)) local_types); *)

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

    let rec put_priorities_term v
      = match v with
            | Angel t -> Angel t
            | Daimon t -> Daimon t
            | Var(x,t) -> Var(x,t)
            | App(u1,u2) -> App(put_priorities_term u1, put_priorities_term u2)
            | Sp(s,_) -> s.bot
            | Struct(fields,_,t) ->
                let p = get_priority t in
                let fields = List.map (second put_priorities_term) fields in
                Struct(fields,Some p,t)
            | Const(c,_,t) ->
                let ct = get_result_type t in
                let p = get_priority ct in
                Const(c,Some p,t)
            | Proj(d,_,t) ->
                let dt = get_first_arg_type t in
                let p = get_priority dt in
                Proj(d,Some p,t)

    in
    let put_priorities_single_clause (lhs,rhs) = (put_priorities_term lhs,put_priorities_term rhs)
    in
    List.map (function f,t,clauses,x -> f,t,List.map put_priorities_single_clause clauses,x) defs

