(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
adequacy checker for recursive definitions involving nested least and
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
                    then if option "squash_priorities" then (n, (t,n)::acc) else (n+2, (t,n+2)::acc)
                    else (n+1, (t,n+1)::acc)
                | _ -> assert false
    in
    let datatypes = List.filter (function Data _ -> true | _ -> assert false) nodes in

    List.fold_left (fun acc t -> let n,acc = order t acc [] in acc) [] datatypes

let infer_priorities (env:environment)
                     (defs:(var_name * type_expression * ((empty,'t) special_term * (empty,'t) special_term) list) list)
  : (var_name * type_expression * ((empty,'t) special_term * (empty,'t) special_term) list) list
  =

    let datatypes = List.fold_left
        (fun ds ftcls ->
            let _,_,cls = ftcls in
            List.fold_left
                (fun ds lhsrhs ->
                    let lhs,rhs = lhsrhs in
                    let ds = merge_uniq ds (extract_datatypes_from_typed_term lhs) in
                    let ds = merge_uniq ds (extract_datatypes_from_typed_term rhs) in
                    ds
                )
                ds
                cls
        )
        []
        defs
    in

    (* debug "datatypes: %s\n  " (string_of_list ",\n  " string_of_type datatypes); *)
    let local_types = find_types_priorities env datatypes in
    (* debug "priorities: %s\n  " (string_of_list ",\n  " (function t,p -> (string_of_type t) ^ ":" ^ (string_of_int p)) local_types); *)

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
            | Angel _ | Daimon _ | Var _ -> v
            | App(u1,u2) -> App(put_priorities_term u1, put_priorities_term u2)
            | Sp(s,_) -> s.bot
            | Const(c,_,t) ->
                let dt = get_result_type t in
                let p = get_priority dt in
                Const(c,Some p,t)
            | Proj(d,_,t) ->
                let dt = get_first_arg_type t in
                let p = get_priority dt in
                Proj(d,Some p,t)

    in
    let put_priorities_single_clause (lhs,rhs) = (put_priorities_term lhs,put_priorities_term rhs)
    in
    List.map (function f,t,clauses -> f,t,List.map put_priorities_single_clause clauses) defs

