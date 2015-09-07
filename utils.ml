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


(*
 * the types for representing
 *   - types
 *   - terms
 *   - environments
 *)
open Misc
open Env

(*
 * some utility functions
 *)
let env_type_assoc (env:environment) (t:type_name)
  = let rec aux = function
        | [] -> raise Not_found
        | (t', n, params, consts)::_ when t'=t -> (n,params,consts)
        | _::ts -> aux ts
    in
    aux env.types

let get_type_arity (env:environment) (t:type_name) : int
  = match env_type_assoc env t with
        (_,params,_) -> List.length params

let is_inductive (env:environment) (t:type_name) : bool
  = match env_type_assoc env t with
        (n,_,_) -> odd n

let get_type_constants (env:environment) (t:type_name) : const_name list
  = match env_type_assoc env t with
        (_,_,consts) -> consts


let env_const_assoc (env:environment) (c:const_name)
  = let rec aux = function
        | [] -> raise Not_found
        | (c', n, t)::_ when c'=c -> (n,t)
        | _::ts -> aux ts
    in
    aux env.constants

let get_constant_type (env:environment) (c:const_name)
  = match env_const_assoc env c with
        (_,t) -> t

let is_projection (env:environment) (c:const_name) : bool
  = match env_const_assoc env c with
        (n,t) -> even n




let env_fun_assoc (env:environment) (f:var_name)
  = let rec aux = function
        | [] -> raise Not_found
        | (f', n, t, clauses, cst)::_ when f'=f -> (n, t, clauses, cst)
        | _::ts -> aux ts
    in
    aux env.functions

let get_function_type (env:environment) (f:var_name)
  = match env_fun_assoc env f with
        (_,t,_,_) -> t

let get_function_clauses (env:environment) (f:var_name)
  = match env_fun_assoc env f with
        (_,_,clauses,_) -> clauses

let get_function_case_struct (env:environment) (f:var_name)
  = match env_fun_assoc env f with
        (_,_,_,cst) -> cst


let get_other_constants (env:environment) (c:const_name) : const_name list
  = let rec get_aux = function
        | [] -> error ("constant " ^ c ^ " doesn't exist")
        | (_,_,_,consts)::_ when List.mem c consts -> consts
        | _::types -> get_aux types
    in get_aux env.types


let rec type_arity (t:type_expression) : int
  = match t with
        | TVar _ | Data _ -> 0
        | Arrow(_,t) -> 1+type_arity t

let get_constant_arity (env:environment) (c:const_name) : int
  = let t = get_constant_type env c in
    type_arity t

(* get the function name from a pattern *)
let rec get_head (v:('a,'p,'t) raw_term) : ('a,'p,'t) raw_term
  = match v with
    | Const _ | Angel _ | Daimon _ | Var _ | Proj _ | Sp _ -> v
    | App(v,_) -> get_head v

let rec get_head_const (v:('a,'p,'t) raw_term) : const_name
  = match v with
    | Const(c,p,_)  -> c
    | Angel _ | Daimon _ | Var _ | Proj _ | Sp _ ->  raise (Invalid_argument "no head constructor")
    | App(v,_) -> get_head_const v

let get_args (v:('a,'p,'t) raw_term) : ('a,'p,'t) raw_term list
  = let rec get_args_aux acc = function
        | Const _ | Angel _ | Daimon _ | Var _ | Proj _ | Sp _ -> acc
        | App(v1,v2) -> get_args_aux (v2::acc) v1
    in
    get_args_aux [] v

let rec get_function_name (v:('a,'p,'t) raw_term) : var_name
  = match v with
    | Var(f,_) -> f
    | Angel _ | Daimon _ | Const _ | Proj _ ->  raise (Invalid_argument "no head function")
    | App(Proj _,v) -> get_function_name v
    | App(v,_) -> get_function_name v
    | Sp(v,_) -> assert false

let rec type_of (u:('a,'p,type_expression) raw_term) : type_expression
  = match u with
        | Daimon t | Angel t | Var(_,t) | Const(_,_,t) | Proj(_,_,t) | Sp(_,t) -> t
        | App(u1,u2) ->
            begin
                match type_of u1 with
                    | Arrow(t2,t) when t2 = type_of u2 -> t
                    | _ -> assert false
            end


let app (f:('a,'p,'t) raw_term) (args:('a,'p,'t) raw_term list) : ('a,'p,'t) raw_term
  = List.fold_left (fun v arg -> App(v,arg)) f args

let rec get_result_type (t:type_expression) : type_expression
  = match t with
    | Data _ | TVar _ -> t
    | Arrow(_,t) -> get_result_type t

let get_first_arg_type (t:type_expression) : type_expression
  = match t with
    | Data _ | TVar _ -> raise (Invalid_argument "get_first_arg_type")
    | Arrow(t,_) -> t

let rec get_args_type (t:type_expression) : type_expression list
  = match t with
    | Data _ | TVar _ -> []
    | Arrow (t1,t2) -> t1::(get_args_type t2)

(* get all the variables from a type, keeping the order of first occurences *)
let extract_type_variables (t:type_expression) : type_name list
  = let rec extract_type_variables_aux = function
        | TVar(x) -> [x]
        | Data(_, params) -> List.concat (List.map extract_type_variables_aux params)
        | Arrow(t1,t2) -> (extract_type_variables_aux t1) @ (extract_type_variables_aux t2)
    in
    uniq ~stable:true (extract_type_variables_aux t)


let rec extract_datatypes (t:type_expression) : type_expression list
  = match t with
    | TVar _ -> []
    | Data(_,params) -> t::(List.concat (List.map extract_datatypes params))
    | Arrow(t1,t2) -> (extract_datatypes t1) @ (extract_datatypes t2)

let rec extract_datatypes_from_typed_term (u:(empty,'p,type_expression) raw_term) : type_expression list
  = match u with
        | Daimon _ | Angel _ | Var _ -> []
        | App(u1,u2) -> union_uniq (extract_datatypes_from_typed_term u1) (extract_datatypes_from_typed_term u2)
        | Const(_,_,t) -> extract_datatypes (get_result_type t)
        | Proj(_,_,t) -> extract_datatypes (get_first_arg_type t)
        | Sp(s,_) -> s.bot

let rec extract_term_variables (v:(empty,'p,'t) raw_term) : var_name list
  = match v with
        | Angel _ | Daimon _ | Const _ | Proj _ -> []
        | Var(x,_) -> [x]
        | App(v1,v2) -> union_uniq (extract_term_variables v1) (extract_term_variables v2)
        | Sp(v,_) -> v.bot

(* let rec extract_pattern_variables (v:pattern) : var_name list *)
let rec extract_pattern_variables (v:(empty,'p,'t) raw_term) : var_name list
  = match get_head v,get_args v with
        | Var(f,_),args -> List.concat (List.map extract_term_variables args)
        | Proj _,v::args -> (extract_pattern_variables v) @ (List.concat (List.map extract_term_variables args))
        | _,_ -> assert false

let rec map_raw_term (f:'a1 -> 'a2) (g:'p1 -> 'p2) (h:'t1 -> 't2) (v:('a1,'p1,'t1) raw_term) : ('a2,'p2,'t2) raw_term
  = match v with
        | Angel t -> Angel (h t)
        | Daimon t -> Daimon (h t)
        | Var(x,t) -> Var(x,h t)
        | Const(c,p,t) -> Const(c,g p,h t)
        | Proj(d,p,t) -> Proj(d,g p,h t)
        | App(v1,v2) -> App(map_raw_term f g h v1, map_raw_term f g h v2)
        | Sp(a,t) -> Sp(f a,h t)

let map_type_term f u = map_raw_term id id f u

(* apply a substitution on a term *)
let rec subst_term sigma (v:(empty,'p,'t) raw_term) : (empty,'p,'t) raw_term
  = match v with
    | Var(x,t) -> (try List.assoc x sigma with Not_found -> Var(x,t))
    | Angel t -> Angel t
    | Daimon t -> Daimon t
    | Const(c,p,t) -> Const(c,p,t)
    | Proj(d,p,t) -> Proj(d,p,t)
    | App(v1,v2) -> App(subst_term sigma v1, subst_term sigma v2)
    | Sp(v,t) -> v.bot

(* apply a substitution on a type *)
let rec subst_type (sigma:type_substitution) (t:type_expression) : type_expression
  = match t with
    | TVar (y) -> (try List.assoc y sigma with Not_found -> t)
    | Arrow(t1,t2) -> Arrow(subst_type sigma t1, subst_type sigma t2)
    | Data(tname, args) -> Data(tname, List.map (subst_type sigma) args)

(* apply a type substitution to all the type annotations inside a typed term *)
let rec subst_type_term  (sigma:type_substitution) (u:(empty,'p,type_expression) raw_term) : (empty,'p,type_expression) raw_term
  = match u with
        | Angel(t) -> Angel(subst_type sigma t)
        | Daimon(t) -> Daimon(subst_type sigma t)
        | Var(x,t) -> Var(x,subst_type sigma t)
        | Const(c,p,t) ->  Const(c,p,subst_type sigma t)
        | Proj(d,p,t) ->  Proj(d,p,subst_type sigma t)
        | App(u1,u2) ->
            let u1 = subst_type_term sigma u1 in
            let u2 = subst_type_term sigma u2 in
            App(u1,u2)
        | Sp(s,t) -> s.bot

(* compose two type substitutions *)
let compose_type_substitution (sigma1:type_substitution) (sigma2:type_substitution) : type_substitution
  = sigma2 @ (List.map (second (subst_type sigma2)) sigma1)


let rec explode (v:('a,'p,'t) raw_term) : ('a,'p,'t) raw_term list
  = let h,args = get_head v,get_args v in
    match h,args with
        | Var _,args | Const _,args | Angel _,args | Daimon _,args | Sp _,args-> h::args
        | Proj _,v::args -> (explode v)@(h::args)
        | Proj _ as p,[] -> [p]
        | App _,_ -> assert false

let implode (args:('a,'p,'t) raw_term list) : ('a,'p,'t) raw_term
  = let rec implode_aux args acc
      = match args with
            | [] -> acc
            | (Var(_,_) | Angel _ | Daimon _ | Const(_,_,_) | App(_,_) | Sp(_,_) as v)::args -> implode_aux args (App(acc,v))
            | (Proj(_,_,t) as v)::args -> implode_aux args (App(v,acc))
    in
    match args with
        | [] -> assert false
        | v::args -> implode_aux args v


