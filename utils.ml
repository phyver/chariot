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
let get_type_arity (env:environment) (t:type_name) : int
  = let rec get_type_arity_aux = function
        | [] -> raise Not_found
        | (_t, _params, _, _)::_ when _t=t -> List.length _params
        | _::ts -> get_type_arity_aux ts
    in
    get_type_arity_aux env.types

let is_inductive (env:environment) (t:type_name) : bool
  = let rec is_inductive_aux = function
        | [] -> raise Not_found
        | (_t, _, _n, _)::_ when _t=t -> odd _n
        | _::ts -> is_inductive_aux ts
    in
    is_inductive_aux env.types

let get_type_constants (env:environment) (t:type_name) : const_name list
  = let rec get_type_constants_aux = function
        | [] -> raise Not_found
        | (_t, _, _, _constants)::_ when _t=t -> _constants
        | _::ts -> get_type_constants_aux ts
    in
    get_type_constants_aux env.types

let get_constant_type (env:environment) (c:const_name)
  = let rec get_type_constants_aux = function
        | [] -> raise Not_found
        | (_c,_p,_t)::_ when _c=c -> _t
        | _::consts -> get_type_constants_aux consts
    in get_type_constants_aux env.constants

let rec type_arity (t:type_expression) : int
  = match t with
        | TVar _ | Data _ -> 0
        | Arrow(_,t) -> 1+type_arity t

let get_constant_arity (env:environment) (c:const_name) : int
  = let t = get_constant_type env c in
    type_arity t

let is_projection (env:environment) (c:const_name) : bool
  = let rec is_projection_aux = function
        | [] -> raise Not_found
        | (_c, _n, _)::_ when _c=c -> even _n
        | _::cs -> is_projection_aux cs
    in
    is_projection_aux env.constants

let get_function_type (env:environment) (x:var_name)
  = let rec get_function_type_aux = function
        | [] -> raise Not_found
        | (f,_,t,_,_)::_ when f=x -> t
        | _::fcts -> get_function_type_aux fcts
    in
    get_function_type_aux env.functions

let get_function_clauses (env:environment) (f:var_name)
  = let rec get_function_clauses_aux = function
        | [] -> raise Not_found
        | (_f,_,_,clauses,_)::_ when _f=f -> clauses
        | _::fcts -> get_function_clauses_aux fcts
    in
    get_function_clauses_aux env.functions

let get_function_case_struct (env:environment) (f:var_name)
  = let rec get_function_case_struct_aux = function
        | [] -> raise Not_found
        | (_f,_,_,_,cs)::_ when _f=f -> cs
        | _::fcts -> get_function_case_struct_aux fcts
    in
    get_function_case_struct_aux env.functions


let get_function_def (env:environment) (f:var_name)
  = let rec get_function_def_aux = function
        | [] -> raise Not_found
        | (_f,_,_,_,v)::_ when _f=f -> v
        | _::fcts -> get_function_def_aux fcts
    in
    get_function_def_aux env.functions

let get_other_constants (env:environment) (c:const_name) : const_name list
  = let rec get_aux = function
        | [] -> error ("constant " ^ c ^ " doesn't exist")
        | (_,_,_,consts)::_ when List.mem c consts -> consts
        | _::types -> get_aux types
    in get_aux env.types

(* get the function name from a pattern *)
let rec get_head (v:('a,'t) special_term) : ('a,'t) special_term
  = match v with
    | Const _ | Angel _ | Var _ | Proj _ | Special _ -> v
    | App(v,_,_) -> get_head v

let rec get_head_const (v:('a,'t) special_term) : const_name
  = match v with
    | Const(c,p,_)  -> c
    | Angel _ | Var _ | Proj _ | Special _ ->  raise (Invalid_argument "no head constructor")
    | App(v,_,_) -> get_head_const v

let rec get_function_name (v:('a,'t) special_term) : var_name
  = match v with
    | Var(f,_) -> f
    | Angel _ | Const _ | Proj _ ->  raise (Invalid_argument "no head function")
    | App(Proj _,v,_) -> get_function_name v
    | App(v,_,_) -> get_function_name v
    | Special(v,_) -> v.bot

let get_args (v:('a,'t) special_term) : ('a,'t) special_term list
  = let rec get_args_aux acc = function
        | Const _ | Angel _ | Var _ | Proj _ | Special _ -> acc
        | App(v1,v2,_) -> get_args_aux (v2::acc) v1
    in
    get_args_aux [] v

let type_of (u:('a,'t) special_term) : 't
  = match u with
        | Angel t
        | Var(_,t)
        | Const(_,_,t)
        | Proj(_,_,t)
        | App(_,_,t) -> t
        | Special(s,t) -> t

(* NOTE: the result has the same "type" as the function! *)
let app (f:('a,'t) special_term) (args:('a,'t) special_term list) : ('a,'t) special_term
  = let t = type_of f in
      List.fold_left (fun v arg -> App(v,arg,t)) f args

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
    uniq (extract_type_variables_aux t)


let rec extract_atomic_types (t:type_expression) : type_expression list
  = match t with
    | TVar _ -> [t]
    | Data(_,params) -> t::(List.concat (List.map extract_atomic_types params))
    | Arrow(t1,t2) -> (extract_atomic_types t1) @ (extract_atomic_types t2)

let rec extract_datatypes (t:type_expression) : type_expression list
  = match t with
    | TVar _ -> []
    | Data(_,params) -> t::(List.concat (List.map extract_datatypes params))
    | Arrow(t1,t2) -> (extract_datatypes t1) @ (extract_datatypes t2)

let rec extract_datatypes_from_typed_term (u:(empty,type_expression) special_term) : type_expression list
  = match u with
        | Angel _ | Var _ -> []
        | App(u1,u2,_) -> merge_uniq (extract_datatypes_from_typed_term u1) (extract_datatypes_from_typed_term u2)
        | Const(_,_,t) -> extract_datatypes (get_result_type t)
        | Proj(_,_,t) -> extract_datatypes (get_first_arg_type t)
        | Special(s,_) -> s.bot


let rec extract_term_variables (v:(empty,'t) special_term) : var_name list
  = let rec extract_term_variables_aux v =
        match v with
            | Angel _ | Const _ | Proj _ -> []
            | Var(x,_) -> [x]
            | App(v1,v2,_) -> (extract_term_variables_aux v1) @ (extract_term_variables_aux v2)
            | Special(v,_) -> v.bot
    in uniq (extract_term_variables_aux v)

(* let rec extract_pattern_variables (v:pattern) : var_name list *)
let rec extract_pattern_variables (v:(empty,'t) special_term) : var_name list
  = match get_head v,get_args v with
        | Var(f,_),args -> List.concat (List.map extract_term_variables args)
        | Proj _,v::args -> (extract_pattern_variables v) @ (List.concat (List.map extract_term_variables args))
        | _,_ -> assert false

let rec map_special_term (f:'a1 -> 'a2) (g:'t1 -> 't2) (u:('a1,'t1) special_term) : ('a2,'t2) special_term
  = match u with
        | Angel t -> Angel (g t)
        | Var(x,t) -> Var(x,g t)
        | Const(c,p,t) -> Const(c,p,g t)
        | Proj(d,p,t) -> Proj(d,p,g t)
        | App(u1,u2,t) -> App(map_special_term f g u1, map_special_term f g u2, g t)
        | Special(a,t) -> Special(f a,g t)

let map_type_term f u = map_special_term identity f u

let add_weight (w1:weight) (w2:weight) : weight
  = match w1,w2 with
    | Infty,_ | _,Infty -> Infty
    | Num a,Num b -> Num (a+b)

let add_weight_int (w:weight) (n:int) : weight
  = add_weight w (Num n)

let op_weight (w:weight) : weight
  = match w with
        | Infty -> raise (Invalid_argument "op_weight")
        | Num n -> Num (-n)

let collapse_weight (bound:int) (w:weight) : weight
  = match w with
    | Infty -> Infty
    | Num w when bound<=w -> Infty
    | Num w when -bound<=w -> Num w
    | Num w (* when w<-bound *) -> Num(-bound)



let rec pattern_to_approx_term (v:'t pattern) (*: approx_term *)
  = match v with
    | Var(x,t) -> Var(x,t)
    | Angel(t) -> Angel(t)
    | Const(c,p,t) -> Const(c,p,t)
    | Proj(d,p,t) -> Proj(d,p,t)
    | App(v1,v2,t) -> App(pattern_to_approx_term v1, pattern_to_approx_term v2,t)
    | Special(s,t) -> s.bot

let typed_app (f:('a,type_expression) special_term) (args:('a,type_expression) special_term list) : ('a,type_expression) special_term
  = List.fold_left (fun v arg ->
        let t1 = type_of arg in
        let tv = type_of v in
        match tv with Arrow(_t1,t2) when _t1=t1 -> App(v,arg,t2) | _ -> raise (Invalid_argument "typed_app"))
  f
  args

let rec subst_term sigma (v:'t term) : 't term
  = match v with
    | Var(x,t) -> (try List.assoc x sigma with Not_found -> Var(x,t))
    | Angel t -> Angel t
    | Const(c,p,t) -> Const(c,p,t)
    | Proj(d,p,t) -> Proj(d,p,t)
    | App(v1,v2,t) -> App(subst_term sigma v1, subst_term sigma v2,t)
    | Special(v,t) -> Special(v,t)

