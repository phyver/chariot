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

(* showing a priority *)
let string_of_priority p
  = if not (option "show_priorities")
    then ""
    else
        match p with
        (* | None ->  "⁽⁾" *)
        (* | None ->  "⁻" *)
        | None -> if option "use_ansi_codes" then ansi_code "red" "⁼" else "⁼"
        | Some p -> if option "use_ansi_codes" then ansi_code "green" (string_of_exp p) else (string_of_exp p)

(* check if a type is atomic in order to know where to put parenthesis *)
let is_atomic_type = function
    | TVar _ -> true
    | Data(t,params) when (option "show_tuples") && (Str.string_match (Str.regexp "prod_\\(0\\|[1-9][0-9]*\\)") t 0) ->
        let n = int_of_string (String.sub t 5 ((String.length t) - 5)) in
        not ((List.length params = n) && (n > 1))
    | Data(t,params) -> true
    | Arrow _ -> false

(* show a type *)
let rec string_of_type = function
    | TVar(x) -> "'"^x
    | Data(t,[]) -> t
    | Data(t,params) when (option "show_tuples") && (Str.string_match (Str.regexp "prod_\\(0\\|[1-9][0-9]*\\)") t 0) ->
        let n = int_of_string (String.sub t 5 ((String.length t) - 5)) in
        if List.length params = n
        then (string_of_list " * " (fun t -> if is_atomic_type t then string_of_type t else "(" ^ string_of_type t ^ ")") params)
        else (t ^ "(" ^ (String.concat "," (List.map string_of_type params)) ^ ")")
    | Data(t,params) ->
        t ^ "(" ^ (String.concat "," (List.map string_of_type params)) ^ ")"
    | Arrow(t1,t2) ->
        if is_atomic_type t1
        then (string_of_type t1) ^ " → " ^ (string_of_type t2)
        else ("(" ^ (string_of_type t1) ^ ")" ^ " → " ^ (string_of_type t2))


(* check if a term is atomic in order to know where to put parenthesis *)
let rec is_atomic_term (v:('a,'p,'t) raw_term) = match v with
    | Var _ | Angel _ | Daimon _ | Const _ | Proj _ | Struct _ -> true
    | App(Proj _, v) -> is_atomic_term v
    | App _ -> false
    | Sp _ -> true

(* show a variables, taking care of the special cases *)
let string_of_var s
  =
    let re_dummy = Str.regexp "_\\(₀\\|₁\\|₂\\|₃\\|₄\\|₅\\|₆\\|₇\\|₈\\|₉\\)*$" in
    assert (s<>"");

    if s = "()" then "()"
    else if Str.string_match re_dummy s 0 then (if verbose 1 then s else "_")
    else s

(* very generic function to show raw terms:
 *   - we can give specific functions for showing priorities / types (arguments sp and st)
 *   - we can give a specific function for showing special features (argument ss)
 *   - we can give an additional parameter that is carried around and can be used the ss function
 *     (typical use: keep an indentation level that is used, and modified by the ss function)
 *)
let rec
  string_of_raw_term
        (o:'o)                          (* additional parameter *)
        (ss:'o -> 'a -> string)         (* to process Sp(...) terms *)
        (sp:'p -> string)               (* to process 'p parameters *)
        (st:'t -> string)               (* to process 't parameters *)
        (v:('a,'p,'t) raw_term)
    : string
  = try string_of_term_int o ss sp st false v   with Invalid_argument "string_of_term_int" ->
    try string_of_term_list o ss sp st false v  with Invalid_argument "string_of_term_list" ->
    try string_of_term_tuple o ss sp st v       with Invalid_argument "string_of_term_tuple" ->
    begin
    match v with
        | Angel t -> "⊤" ^ (st t)
        | Daimon t -> "⊥" ^ (st t)
        | Var(x,t) -> (string_of_var x) ^ (st t)
        | Const(c,p,t) -> c ^ (sp p) ^ (st t)
        | Proj(d,p,t) -> "." ^ d ^ (sp p) ^ (st t)
        | App(Proj _ as v1,v2) ->
            let s2 = (string_of_raw_term_paren o ss sp st v2) in
            let s1 =  (string_of_raw_term o ss sp st v1) in
            fmt "%s%s" s2 s1
        (* | App(App(Var("add",_),v1),v2) when (option "show_nats") -> *)
        (*     let s1 = (string_of_raw_term o ss sp st v1) in *)
        (*     let s2 =  (string_of_raw_term_paren o ss sp st v2) in *)
        (*     fmt "%s+%s" s1 s2 *)
        | App(v1,v2) ->
            let s1 = (string_of_raw_term o ss sp st v1) in
            let s2 =  (string_of_raw_term_paren o ss sp st v2) in
            fmt "%s %s" s1 s2
        | Struct(fields,p,t) ->
            fmt "{ %s }%s%s" (string_of_list " ; " (function d,v -> fmt "%s = %s" d (string_of_raw_term o ss sp st v) ) fields) (sp p) (st t)
        | Sp(v,t) -> (ss o v) ^ (st t)
    end
and
  (* same function as above, but adds parenthesis when the argument is not atomic *)
  string_of_raw_term_paren (o:'o) (ss:'o -> 'a -> string) sp st (v:('a,'p,'t) raw_term) =
    try string_of_term_int o ss sp st true v with Invalid_argument "string_of_term_int" ->
    try string_of_term_list o ss sp st true v with Invalid_argument "string_of_term_list" ->
    try string_of_term_tuple o ss sp st v with Invalid_argument "string_of_term_tuple" ->
        if is_atomic_term v
        then string_of_raw_term o ss sp st v
        else ("(" ^ (string_of_raw_term o ss sp st v) ^ ")")
and
  (* try showing the term as an integer *)
  string_of_term_int (o:'o) (ss:'o -> 'a -> string) sp st (p:bool) (v:('a,'p,'t) raw_term) =
    let rec aux n v =
        match v with
        | Const("Zero",_,_) -> n,None
        | App(Const("Succ",_,_),v) -> aux (n+1) v
        | _ -> n,Some v
    in
        if not (option "show_nats")
        then raise (Invalid_argument "string_of_term_int")
        else
            match aux 0 v with
                | n,None -> string_of_int n
                | 0,Some v -> raise (Invalid_argument "string_of_term_int")
                | n,Some v -> if p
                              then "(" ^ (string_of_raw_term o ss sp st v) ^ "+" ^ (string_of_int n) ^ ")"
                              else (string_of_raw_term o ss sp st v) ^ "+" ^ (string_of_int n)

and
  (* try showing the term as a list *)
  string_of_term_list (o:'o) (ss:'o -> 'a -> string) sp st (p:bool) (v:('a,'p,'t) raw_term) =
    let rec aux l v =
        match v with
        | Const("Nil",_,_) -> l,None
        | App(App(Const("Cons",_,_),h),t) -> aux (h::l) t
        | _ -> l,Some v
    in
        if not (option "show_lists")
        then raise (Invalid_argument "string_of_term_list")
        else
            match aux [] v with
                | l,None -> "[" ^ (String.concat "; " (List.map (string_of_raw_term o ss sp st) (List.rev l))) ^ "]"
                | [],Some v -> raise (Invalid_argument "string_of_term_list")
                | l,Some v -> if p
                              then "(" ^ (String.concat "::" (List.map (string_of_raw_term o ss sp st) (List.rev l))) ^ "::" ^ (string_of_raw_term o ss sp st v) ^ ")"
                              else String.concat "::" (List.map (string_of_raw_term_paren o ss sp st) (List.rev l)) ^ "::" ^ (string_of_raw_term_paren o ss sp st v)
and
  (* try showing the term as a tuple *)
  string_of_term_tuple (o:'o) (ss:'o -> 'a -> string) sp st (u:('a,'p,'t) raw_term) =
    if not (option "show_tuples")
    then raise (Invalid_argument "string_of_term_tuple")
    else
        match get_head u, get_args u with
            | Const(c,p,_), args when Str.string_match (Str.regexp "Tuple_\\(0\\|[1-9][0-9]*\\)") c 0 ->
                    let n = int_of_string (String.sub c 6 ((String.length c) - 6)) in
                    if List.length args = n
                    then ("(" ^ (string_of_list ", " (string_of_raw_term o ss sp st) args) ^ ")")
                    else raise (Invalid_argument "string_of_term_tuple")
            | _ -> raise (Invalid_argument "string_of_term_tuple")


(* generic printing function for terms with priorities *)
let string_of_plain_term v = string_of_raw_term () (fun o s -> s.bot) (k "") (k "") v
let string_of_term v = string_of_raw_term () (fun o s -> s.bot) string_of_priority (k "") v

(* showing sct term with approximations *)
let string_of_weight w = match w with
    | Infty -> "∞"
    | Num n -> (string_of_int n)

let string_of_coeff (c:coeff) : string
  = fmt "<%s>" (string_of_list "," (function p,w -> (string_of_weight w)^(string_of_priority p)) c)

let string_of_approx_term (v:approx_term) : string
  =
    let string_of_approx_term_aux
      = string_of_raw_term ()
            (fun o u ->
                match u with
                    (* the only AppRes in such terms should come first and is
                     * dealt with before calling string_of_approx_term_aux *)
                    | AppRes c -> assert false
                    | AppArg [] -> assert false
                    | AppArg l ->
                        (string_of_list " + "
                                        (function x,c ->  fmt "%s%s" (string_of_coeff c) x)
                                        l)
            )
            string_of_priority
            (k "") (* don't show any type information *)
    in

    match v with
        | Sp(AppRes c,_) ->
           fmt ".<%s>" (string_of_coeff c)
        | v -> string_of_approx_term_aux v

(* show an SCT pattern *)
let string_of_sct_pattern ((f,ps):sct_pattern) : string =
    (* let f = Var(f,()) in *)
    (* let v = match implode (f::ps) with *)
    (*             | App(v,Sp(AppRes(p,w),t),t') -> App(Sp(AppRes(p,w),t),v,t') *)
    (*             | v -> v *)
    (* in *)
    (* string_of_approx_term v *)
    fmt "%s, %s"
        f
        (string_of_list ", " string_of_approx_term ps)

(* show an SCT clause *)
let string_of_sct_clause (l,r:sct_clause) : string =
    fmt "%s => %s" (string_of_sct_pattern l) (string_of_sct_pattern r)


(* show a term with unfolded parts, because the types unfolded_struct and
 * unfolded_term are mutually recursive, the functions string_of_unfolded_struct
 * and string_of_unfolded_term are mutually recursive as well *)
(* let rec *)
(*    string_of_unfolded_struct (indent:int) (v:('p,'t) frozen_struct) = *)
(*        let prefix = if indent > 0 then "\n" ^ String.make indent ' ' else "" *)
(*        in *)
(*        (1* let new_indent = if indent > 0 then indent + 4 else 0 *1) *)
(*        (1* in *1) *)

(*        match v with *)
(*        | Frozen(n,fields) -> *)
(*             prefix ^ "{<" ^ (string_of_int n) ^ ">" ^ *)
(*             (1* (if option "show_term_struct" then ("=" ^ string_of_plain_term v) else "") ^ *1) *)
(*             (1* (if option "show_type_struct" then let t = type_of v in (":" ^ string_of_type t) else "") ^ *1) *)
(*             (string_of_list " ; " (function d,t -> fmt "%s = %s" d (string_of_plain_term t)) fields) ^ *) 
(*             "}" *)
(*        (1* | Unfolded fields -> *1) *)
(*        (1*      prefix ^ "{" ^ *1) *)
(*        (1*      prefix ^ "  " ^ (String.concat (";"^prefix^"  ") *1) *)
(*        (1*                              (List.map (function d,v -> *1) *)
(*        (1*                                              fmt "%s = %s" *1) *)
(*        (1*                                                  d *1) *)
(*        (1*                                                  (string_of_unfolded_term new_indent v)) *1) *)
(*        (1*                                        fields)) ^ *1) *)
(*        (1*      "}" *1) *)
(* and *)
let  string_of_unfolded_term indent v
  = string_of_raw_term indent
                       (fun indent t -> match t with Frozen(n,v) -> fmt "<%d:%s>" n (string_of_plain_term v))
                       (k "")
                       (k "")
                       v

let string_of_unfolded_term v = string_of_unfolded_term 2 v

let  string_of_frozen_term indent v
  = string_of_raw_term indent
                       (fun indent t -> match t with Frozen(v) -> fmt "<%s>" (string_of_plain_term v))
                       (k "")
                       (k "")
                       v
let string_of_frozen_term v = string_of_frozen_term 2 v

(* show case / structures trees *)
let rec
    string_of_case_struct_tree (indent:int) (sv:'v->string) (v:'v case_struct_tree) =
        let prefix = if indent > 0 then "\n" ^ String.make indent ' ' else ""
        in
        let new_indent = if indent > 0 then indent + 4 else 0
        in
        match v with
        | CSFail -> "FAIL"
        | CSCase(x,ds,l) ->
             prefix ^ (fmt "case %s%s of" x (string_of_list "" (fun d -> "."^d)ds)) ^
             prefix ^ (String.concat prefix
                                     (List.map (function c,(args,v) -> fmt "  %s%s  ->  %s" c (if args=[] then "" else " " ^ String.concat " " args) (string_of_case_struct_tree new_indent sv v)) l))
        | CSStruct fields ->
             prefix ^ "{" ^
             prefix ^ "  " ^ (String.concat (" ;"^prefix^"  ")
                                     (List.map (function d,v -> d ^ " = " ^ (string_of_case_struct_tree new_indent sv v)) fields)) ^
            " }"
        | CSLeaf(v) -> sv v
let string_of_case_struct_term v = string_of_case_struct_tree 2 string_of_plain_term v


(* show a typed terms with type annotations on all subterms *)
let string_of_typed_term v
  =
    let i = ref 0 in
    let new_i () = incr i ; !i in
    let all_types = ref [] in

    let show_type t =
        let n = new_i() in
        all_types := (n,t)::!all_types;
        string_of_exp n
    in

    let s_term = string_of_raw_term () (fun o s -> s.bot) (k "") show_type v in
    let s_types = string_of_list "\n" (function k,t -> fmt "  - %d: %s" k (string_of_type t)) (List.rev !all_types) in
    fmt "%s\nwith:\n%s\n" s_term s_types

(* misc utility function *)
let string_of_type_substitution sigma = string_of_list " , " (function x,t -> fmt "'%s=%s" x (string_of_type t)) sigma
let string_of_term_substitution sigma = string_of_list " , " (function x,t -> fmt "%s=%s" x (string_of_plain_term t)) sigma
let string_of_context gamma = string_of_list " , " (function x,t -> fmt "%s:%s" x (string_of_type t)) gamma


(***
 * showing the environment
 *)
let show_data_type env tname params consts =
    print_string "  ";
    print_string tname;
    print_list "(" "," ")" (fun x -> print_string ("'" ^ x)) params;
    print_string " where";
    print_list "\n    | " "\n    | " "\n"
               (function c -> print_string (fmt "%s : %s" c (string_of_type (get_constant_type env c))) ;)
               consts

let show_type_bloc env types
  =
    let rec show_type_bloc_aux types
      = match types with
            | [] -> assert false
            | [(tname,_,params,consts)] ->
                    show_data_type env tname params consts;
            | (tname,_,params,consts)::types ->
                    begin
                        show_data_type env tname params consts;
                        print_string "and\n";
                        show_type_bloc_aux types
                    end
    in
    match types with
        | [] -> assert false
        | (_,n,_,_)::_ ->
            if even n
            then print_endline "codata"
            else print_endline "data";
            show_type_bloc_aux types;
            print_newline()


let show_types env =
    let type_blocs = partition (function _,(n:bloc_nb),_,_ -> n) (List.rev env.types) in
    match type_blocs with
        | [] -> warning "no type in environment"
        | type_blocs ->
            msg "types in environment:";
            List.iter (show_type_bloc env) type_blocs;
            flush_all()


let show_function f t clauses (args,cst) =
    print_string (fmt "   %s : %s" f (string_of_type t));
    print_list "\n    | " "\n    | " "\n"
                (function pattern,term -> print_string (fmt "%s = %s" (string_of_term pattern) (string_of_term term)))
                clauses;
    if (verbose 2)
    then
        let tmp = if args = [] then "" else (string_of_list " " id args) ^ " -> " in
        msg "\ncorresponding case and struct form:\n%s%s" tmp (string_of_case_struct_term cst)

let show_function_bloc env funs
  =
    let rec show_function_bloc_aux funs
      = match funs with
            | [] -> assert false
            | [ (f,_,t,clauses,cst) ] ->
                show_function f t clauses cst
            | (f,_,t,clauses,cst)::funs ->
                    begin
                        show_function f t clauses cst;
                        print_string "and\n";
                        show_function_bloc_aux funs
                    end
    in
    match funs with
        | [] -> assert false
        | funs ->
            print_endline "val";
            show_function_bloc_aux funs;
            print_newline()

let show_functions env =
    let fun_blocs = partition (function _,(n:bloc_nb),_,_,_ -> n) (List.rev env.functions) in
    match fun_blocs with
        | [] -> warning "no function in environment";
        | funs ->
            msg "functions in environment:";
            List.iter (show_function_bloc env) funs;
            flush_all()

let show_environment env =
    let type_blocs = partition (function _,(n:bloc_nb),_,_ -> n) (List.rev env.types) in
    let fun_blocs = partition (function _,(n:bloc_nb),_,_,_ -> n) (List.rev env.functions) in
    let rec show_env_aux types funs =
        match types,funs with
            | [],[] -> ()
            | types,[] -> List.iter (show_type_bloc env) types; flush_all()
            | [],funs -> List.iter (show_function_bloc env) funs; flush_all()
            | (((_,nt,_,_)::_) as t_bloc)::types , ((_,nf,_,_,_)::_)::_ when nt<nf ->
                    show_type_bloc env t_bloc;
                    show_env_aux types funs
            | ((_,nt,_,_)::_)::_ , (((_,nf,_,_,_)::_) as f_bloc)::funs when nt>nf ->
                    show_function_bloc env f_bloc;
                    show_env_aux types funs
            | ((_,nt,_,_)::_)::_ , ((_,nf,_,_,_)::_)::_ (*when nt=nf*) -> assert false
            | []::_,_ | _,[]::_ -> assert false
    in
    show_env_aux type_blocs fun_blocs


