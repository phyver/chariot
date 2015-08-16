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
open Base
open State

let string_of_priority p = match p with
    (* | None ->  "⁽⁾" *)
    (* | None ->  "⁻" *)
    | None ->  if (option "use_ansi_codes") then ansi_code "red" "⁼" else "⁼"
    | Some p -> if (option "use_ansi_codes") then ansi_code "green" (exp_of_int p) else (exp_of_int p)

(* TODO: with product, we need to add parenthesis *)
let is_atomic_type = function
    | TVar _ -> true
    | Data(t,params) when (option "show_tuples") && (Str.string_match (Str.regexp "prod_\\(0\\|[1-9][0-9]*\\)") t 0) ->
        let n = int_of_string (String.sub t 5 ((String.length t) - 5)) in
        not ((List.length params = n) && (n > 1))
    | Data(t,params) -> true
    | Arrow _ -> false

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

let rec print_type t = print_string (string_of_type t)

let rec is_atomic_term (v:'a special_term) = match v with
    | Var _ | Angel | Const _ | Proj _ -> true
    | App(Proj _, v) -> is_atomic_term v
    | App _ -> false
    | Special v -> true

let rec
  string_of_term_int (sp:'a -> string) (p:bool) (u:'a special_term) =
    let rec aux n v =
        match v with
        | Const("Zero",_) -> n,None
        | App(Const("Succ",_),v) -> aux (n+1) v
        | _ -> n,Some v
    in
        if not (option "show_nats")
        then raise (Invalid_argument "string_of_term_int")
        else
            match aux 0 u with
                | n,None -> string_of_int n
                | 0,Some v -> raise (Invalid_argument "string_of_term_int")
                | n,Some v -> if p
                              then "(" ^ (string_of_special_term sp v) ^ "+" ^ (string_of_int n) ^ ")"
                              else (string_of_special_term sp v) ^ "+" ^ (string_of_int n)

and
  string_of_term_list (sp:'a -> string) (p:bool) (u:'a special_term) =
    let rec aux l v =
        match v with
        | Const("Nil",_) -> l,None
        | App(App(Const("Cons",_),h),t) -> aux (h::l) t
        | _ -> l,Some v
    in
        if not (option "show_lists")
        then raise (Invalid_argument "string_of_term_list")
        else
            match aux [] u with
                | l,None -> "[" ^ (String.concat "; " (List.map (string_of_special_term sp) (List.rev l))) ^ "]"
                | [],Some v -> raise (Invalid_argument "string_of_term_list")
                | l,Some v -> if p
                              then "(" ^ (String.concat "::" (List.map (string_of_special_term sp) (List.rev l))) ^ "::" ^ (string_of_special_term sp v) ^ ")"
                              else String.concat "::" (List.map (string_of_term_paren sp) (List.rev l)) ^ "::" ^ (string_of_term_paren sp v)

and
  string_of_term_tuple (sp:'a -> string) (u:'a special_term) =
    if not (option "show_tuples")
    then raise (Invalid_argument "string_of_term_tuple")
    else
        match get_head u, get_args u with
            | Const(c,p), args when Str.string_match (Str.regexp "Tuple_\\(0\\|[1-9][0-9]*\\)") c 0 ->
                    let n = int_of_string (String.sub c 6 ((String.length c) - 6)) in
                    if List.length args = n
                    then ("(" ^ (string_of_list ", " (string_of_special_term sp) args) ^ ")")
                    else raise (Invalid_argument "string_of_term_tuple")
            | _ -> raise (Invalid_argument "string_of_term_tuple")

and
  string_of_term_paren (sp:'a -> string) (v:'a special_term) =
    try string_of_term_int sp true v with Invalid_argument "string_of_term_int" ->
    try string_of_term_list sp true v with Invalid_argument "string_of_term_list" ->
    try string_of_term_tuple sp v with Invalid_argument "string_of_term_tuple" ->
        if is_atomic_term v
        then string_of_special_term sp v
        else ("(" ^ (string_of_special_term sp v) ^ ")")

and
  string_of_special_term (sp:'a -> string) (v:'a special_term) =
    try string_of_term_int sp false v with Invalid_argument "string_of_term_int" ->
    try string_of_term_list sp false v with Invalid_argument "string_of_term_list" ->
    try string_of_term_tuple sp v with Invalid_argument "string_of_term_tuple" ->
        begin
        match v with
            | Angel -> "⊤"
            | Var(x) -> x
            | Const(c,p) -> c ^ (if not (option "show_priorities") then "" else string_of_priority p)
            | Proj(d,p) -> "." ^ d ^  (if not (option "show_priorities") then "" else string_of_priority p)
            | App(Proj _ as v1,v2) -> (string_of_term_paren sp v2) ^ (string_of_special_term sp v1)
            | App(App(Var("add"),v1),v2) when (option "show_nats") -> (string_of_special_term sp v1) ^ "+" ^ (string_of_term_paren sp v2)   (* TODO: don't show add as + in pattern *)
            | App(v1,v2) -> (string_of_special_term sp v1) ^ " " ^ (string_of_term_paren sp v2)
            | Special v -> sp v
        end

let string_of_term = string_of_special_term (fun s -> s.bot)

let print_term t = print_string (string_of_term t)


let string_of_weight w = match w with
    | Infty -> "∞"
    | Num n -> (string_of_int n)

let string_of_approx_term
  = string_of_special_term
        (function | ApproxProj(p,w) ->
                        "<" ^ (string_of_weight w) ^ ">" ^ (string_of_priority p) ^ " ."
                        (* in if (option "use_ansi_codes") then ansi_code "underline" s else s *)
                  | ApproxConst [] ->
                        "∅"
                        (* in if (option "use_ansi_codes") then ansi_code "underline" s else s *)
                  | ApproxConst l ->
                        (string_of_list " + " (function p,w,x ->  "<" ^ (string_of_weight w) ^ ">" ^ (string_of_priority p) ^ " " ^ x) l)
                        (* in if (option "use_ansi_codes") then ansi_code "underline" s else s *)
        )


let show_data_type env tname params consts =
    print_string "  ";
    print_string tname;
    print_list "(" "," ")" (fun x -> print_string ("'" ^ x)) params;
    print_string " where";
    print_list "\n    | " "\n    | " "\n"
               (function c -> print_string c; print_string " : "; print_type (get_constant_type env c) ;)
               consts

let string_of_sct_clause (l,r) =
    fmt "%s  =>  %s" (string_of_approx_term l) (string_of_approx_term r)

let show_types env =

    let rec showtypesaux = function
        | [] -> assert false
        | [(tname,params,_,consts)] -> show_data_type env tname params consts;
        | (tname,params,n,consts)::(((_,_,_n,_)::_) as types) when _n=n ->
                begin
                    show_data_type env tname params consts;
                    print_string "and\n";
                    showtypesaux types
                end
        | (tname,params,_,consts)::(((_,_,p,_)::_) as types) ->
                begin
                    show_data_type env tname params consts;
                    print_newline();
                    if even p
                    then print_string "codata\n"
                    else print_string "data\n";
                    showtypesaux types
                end


    in match List.rev env.types with
        | [] -> print_string "(* ===  no type in environment  ======================= *)\n"
        | ((_,_,n,_)::_) as types ->
                print_string "\n(* ===  types in environment  ======================= *)\n";
                if even n
                then print_string "codata\n"
                else print_string "data\n";
                showtypesaux types;
                print_string "\n(* ================================================== *)\n\n"


let show_function f t clauses =
    print_string "   ";
    print_string f;
    print_string " : ";
    print_type t;
    print_list "\n    | " "\n    | " "\n"
                (function pattern,term -> print_term pattern; print_string " = "; print_term term)
                clauses

let show_functions env =
    let rec showfunctionsaux = function
        | [] -> ()
        | [ (f,_,t,clauses) ] -> show_function f t clauses
        | (f,m,t,clauses)::((_,n,_,_)::_ as defs) when m=n ->
            begin
                show_function f t clauses;
                print_string "and\n";
                showfunctionsaux defs
            end
        | (f,m,t,clauses)::((_,n,_,_)::_ as defs) ->
            begin
                show_function f t clauses;
                print_newline ();
                print_string "val\n";
                showfunctionsaux defs
            end
    in
        print_string "(* ===  functions in environment  =================== *)\n";
        print_string "val\n";
        showfunctionsaux (List.rev env.functions);
        print_string "\n(* ================================================== *)\n\n"
