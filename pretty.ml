open Misc
open Base
open State

let print_exp n = print_string (exp_of_int n)

let rec string_of_type = function
    | TVar(x) -> "'"^x
    | Data(t,[]) ->
            t
    | Data(t,params) ->
            t ^ "(" ^ (String.concat "," (List.map string_of_type params)) ^ ")"
    | Arrow((TVar _ | Data _) as t1,t2) ->
            (string_of_type t1) ^ " → " ^ (string_of_type t2)
    | Arrow(t1,t2) ->
            "(" ^ (string_of_type t1) ^ ")" ^ " → " ^ (string_of_type t2)

let rec print_type t = print_string (string_of_type t)

let rec is_atomic (v:'a special_term) = match v with
    | Var _ | Angel | Const _ | Proj _ -> true
    | App(Proj _, v) -> is_atomic v
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
        if (option "dont_show_nats")
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
        if (option "dont_show_lists")
        then raise (Invalid_argument "string_of_term_list")
        else
            match aux [] u with
                | l,None -> "[" ^ (String.concat "; " (List.map (string_of_special_term sp) (List.rev l))) ^ "]"
                | [],Some v -> raise (Invalid_argument "string_of_term_list")
                | l,Some v -> if p
                              then "(" ^ (String.concat "::" (List.map (string_of_special_term sp) (List.rev l))) ^ "::" ^ (string_of_special_term sp v) ^ ")"
                              else String.concat "::" (List.map (string_of_special_term sp) (List.rev l)) ^ "::" ^ (string_of_special_term sp v)

and
  string_of_term_paren (sp:'a -> string) (v:'a special_term) =
    try string_of_term_int sp true v with Invalid_argument "string_of_term_int" ->
    try string_of_term_list sp true v with Invalid_argument "string_of_term_list" ->
        if is_atomic v
        then string_of_special_term sp v
        else ("(" ^ (string_of_special_term sp v) ^ ")")

and
  string_of_special_term (sp:'a -> string) (v:'a special_term) =
    try string_of_term_int sp false v with Invalid_argument "string_of_term_int" ->
    try string_of_term_list sp false v with Invalid_argument "string_of_term_list" ->
        begin
        match v with
            | Angel -> "⊤"
            | Var(x) -> x
            | Const(c,None) -> c ^ (if (option "dont_show_priorities") then "" else "⁽⁾")
            | Const(c,Some p) -> c ^ (if (option "dont_show_priorities") then "" else exp_of_int p)
            | Proj(d,None) -> "." ^ d ^  (if (option "dont_show_priorities") then "" else "⁽⁾")
            | Proj(d,Some p) -> "." ^ d  ^ (if (option "dont_show_priorities") then "" else exp_of_int p)
            | App(Proj _ as v1,v2) -> (string_of_term_paren sp v2) ^ (string_of_special_term sp v1)
            | App(App(Var("add"),v1),v2) when not (option "dont_show_nats") -> (string_of_special_term sp v1) ^ "+" ^ (string_of_term_paren sp v2)
            | App(v1,v2) -> (string_of_special_term sp v1) ^ " " ^ (string_of_term_paren sp v2)
            | Special v -> sp v
        end

let string_of_term = string_of_special_term (fun s -> s.bot)

let print_term t = print_string (string_of_term t)


let show_data_type env tname params consts =
    print_string "  ";
    print_string tname;
    print_list "" "(" "," ")" print_string params;
    print_string " where";
    print_list "\n"
               "\n    | " "\n    | " "\n"
               (function c -> print_string c; print_string " : "; print_type (get_constant_type env c) ;)
               consts

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
                    if p mod 2 = 0
                    then print_string "codata\n"
                    else print_string "data\n";
                    showtypesaux types
                end


    in match List.rev env.types with
        | [] -> print_string "(* ===  no type in environment  ======================= *)\n"
        | ((_,_,n,_)::_) as types ->
                print_string "\n(* ===  types in environment  ======================= *)\n";
                if n mod 2 = 0
                then print_string "codata\n"
                else print_string "data\n";
                showtypesaux types;
                print_string "\n(* ================================================== *)\n\n"


let show_function f t clauses =
    print_string "   ";
    print_string f;
    print_string " : ";
    print_type t;
    print_list "\n"
                "\n    | " "\n    | " "\n"
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
