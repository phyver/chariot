open Misc
open Base

let print_exp n = print_string (exp_of_int n)

let rec print_list empty b1 sep b2 p = function
    | [] -> print_string empty;
    | [x] -> print_string b1; p x; print_string b2
    | x::xs -> print_string b1; p x; List.iter (fun x -> print_string sep; p x) xs; print_string b2

let rec print_type = function
    | TVar(x) -> print_string @$ "'" ^ x
    | Data(t,args,p) ->
            print_string t;
            (*if p > 0 then*) print_exp p;
            print_list "" "(" "," ")" print_type args
    | Arrow((TVar _ | Data _) as t1,t2) ->
            print_type t1;
            print_string " → ";
            print_type t2
    | Arrow(t1,t2) ->
            print_string "(" ; print_type t1; print_string ")";
            print_string " → ";
            print_type t2

let rec is_atomic = function
    | Var _ | Angel | Const _ | Proj _ -> true
    | App(Proj _, v) -> is_atomic v
    | App _ -> false

let rec
  print_term_int u =
    let rec aux n v =
        match v with
        | Const("Zero",_) -> n,None
        | App(Const("Succ",_),v) -> aux (n+1) v
        | _ -> n,Some v
    in
        match aux 0 u with
            | n,None -> print_int n
            | 0,Some v -> raise (Invalid_argument "print_term_int")
            | n,Some v -> print_term v; print_string "+"; print_int n

and
  print_paren_term v =
    try
        print_term_int v
    with Invalid_argument "print_term_int" ->
        if is_atomic v
        then print_term v
        else (print_string "("; print_term v; print_string ")")

and
  print_term v =
    try
        print_term_int v
    with Invalid_argument "print_term_int" ->
        begin
        match v with
            | Angel -> print_string "⊤"
            | Var(x) -> print_string x
            | Const(c,p) -> print_string c; print_exp p
            | App(Proj _ as v1,v2) -> print_paren_term v2; print_term v1
            | App(v1,v2) -> print_term v1; print_string " "; print_paren_term v2
            | Proj(d,p) -> print_string "." ; print_string d; print_exp p
        end

let show_data_type env tname params priority consts =
    print_string "  ";
    print_string tname;
    print_list "" "(" "," ")" print_string params;
    print_string " where";
    print_list "\n"
               "\n    | " "\n    | " "\n"
               (function c -> print_string c; print_exp priority; print_string " : "; print_type (get_constant_type env c) ;)
               consts

let show_types env =

    let rec showtypesaux = function
        | [] -> assert false
        | [(tname,params,priority,consts)] -> show_data_type env tname params priority consts;
        | (tname,params,priority,consts)::(((_,_,p,_)::_) as types) when priority=p ->
                begin
                    show_data_type env tname params priority consts;
                    print_string "and\n";
                    showtypesaux types
                end
        | (tname,params,priority,consts)::(((_,_,p,_)::_) as types) ->
                begin
                    show_data_type env tname params priority consts;
                    print_newline();
                    if p mod 2 = 0
                    then print_string "codata\n"
                    else print_string "data\n";
                    showtypesaux types
                end


    in match List.rev env.types with
        | [] -> print_string "(* ===  no type in environment  ======================= *)\n"
        | ((_,_,priority,_)::_) as types ->
                print_string "\n(* ===  types in environment  ======================= *)\n";
                if priority mod 2 = 0
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
