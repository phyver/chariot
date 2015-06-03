open Misc
open Base

let print_exp n = print_string (exp_of_int n)

let rec print_list empty b1 sep b2 p = function
    | [] -> print_string empty;
    | [x] -> print_string b1; p x; print_string b2
    | x::xs -> print_string b1; p x; List.iter (fun x -> print_string sep; p x) xs; print_string b2

let rec print_type env = function
    | TVar(x) -> print_string @$ "'" ^ x
    | Data(t,args) ->
            print_string t;
            print_exp (get_type_priority t env);
            print_list "" "(" "," ")" (print_type env) args
    | Arrow((TVar _ | Data _) as t1,t2) ->
            print_type env t1;
            print_string " → ";
            print_type env t2
    | Arrow(t1,t2) ->
            print_string "(" ; print_type env t1; print_string ")";
            print_string " → ";
            print_type env t2


let print_term_int u =
    let rec aux n (App(u,args)) = match u,args with
        | Const("Zero"),[] -> n
        | Const("Succ"),[v] -> aux (n+1) v
        | _ -> raise (Invalid_argument "print_term_int")
    in
        let n = aux 0 u in
        print_int n

let rec
  print_paren_term v =
      match v with
        | App(_,[]) -> print_term v
        | v -> print_string "("; print_term v; print_string ")"

and
  print_atomic_term = function
    | Daimon -> print_string "⊥"
    | Var(x) -> print_string x
    | Const(c) -> print_string c
    | Proj(u,d) -> print_paren_term u; print_string "." ; print_string d
and
  print_term v =
    let (App(u,args)) = v in
    try
        print_term_int v
    with Invalid_argument "print_term_int" -> print_atomic_term u; print_list "" " " " " "" print_paren_term args


let showtypes env =

    let print_data_type tname params priority consts =
        print_string "  ";
        print_string tname;
        print_exp priority;
        print_list "" "(" "," ")" print_string params;
        print_string " where";
        print_list "\n"
                   "\n    | " "\n    | " "\n"
                   (function c -> print_string c; print_exp priority; print_string " : "; print_type env (get_type_const c env) ;)
                   consts
    in

    let rec showtypesaux = function
        | [] -> assert false
        | [(tname,params,priority,consts)] -> print_data_type tname params priority consts;
        | (tname,params,priority,consts)::(((_,_,p,_)::_) as types) when priority=p ->
                begin
                    print_data_type tname params priority consts;
                    print_string "and\n";
                    showtypesaux types
                end
        | (tname,params,priority,consts)::(((_,_,p,_)::_) as types) ->
                begin
                    print_data_type tname params priority consts;
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


let showfunctions env =
    let print_function f t clauses =
        print_string "   ";
        print_string f;
        print_string " : ";
        print_type env t;
        print_list "\n"
                    "\n    | " "\n    | " "\n"
                    (function pattern,term -> print_term pattern; print_string " = "; print_term term)
                    clauses;
    in

    let rec showfunctionsaux = function
        | [] -> ()
        | [ (f,_,t,clauses) ] -> print_function f t clauses
        | (f,m,t,clauses)::((_,n,_,_)::_ as defs) when m=n ->
            begin
                print_function f t clauses;
                print_string "and\n";
                showfunctionsaux defs
            end
        | (f,m,t,clauses)::((_,n,_,_)::_ as defs) ->
            begin
                print_function f t clauses;
                print_newline ();
                print_string "val\n";
                showfunctionsaux defs
            end
    in
        print_string "(* ===  functions in environment  =================== *)\n";
        print_string "val\n";
        showfunctionsaux (List.rev env.functions);
        print_string "\n(* ================================================== *)\n\n"
