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

let rec is_atomic env = function
    | Daimon -> true
    | Var _ -> true
    | Constant _ -> true
    | Apply(Constant c,e2) ->
        begin
            let p = get_constant_priority c env in
            0 = p mod 2 && is_atomic env e2
        end
    | Apply(_,_) -> false

let rec print_term env = function
    | Daimon -> print_string "⊥"
    | Var(x) -> print_string x
    | Constant(c) ->
        begin
            try
                let p = get_constant_priority c env in
                print_string c;
                print_exp p;
            with Not_found -> print_string c;print_string "⁽⁾"
        end
    | Apply(((Constant c) as e1), e2) when is_atomic env e2 ->
        begin
            let p = get_constant_priority c env in
            if p mod 2 = 0
            then (print_term env e2; print_string "."; print_term env e1)
            else (print_term env e1; print_string " "; print_term env e2;)
        end
    | Apply(((Constant c) as e1), e2) ->
        begin
            let p = get_constant_priority c env in
            if p mod 2 = 0
            then (print_string "("; print_term env e2; print_string ")."; print_term env e1)
            else ( print_term env e2; print_string " ("; print_term env e1; print_string ")")
        end
    | Apply(e1,e2) ->
        begin
            if is_atomic env e2
            then (print_term env e1; print_string " "; print_term env e2;)
            else ( print_term env e1; print_string " ("; print_term env e2; print_string ")")
        end

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
                    (function pattern,term -> print_term env pattern; print_string " = "; print_term env term)
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
