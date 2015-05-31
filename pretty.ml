open Misc
open Base

let verbose = ref 0

let print_exp n =
    let exp = ["⁰"; "¹"; "²"; "³"; "⁴"; "⁵"; "⁶"; "⁷"; "⁸"; "⁹"] in
    let rec aux n acc =
        if n = 0
        then acc
        else
            let d = n mod 10 in
            aux (n/10) ((List.nth exp d)::acc)
    in
    List.iter print_string (aux n [])

let print_sub n =
    let sub = ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"] in
    let rec aux n acc =
        if n = 0
        then acc
        else
            let d = n mod 10 in
            aux (n/10) ((List.nth sub d)::acc)
    in
    List.iter print_string (aux n [])

let rec print_list empty b1 sep b2 p = function
    | [] -> print_string empty;
    | [x] -> print_string b1; p x; print_string b2
    | x::xs -> print_string b1; p x; List.iter (fun x -> print_string sep; p x) xs; print_string b2

let print_constant (c:const_name) (p:priority) =
    print_string c;
    if !verbose>0 then print_exp p

let rec print_type env = function
    | TVar(false,x) -> print_string @$ "'_" ^ x
    | TVar(true,x) -> print_string @$ "'" ^ x
    | Data(t,args) ->
            print_string t;
            print_exp (get_priority t env);
            print_list "" "(" "," ")" (print_type env) args
    | Arrow((TVar _ | Data _) as t1,t2) ->
            print_type env t1;
            print_string " → ";
            print_type env t2
    | Arrow(t1,t2) ->
            print_string "(" ; print_type env t1; print_string ")";
            print_string " → ";
            print_type env t2

let rec print_term = function
    | Var(x) -> print_string x
    | Constant(c) -> print_string c
    | Apply(e1,((Var _ | Constant _) as e2)) -> print_term e1; print_string " "; print_term e2
    | Apply(e1,e2) -> print_term e1; print_string " ("; print_term e2; print_string ")"

let showtypes env =

    let print_data_type tname params priority consts =
        print_string "  ";
        print_string tname;
        print_exp priority;
        print_list "" "(" "," ")" print_string params;
        print_string " where";
        print_list "\n" "\n    | " "\n    | " "\n" (function c -> print_string c; print_exp priority; print_string " : "; print_type env (get_type_const c env) ;) consts
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
    | [] -> ()
    | ((_,_,priority,_)::_) as types ->
            if priority mod 2 = 0
            then print_string "codata\n"
            else print_string "data\n";
            showtypesaux types
