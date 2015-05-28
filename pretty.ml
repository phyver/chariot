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

let rec print_list b1 sep b2 p = function
    | [] -> print_string b1; print_string b2
    | [x] -> print_string b1; p x; print_string b2
    | x::xs -> print_string b1; p x; List.iter (fun x -> print_string sep; p x) xs; print_string b2

let print_constant (c:term_constant) =
    print_string c.name;
    if !verbose>0 then print_exp c.priority

let rec print_type = function
    | TVar(false,x) -> print_string x
    | TVar(true,x) -> print_string @$ "_" ^ x
    | Data(t,args) ->
            print_string t;
            (* if !verbose>0 then print_exp t.priority; *)
            print_list "(" "," ")" print_type args
    | Arrow((TVar _ | Data _) as t1,t2) ->
            print_type t1;
            print_string " → ";
            print_type t2
    | Arrow(t1,t2) ->
            print_string "(" ; print_type t1; print_string ")";
            print_string " → ";
            print_type t2

let print_data_type (t,priority,consts) =
    match t with
        | Data(t,args) ->
                if priority mod 2 = 0
                then print_string "co";
                print_string "data\n";
                print_string "  ";
                print_string t;
                print_exp priority;
                print_list "(" "," ")" (fun x -> match x with TVar(true,x) -> print_string x
                                                                | _ -> assert false) args;
                print_string " where";
                print_list "\n    | " "\n    | " "\n" (function c,t -> print_string c.name; print_string " : "; print_type t;) consts
        | _ -> assert false

