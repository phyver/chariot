
let ( @$ ) f x = f x

let  first f (x,y) = (f x, y)
let second f (x,y) = (x, f y)


(* look for a value with at least two occurences *)
let uniq l =
    let rec aux = function
        | [] -> None
        | [a] -> None
        | a::b::_ when a=b -> Some a
        | a::b::l -> aux (b::l)
    in aux (List.sort compare l)

(* look for a value that appears in the two lists *)
let common l1 l2 =
    let rec aux l1 l2 = match l1,l2 with
        | [],_ | _,[] -> None
        | x1::_,x2::_ when x1=x2 -> Some x1
        | x1::l1,x2::_ when x1<x2 -> aux l1 l2
        | x1::_,x2::l2 (*when x1>x2*) -> aux l1 l2
    in aux (List.sort compare l1) (List.sort compare l2)

(* find a value that appears in l1 but not in l2 *)
let find_in_not_in l1 l2 =
    let rec aux l1 l2 = match l1,l2 with
        | [],_ -> None
        | x::_,[] -> Some x
        | x1::_,x2::_ when x1<x2 -> Some x1
        | x1::l1,x2::_ when x1>x2 -> aux l1 l2
        | x1::l1,x2::l2 (*when x1=x2*) -> aux l1 l2
    in aux (List.sort compare l1) (List.sort compare l2)

let exp_of_int n =
    let exp = ["⁰"; "¹"; "²"; "³"; "⁴"; "⁵"; "⁶"; "⁷"; "⁸"; "⁹"] in
    let rec aux n acc =
        if n = 0
        then acc
        else
            let d = n mod 10 in
            aux (n/10) ((List.nth exp d)::acc)
    in
    String.concat "" (aux n [])

let sub_of_int n =
    let sub = ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"] in
    let rec aux n acc =
        if n = 0
        then acc
        else
            let d = n mod 10 in
            aux (n/10) ((List.nth sub d)::acc)
    in
    String.concat "" (aux n [])

