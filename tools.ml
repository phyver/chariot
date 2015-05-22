exception Error of string

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



