let first f (x,y) = (f x, y)
let second f (x,y) = (x, f y)

let rec print_list empty b1 sep b2 p l
  = match l with
        | [] -> print_string empty;
        | [x] -> print_string b1; p x; print_string b2
        | x::xs -> print_string b1; p x; List.iter (fun x -> print_string sep; p x) xs; print_string b2

let string_of_list sep s l = String.concat sep (List.map s l)

(* remove duplicates *)
(* not as efficient as the sorting version, but it keeps the order of the first occurences of the list *)
let uniq l
  = let rec uniq_aux acc l
      = match l with
            | [] -> List.rev acc
            | x::xs when List.mem x acc -> uniq_aux acc xs
            | x::xs -> uniq_aux (x::acc) xs
  in
  uniq_aux [] l

(* look for a value with at least two occurences *)
let find_dup l
  = let rec find_dup_aux l = match l with
            | [] -> None
            | [a] -> None
            | a::b::_ when a=b -> Some a
            | a::b::l -> find_dup_aux (b::l)
    in
    find_dup_aux (List.sort compare l)

(* look for a value that appears in the two lists *)
let find_common l1 l2
  = let rec find_common_aux l1 l2
      = match l1,l2 with
            | [],_ | _,[] -> None
            | x1::_,x2::_ when x1=x2 -> Some x1
            | x1::l1,x2::_ when x1<x2 -> find_common_aux l1 l2
            | x1::_,x2::l2 (*when x1>x2*) -> find_common_aux l1 l2
    in
    find_common_aux (List.sort compare l1) (List.sort compare l2)

(* find a value that appears in l1 but not in l2 *)
let find_in_difference l1 l2
  = let rec find_in_difference_aux l1 l2
      = match l1,l2 with
            | [],_ -> None
            | x::_,[] -> Some x
            | x1::_,x2::_ when x1<x2 -> Some x1
            | x1::_,x2::l2 when x1>x2 -> find_in_difference_aux l1 l2
            | x1::l1,x2::l2 (*when x1=x2*) -> find_in_difference_aux l1 l2
    in
    find_in_difference_aux (List.sort compare l1) (List.sort compare l2)

(* transforms a positive integer into a UTF-8 string of superscripts *)
let exp_of_int n
  = let exp = ["⁰"; "¹"; "²"; "³"; "⁴"; "⁵"; "⁶"; "⁷"; "⁸"; "⁹"]
    in
    let rec exp_of_int_aux n acc
      = if n = 0
        then acc
        else
            let d = n mod 10 in
            exp_of_int_aux (n/10) ((List.nth exp d)::acc)
    in
    let sign = if n<0 then "⁻" else ""
    in
    let n = abs n
    in
    if n=0
    then "⁰"
    else String.concat "" (sign::(exp_of_int_aux n []))

(* transforms a positive integer into a UTF-8 string of subscripts *)
let sub_of_int n
  = let sub = ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"]
    in
    let rec sub_of_int_aux n acc
      = if n = 0
        then acc
        else
            let d = n mod 10 in
            sub_of_int_aux (n/10) ((List.nth sub d)::acc)
    in
    let sign = if n<0 then "₋" else ""
    in
    let n = abs n
    in
    if n=0
    then "₀"
    else String.concat "" (sign::(sub_of_int_aux n []))

(* combine two lists into a list of pairs, and returns the suffix of the second one
 * raise Invalid_argument if the second list is shorter than the first one *)
let rec combine_suffix short long
  = match short,long with
        | [],l -> [],l
        | _,[] -> raise (Invalid_argument "combine_suffix")
        | a::short,b::long -> let l,s = combine_suffix short long in ((a,b)::l,s)

let range a b
  = let rec range_aux acc b
      = if b<a
        then acc
        else range_aux (b::acc) (b-1)
    in
    range_aux [] b

let print_bool b
  = if b
    then print_string "true"
    else print_string "false"

let print_prefix prefix fmt
  = let print s
      = let s = Str.global_replace (Str.regexp_string "\n") ("\n"^prefix) s
        in
        print_endline (prefix ^ s)
    in
    Printf.ksprintf print fmt

let debug fmt
  = print_prefix "-- == " fmt

let msg fmt
  = print_prefix "-- " fmt

let warning fmt
  = print_prefix "-- !! " fmt

let errmsg fmt
  = print_prefix "-- ** " fmt
