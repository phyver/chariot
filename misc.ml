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


(***
 * several miscelaneaus small functions that don't really go anywhere
 *)

let first (f:'a -> 'x) (x,y:'a*'b) : 'x*'b
  = (f x, y)
let second (f:'b -> 'x) (x,y:'a*'b) : 'a*'x
  = (x, f y)

let even (n:int) : bool = (n mod 2) = 0
let odd (n:int) : bool = not (even n)       (* works for negative numbers *)

let string_of_list (sep:string) (s:'a->string) (l:'a list) : string
  = String.concat sep (List.map s l)

let rec print_list (b1:string) (sep:string) (b2:string) (p:'a -> unit) (l:'a list) : unit
  = match l with
        | [] -> ()
        | [x] -> print_string b1; p x; print_string b2
        | x::xs -> print_string b1; p x; List.iter (fun x -> print_string sep; p x) xs; print_string b2

let print_bool (b:bool) : unit
  = if b
    then print_string "true"
    else print_string "false"

(* remove duplicates *)
(* not as efficient as the sorting version, but it keeps the order of the first occurences of the list *)
let uniq (l:'a list) : 'a list
  = let rec uniq_aux acc l
      = match l with
            | [] -> List.rev acc
            | x::xs when List.mem x acc -> uniq_aux acc xs
            | x::xs -> uniq_aux (x::acc) xs
  in
  uniq_aux [] l

(* insert in a sorted uniq list *)
let rec insert (x:'a) (l:'a list) : 'a list
  = match l with
        | [] -> [x]
        | y::l when x<y -> x::y::l
        | y::l when x>y -> y::(insert x l)
        | y::l (* when x=y *) -> y::l

(* merge two sorted uniq lists *)
let rec merge_uniq (l1:'a list) (l2:'a list) : 'a list
  = match l1,l2 with
        | [],l | l,[] -> l
        | x1::l1,x2::_ when x1<x2 -> x1::(merge_uniq l1 l2)
        | x1::_,x2::l2 when x1>x2 -> x2::(merge_uniq l1 l2)
        | x1::l1,x2::l2 (* when x1=x2 *) -> x1::(merge_uniq l1 l2)

(* look for a value with at least two occurences *)
let find_dup (l:'a list) : 'a option
  = let rec find_dup_aux l = match l with
            | [] -> None
            | [a] -> None
            | a::b::_ when a=b -> Some a
            | a::b::l -> find_dup_aux (b::l)
    in
    find_dup_aux (List.sort compare l)

(* look for a value that appears in the two lists *)
let find_common (l1:'a list) (l2:'a list) : 'a option
  = let rec find_common_aux l1 l2
      = match l1,l2 with
            | [],_ | _,[] -> None
            | x1::_,x2::_ when x1=x2 -> Some x1
            | x1::l1,x2::_ when x1<x2 -> find_common_aux l1 l2
            | x1::_,x2::l2 (*when x1>x2*) -> find_common_aux l1 l2
    in
    find_common_aux (List.sort compare l1) (List.sort compare l2)

(* find a value that appears in l1 but not in l2 *)
let find_in_difference (l1:'a list) (l2:'a list) : 'a option
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
let exp_of_int (n:int) : string
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
let sub_of_int (n:int) : string
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
let rec combine_suffix (short:'a list) (long:'b list) : ('a*'b) list * 'b list
  = match short,long with
        | [],l -> [],l
        | _,[] -> raise (Invalid_argument "combine_suffix")
        | a::short,b::long -> let l,s = combine_suffix short long in ((a,b)::l,s)

(* repeat a value into a list of given length *)
let rec repeat (x:'a) (n:int) : 'a list =
    if n = 0
    then []
    else x::(repeat x (n-1))

(* return a list containing a range of values *)
let range (a:int) (b:int) : int list
  = let rec range_aux acc b
      = if b<a
        then acc
        else range_aux (b::acc) (b-1)
    in
    range_aux [] b


(* format a string using printf notation *)
let fmt s = Printf.sprintf s

let todo s = raise (Failure ("-- TODO -- " ^ (fmt s)))


(* print a string (in printf format) on a channel, adding a prefix on each line *)
let print_prefix (out_channel:out_channel) (prefix:string) fmt
  = let print s
      = let s = Str.global_replace (Str.regexp_string "\n") ("\n"^prefix) s
        in
        Printf.fprintf out_channel "%s%s\n" prefix s;
        flush_all()
    in
    Printf.ksprintf print fmt

(* adds ansi codes around string to obtain the given color (or underline attribute) *)
(* probably not very portable... *)
let ansi_code (color:string) (s:string) :string
  = let codes =
        [
            "red",       "\x1b[31m";
            "green",     "\x1b[32m";
            "yellow",    "\x1b[33m";
            "blue",      "\x1b[34m";
            "magenta",   "\x1b[35m";
            "cyan",      "\x1b[36m";
            "underline", "\x1b[4m" ;
        ] in
    let end_code = "\x1b[0m" in
    try
        let begin_code = List.assoc color codes in
        let s = Str.global_replace (Str.regexp_string end_code) (end_code ^ begin_code) s in
        Printf.sprintf "%s%s%s" begin_code s end_code
    with Not_found -> raise (Invalid_argument ("ansi_code: color " ^ color ^ " doesn't exist"))

(* various helper function to print messages *)
let msg fmt
  = print_prefix stdout "-- " fmt

let warning fmt
  = let prefix = ansi_code "cyan" "--!! " in
    print_prefix stdout prefix fmt

let errmsg fmt
  = let prefix = ansi_code "red" "--** " in
    print_prefix stdout prefix fmt

let debug fmt
  = let prefix = ansi_code "yellow" "--== " in
    print_prefix stdout prefix fmt

