open Base
open Pretty
open Misc


let rec partition f l = match l with
    | [] -> []
    | [x] -> [[x]]
    | x::((y::_) as l) when f x = f y ->
            (match partition f l with l1::ls -> (x::l1)::ls | _ -> assert false)
    | x::l -> [x]::(partition f l)

let get_constants env (c:const_name) : const_name list =
    let rec get_aux = function
        | [] -> error ("constant " ^ c ^ " doesn't exist")
        | (_,_,_,consts)::_ when List.mem c consts -> consts
        | _::types -> get_aux types
    in get_aux env.types


let term_to_patterns (v:term) : term list
  =
    let rec p = function
        | Var(x) -> Var(x)
        | Const(c,p) -> Const(c,p)
        | Proj _ | Angel | App(Proj _,_) -> assert false
        | App(v1,v2) -> App(p v1,p v2)
        | Special v -> v.bot
    in

    let rec aux = function
        | Var _ | Const _ -> []
        | Proj _ | Angel -> assert false
        | App(Proj(d,p),v) -> (aux v) @ [(Proj(d,p))]
        | App(v1,v2) -> (aux v1) @ [p v2]
        | Special v -> v.bot
    in
    aux v

(* NOTE: I don't need to look at the RHS of definitions if I don't want to "compile" my terms to CASE-definitions *
 * I can only look at the LHS definition and don't need to use any substitution... *)
let  isVar = function
      | Var _::_ -> 0
      | (Proj _)::_ -> 1
      |  _::_ -> 2
      | [] -> 3
let rec
  (* raise Exit if all patterns are matched, returns () otherwise *)
  cover env (ps:term list list) : unit =
(* print_string "cover patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      match List.filter (function [] -> false | _ -> true) ps with
        | [] -> raise Exit
        | ps -> List.iter (coverVarConstProj env) (partition isVar ps)
and
  (* all the patterns in ps start with the same kind (Var, Const, Proj) of pattern
   * This function just calls the appropriate function on ps *)
  coverVarConstProj env (ps:term list list) : unit =
(* print_string "coverVarConstProj patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      match ps with
    | [] -> assert false
    | []::ps -> assert false
    | ((Var _)::_)::_ -> coverVar env ps
    | (Proj(d,p)::_)::_ -> coverProj env ps d
    | (p::_)::_ -> coverConst env ps (get_head_const p)
and
  (* all the patterns in ps start with a variable: we remove it and continue... *)
  coverVar env (ps:term list list) : unit =
(* print_string "coverVar patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      cover env (List.map List.tl ps)
and
  (* all the patterns in ps start with a projection: *)
  coverProj env (ps:term list list) (d:const_name) : unit =
(* print_string "coverProj patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      let allprojs = get_constants env d in
      let projs = List.map (function Proj(d,_)::_ -> d | _ -> assert false) ps in
(* print_list "" "projs: " "," "\n" print_string projs; *)
(* print_list "" "allprojs: " "," "\n" print_string allprojs; *)
      match find_in_difference allprojs projs with
        | None -> cover env (List.map List.tl ps)
        | Some p -> ()
and
  (* all the patterns in ps start with a constructor: *)
  coverConst env (ps:term list list) c =
(* print_string "coverConst patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      let allconsts = get_constants env c in
      let consts = List.map (function p::_ -> get_head_const p | _ -> assert false) ps in
(* print_list "" "consts: " "," "\n" print_string consts; *)
(* print_list "" "allconsts: " "," "\n" print_string allconsts; *)
      match find_in_difference allconsts consts with
        | None -> cover env (List.map (function p::ps -> (term_to_patterns p)@ps | _ -> assert false) ps)
        | Some p -> ()

let exhaustive env clauses =
    let ps = List.map (function lhs,_ -> term_to_patterns lhs) clauses in
    try
        cover env ps;
        false
    with Exit -> true

