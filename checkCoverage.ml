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

(* type cov_term = *)
(*     | Struct of (const_name * cov_term) list *)
(*     | Case of var_name * (conts_name * cov_term) list *)
(*     | Seq of cov_term * cov_term *)
(*     | Fail *)
(*     | Term of term *)

type cpattern =
    | PConst of const_name * cpattern list
    | PVar of var_name
type dpattern = const_name
type pattern = C of cpattern | P of dpattern


let term_to_patterns (v:'a term) : pattern list
  =
    let rec get_pattern (App(u,args)) =
        match u with
            | Angel -> assert false
            | Var(x) -> PVar x
            | Proj _ -> assert false
            | Const(c,_) -> PConst(c,List.map get_pattern args)
    in

    let rec aux (App(u,args)) = match u with
        | Var(f) -> List.map (fun p -> C (get_pattern p)) args
        | Proj(u,d,_) -> (aux u)@(P d)::(List.map (fun p -> C (get_pattern p)) args)

        | Angel -> assert false
        | Const _ -> assert false
    in
    aux v


(* NOTE: I don't need to look at the RHS of definitions if I don't want to "compile" my terms to CASE-definitions *
 * I can only look at the LHS definition and don't need to use any substitution... *)
let  isVar = function
      | (C(PVar _))::_ -> 0
      | (C(PConst _))::_ -> 1
      | (P _)::_ -> 2
      | [] -> 3
let rec
  (* raise Exit if all patterns are matched, returns () otherwise *)
  cover env (ps:pattern list list) : unit =
      match ps with
        | [] -> raise Exit
        | ps -> List.iter (coverVarConstProj env) (partition isVar ps)
and
  (* all the patterns in ps start with the same kind (PVar, PConst, PProj) of pattern.
   * This function just calls the appropriate function on ps *)
  coverVarConstProj env (ps:pattern list list) : unit = match ps with
    | [] -> assert false
    | []::ps -> cover env ps
    | ((C(PVar _))::_)::_ -> coverVar env ps
    | ((C(PConst(c,_)))::_)::_ -> coverConst env ps c
    | ((P d)::_)::_ -> coverProj env ps d
and
  (* all the patterns in ps start with a variable: we remove it and continue... *)
  coverVar env (ps:pattern list list) : unit = cover env (List.map List.tl ps)
and
  (* all the patterns in ps start with a projection: *)
  coverProj env (ps:pattern list list) (d:const_name) : unit =
      let allprojs = get_constants env d in
      let projs = List.map (function (P d)::_ -> d | _ -> assert false) ps in
      match find_in_difference allprojs projs with
        | None -> cover env (List.map List.tl ps)
        | Some p -> ()
and
  (* all the patterns in ps start with a constructor: *)
  coverConst env (ps:pattern list list) c =
      let allconsts = get_constants env c in
      let consts = List.map (function (C(PConst(c,_)))::_ -> c | _ -> assert false) ps in
      match find_in_difference allconsts consts with
        | None -> cover env (List.map (function (C(PConst(c,qs)))::ps -> (List.map (fun x -> C x) qs)@ps | _ -> assert false) ps)
        | Some p -> ()

let exhaustive env clauses =
    let ps = List.map (function lhs,_ -> term_to_patterns lhs) clauses in
    try
        cover env ps;
        false
    with Exit -> true



let rec print_cpattern = function
    | PVar x -> print_string x
    | PConst(c,ps) -> print_string c; print_list "" " " " " "" print_cpattern ps

let print_pattern = function
    | C p -> print_cpattern p
    | P p -> print_string ("." ^ p)

let print_patterns ps = print_list "[]" "[ " " , " " ]" print_pattern ps
