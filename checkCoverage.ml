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


open Base
open Utils
open Pretty
open Misc



let term_to_patterns (v:type_expression term) : type_expression term list
  =
    let rec aux = function
        | Var _ | Const _ -> []
        | Proj _ | Angel _ -> assert false
        | App(Proj(d,p,t),v,_) -> (aux v) @ [(Proj(d,p,t))]
        | App(v1,v2,_) -> (aux v1) @ [v2]
        | Special(v,t) -> v.bot
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
  cover env (ps:type_expression term list list) : unit =
(* print_string "cover patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      match List.filter (function [] -> false | _ -> true) ps with
        | [] -> raise Exit
        | ps -> List.iter (coverVarConstProj env) (partition isVar ps)
and
  (* all the patterns in ps start with the same kind (Var, Const, Proj) of pattern
   * This function just calls the appropriate function on ps *)
  coverVarConstProj env (ps:type_expression term list list) : unit =
(* print_string "coverVarConstProj patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      match ps with
    | [] -> assert false
    | []::ps -> assert false
    | ((Var _)::_)::_ -> coverVar env ps
    | (Proj(d,p,_)::_)::_ -> coverProj env ps d
    | (p::_)::_ -> coverConst env ps (get_head_const p)
and
  (* all the patterns in ps start with a variable: we remove it and continue... *)
  coverVar env (ps:type_expression term list list) : unit =
(* print_string "coverVar patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      cover env (List.map List.tl ps)
and
  (* all the patterns in ps start with a projection: *)
  coverProj env (ps:type_expression term list list) (d:const_name) : unit =
(* print_string "coverProj patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      let allprojs = get_other_constants env d in
      let projs = List.map (function Proj(d,_,_)::_ -> d | _ -> assert false) ps in
(* print_list "" "projs: " "," "\n" print_string projs; *)
(* print_list "" "allprojs: " "," "\n" print_string allprojs; *)
      match find_in_difference allprojs projs with
        | None -> cover env (List.map List.tl ps)
        | Some p -> ()
and
  (* all the patterns in ps start with a constructor: *)
  coverConst env (ps:type_expression term list list) c =
(* print_string "coverConst patterns:\n"; print_list "empty\n\n" "" "\n" "\n\n" (fun p -> print_list "  --" "  " " , " "" print_term p) ps; *)
      let allconsts = get_other_constants env c in
      let consts = List.map (function p::_ -> get_head_const p | _ -> assert false) ps in
(* print_list "" "consts: " "," "\n" print_string consts; *)
(* print_list "" "allconsts: " "," "\n" print_string allconsts; *)
      match find_in_difference allconsts consts with
        | None -> cover env (List.map (function p::ps -> (term_to_patterns p)@ps | _ -> assert false) ps)
        | Some p -> ()

let check_exhaustivity (env:environment) (clauses:(type_expression pattern*type_expression term) list) : bool
  = let ps = List.map (function lhs,_ -> term_to_patterns lhs) clauses in
    try
        cover env ps;
        false
    with Exit -> true

