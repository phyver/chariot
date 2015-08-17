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
open Pretty
open Misc

let rec subst_term sigma (v:term) : term
  = match v with
    | Var(x,t) -> (try List.assoc x sigma with Not_found -> Var(x,t))
    | Angel _ | Const _ | Proj _ -> v
    | App(v1,v2,t) -> App(subst_term sigma v1, subst_term sigma v2,t)
    | Special(v,t) -> v.bot

(* FIXME: check 't parameter??? *)
let rec equal_term v1 v2 = match v1,v2 with
    | Var(x,_),Var(y,_) -> x=y
    | Angel _,Angel _ -> true
    | App(v11,v12,_),App(v21,v22,_) -> (equal_term v11 v21) && (equal_term v12 v22)
    | Proj(d1,_,_),Proj(d2,_,_) -> d1=d2
    | Const(c1,_,_),Const(c2,_,_) -> c1=c2
    | _,_ -> false

let unify_pattern (pattern,def:term*term) (v:term) : term
  = (* the function defined by the pattern: this variable cannot be instantiated! *)
    let f = get_function_name pattern in

    let rec unify_aux (eqs:(term*term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when equal_term s t -> unify_aux eqs acc
            | (App(u1,v1,_),App(u2,v2,_))::eqs -> unify_aux ((u1,u2)::(v1,v2)::eqs) acc
            | (Var(_f,_), _)::_ when _f = f -> unificationError "cannot unify the function name"
            | (Var(x,_), v)::eqs ->
                    let eqs = List.map (function u1,u2 -> (subst_term [x,v] u1, subst_term [x,v] u2)) eqs in
                    let acc = List.map (function _x,_u -> (_x, subst_term [x,v] _u)) acc in
                    unify_aux eqs ((x,v)::acc)
            | (Special(v,_),_)::_ | (_,Special(v,_))::_ -> v.bot
            | _ -> unificationError "cannot unify"

    in
    let sigma = unify_aux [pattern,v] [] in
    subst_term sigma def

(* NOTE: very inefficient *)
let reduce_all (env:environment) (v:term) : term
  =
    (* look for the first clause that can be used to reduce u
     * the boolean in the result indicates if a reduction was made *)
    let rec reduce_first_clause (v:term) clauses : term*bool =
        match clauses with
            | [] -> v,false
            | clause::clauses ->
                begin
                    try
                        let new_term = unify_pattern clause v in
                        new_term,true
                    with UnificationError _ -> reduce_first_clause v clauses
                end
    and
      reduce v = match v with
          | Var(f,_) -> (try reduce_first_clause v (get_function_clauses env f) with Not_found -> v,false)
          | Const _ | Angel _ | Proj _ -> v,false
          | App(v1,v2,t) -> 
                let v1,b1 = reduce v1 in
                let v2,b2 = reduce v2 in
                let v3,b3 = (try reduce_first_clause (App(v1,v2,t)) (get_function_clauses env (get_function_name v))
                             with Invalid_argument "no head function" | Not_found -> App(v1,v2,t),b1||b2) in
                v3, b1||b2||b3
          | Special(v,_) -> v.bot
    in

    let rec aux v =
      let v,b = reduce v in
      if b then aux v else v
    in

    aux v
