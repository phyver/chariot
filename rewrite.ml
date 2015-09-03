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


open Misc
open Env
open Utils
open State
open Pretty
open Typing

let rec equal_term (v1:(empty,'p,'t) raw_term) (v2:(empty,'p,'t) raw_term) : bool
  = match v1,v2 with
    | Var(x,_),Var(y,_) -> x=y
    | Angel _,Angel _ -> true
    | Daimon _,Daimon _ -> true
    | App(v11,v12),App(v21,v22) -> (equal_term v11 v21) && (equal_term v12 v22)
    | Proj(d1,_,_),Proj(d2,_,_) -> d1=d2
    | Const(c1,_,_),Const(c2,_,_) -> c1=c2
    | Sp(s,_),_ | _,Sp(s,_) -> assert false
    | _,_ -> false

(* NOTE: the types in substerms don't mean much as they are unchanged by substitutions *)
let unify_pattern (pattern,def:(empty,'p,'t) raw_term*(empty,'p,'t) raw_term) (v:(empty,'p,'t) raw_term) : (empty,'p,'t) raw_term
  = (* the function defined by the pattern: this variable cannot be instantiated! *)
    (* FIXME: ugly *)
    let f = get_function_name pattern in

    let rec unify_aux (eqs:((empty,'p,'t) raw_term*(empty,'p,'t) raw_term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when equal_term s t -> unify_aux eqs acc
            | (App(u1,v1),App(u2,v2))::eqs -> unify_aux ((u1,u2)::(v1,v2)::eqs) acc
            | (Var(_f,_), _)::_ when _f = f -> unificationError "cannot unify the function name"
            | (Var(x,_), v)::eqs ->
                    let eqs = List.map (function u1,u2 -> (subst_term [x,v] u1, subst_term [x,v] u2)) eqs in
                    let acc = List.map (function _x,_u -> (_x, subst_term [x,v] _u)) acc in
                    unify_aux eqs ((x,v)::acc)
            | (Sp(v,_),_)::_ | (_,Sp(v,_))::_ -> v.bot
            | _ -> unificationError "cannot unify"

    in
    let sigma = unify_aux [pattern,v] [] in
    subst_term sigma def

(* NOTE: very inefficient *)
let rewrite_all (env:environment) (v:(empty,'p,'t) raw_term) : (empty,'p,'t) raw_term
  =
    (* NOTE: types aren't used during computation, but the type is infered
     * again once the normal form is reached.
     * FIXME: note that "take 0 [1;2;3]" of type list(nat) rewrites to "[]" of
     * type list('a) *)

    let counter = ref 0 in

    (* look for the first clause that can be used to rewrite u
     * the boolean in the result indicates if a reduction was made *)
    let rec rewrite_first_clause (v:(empty,'p,'t) raw_term) clauses : (empty,'p,'t) raw_term =
        match clauses with
            | [] -> v
            | clause::clauses ->
                begin
                    try
                        let new_term = unify_pattern clause v in
                        incr counter;
                        new_term
                    with UnificationError _ -> rewrite_first_clause v clauses
                end
    and
      rewrite (v:(empty,'p,'t) raw_term) : (empty,'p,'t) raw_term
        = match v with
          | Var(f,_) -> (try rewrite_first_clause v (get_function_clauses env f)
                         with Not_found -> v)
          | Const _ | Angel _ | Daimon _ | Proj _ -> v
          | App(v1,v2) ->
                let v1 = rewrite v1 in
                let v2 = rewrite v2 in
                let v3 = (try rewrite_first_clause (App(v1,v2)) (get_function_clauses env (get_function_name v))
                             with Invalid_argument "no head function" | Not_found -> App(v1,v2)) in
                v3
          | Sp(v,_) -> v.bot
    in

    let rec aux v =
        let n = !counter in
        let v = rewrite v in
        if n = !counter
        then ((if verbose 1 then msg "%d reductions" n); v)
        else aux v
    in

    let v = aux v in
    let _,v,_ = infer_type_term env v in
    v
