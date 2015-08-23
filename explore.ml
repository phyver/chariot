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
open Base
open State
open Pretty
open Compute
open Typing

let rec head_to_explore (v:type_expression term) : explore_term = match v with
    | Angel t -> Angel t
    | Var(x,t) -> Var(x,t)
    | Proj(d,p,t) -> Proj(d,p,t)
    | Const(c,p,t) -> Const(c,p,t)
    | Special(v,t) -> v.bot
    | App(v1,v2,t) -> assert false

let struct_nb = ref 0

let rec term_to_explore_aux (env:environment) (v:type_expression term) : explore_term
  = let t = type_of v in
    let hd,args = get_head v, get_args v in
     match t with
        | Data(tname,_) as t ->
            if (is_inductive env tname)
            then
                typed_app (head_to_explore hd) (List.map (term_to_explore_aux env) args)
            else
                (incr struct_nb; Special (Folded(!struct_nb,v),t))
        | Arrow _ | TVar _ ->
            typed_app (head_to_explore hd) (List.map (term_to_explore_aux env) args)

let term_to_explore env v = struct_nb := 0; term_to_explore_aux env (reduce_all env v)


let rec unfold (env:environment) (p:int->bool) (v:explore_term) : explore_term
 =  match v with
        | Angel _ | Var _ | Proj _ | Const _ -> v
        | App(v1,v2,t) -> App(unfold env p v1, unfold env p v2,t)
        | Special(Unfolded fields,t) -> Special (Unfolded (List.map (second (unfold env p)) fields),t)
        | Special(Folded(n,v),t) when not (p n) -> incr struct_nb; Special(Folded(!struct_nb,v),t)
        | Special(Folded(n,v),Data(tname,_)) when (p n) ->
                let consts = get_type_constants env tname in
                let fields = List.map (fun d ->
                    let v = App(Proj(d,None,todo"???"),v,todo"???") in
                    let v = reduce_all env v in
                    (d, term_to_explore_aux env v)) consts
                in
                Special(Unfolded fields,todo"???")
        | Special _ -> assert false

let unfold env p v = struct_nb:=0; unfold env p v

let rec unfold_to_depth env v depth
 =  if depth = 0
    then term_to_explore env v
    else
        let v = unfold_to_depth env v (depth-1) in
        unfold env (fun _ -> true) v

let explore_term_depth (env:environment) (v:type_expression term) (depth:int) : unit
  = print_explore_term (unfold_to_depth env v depth)

