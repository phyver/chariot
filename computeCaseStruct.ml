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

let rec reduce env (v:type_expression term) : type_expression term
  =
    let counter = ref 0 in

    let rec explode v
      = let h,args = get_head v,get_args v in
        match h,args with
            | Var _,args | Const _,args | Angel _,args -> h::args
            | Proj _,v::args -> (explode v)@(h::args)
            | Proj _ as p,[] -> [p]
            | App _,_ -> assert false
            | Special(s,_),_ -> s.bot
    in

    let implode args =
        let rec implode_aux args acc
          = match args with
                | [] -> acc
                | (Var(_,t) | Angel(t) | Const(_,_,t) | App(_,_,t) as v)::args -> implode_aux args (App(acc,v,t))
                | (Proj(_,_,t) as v)::args -> implode_aux args (App(v,acc,t))
                | Special(s,_)::args -> s.bot
        in
        match args with
            | [] -> assert false
            | v::args -> implode_aux args v
    in

    let rec extract_value x sigma =
        match sigma with
            | [] -> raise Not_found
            | (y,v)::sigma when x=y -> v,sigma
            | p::sigma -> let v,sigma = extract_value x sigma in v,p::sigma
    in

    (* NOTE: sigma should only contain terms in normal form *)
    let rec rewrite_case_struct
        (sigma:(var_name*type_expression term) list)
        (rest:type_expression term list)
        (cs:type_expression term case_struct_tree)
      : type_expression term case_struct_tree * type_expression term list
      =
        (* debug "rewrite_case_struct %s\nwith sigma=[%s] and rest=[%s]" *)
        (*             (string_of_case_struct_term cs) *)
        (*             (string_of_term_substitution sigma) *)
        (*             (string_of_list "," string_of_term rest); *)
        match cs with
            | CaseFail -> error "match failure"
            | Struct fields ->
                begin
                    match rest with
                        | Proj(d,_,_)::rest ->
                            let xs,cl = (try List.assoc d fields with Not_found -> assert false) in
                            let tau,rest = combine_suffix xs rest in
                            rewrite_case_struct (tau@sigma) rest cl
                        | _ -> raise Exit
                end
            | CSLeaf v ->
                    incr counter;
                    CSLeaf (subst_term sigma v),rest
            | Case(x,clauses) ->
                try
                    let v,sigma = extract_value x sigma in
                    match get_head v,get_args v with
                        | Const(c,_,_),args ->
                            let xs,cl = (try List.assoc c clauses with Not_found -> assert false) in
                            let tau,rest' = combine_suffix xs args in
                            rewrite_case_struct (tau@sigma) (rest'@rest) cl
                        | _ -> error "typing error"
                with Not_found -> assert false
    in

    let rec
    rewrite (v:type_expression term) : type_expression term
      =
        (* debug "rewrite for %s" (s_o_u v); *)
        let args = explode v in
        let h,args = (try List.hd args,List.tl args with _ -> assert false) in
        let args = List.map nf args in
        match h with
            | Const _ | Angel _ -> implode (h::args)

            | App _ -> assert false
            | Special(s,_) -> s.bot
            | Proj(d,_,_) -> assert (args=[]); h

            | Var(f,t) ->
                begin
                    try
                        let xs,csf = get_function_case_struct env f in
                        let sigma,rest = combine_suffix xs args in
                        match rewrite_case_struct sigma rest csf with
                            | CSLeaf v,rest -> implode (v::rest)
                            | _ -> implode (h::args)
                    with Invalid_argument "combine_suffix" -> implode (h::args)
                    | Exit -> implode (h::args)
                end
    and

    nf (v:type_expression term) : type_expression term
      =
        (* debug "nf for %s" (s_o_u v); *)
        let n = !counter in
        let v = rewrite v in
        if n = !counter
        then v
        else nf v
    in

    (* debug "REDUCING term %s" (s_o_u v); *)

    let _,result,_ = infer_type_term env (nf v) in
    if verbose 1 then msg "%d reduction(s) made" !counter;
    result
