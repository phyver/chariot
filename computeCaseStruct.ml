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

(* Map instance for meoizing computation *)
module Memo = Map.Make (struct type t=(empty,unit,type_expression) raw_term let compare=compare end)

let rec reduce env (v:(empty,unit,type_expression) raw_term) : (empty,unit,type_expression) raw_term
  =
    let counter = ref 0 in
    let table = ref Memo.empty in

    let rec extract_value x sigma =
        match sigma with
            | [] -> raise Not_found
            | (y,v)::sigma when x=y -> v,sigma
            | p::sigma -> let v,sigma = extract_value x sigma in v,p::sigma
    in

    (* NOTE: sigma should only contain terms in normal form *)
    let rec rewrite_case_struct
        sigma
        (rest:(empty,unit,type_expression) raw_term list)
        (cs:(empty,unit,type_expression) raw_term case_struct_tree)
      : (empty,unit,type_expression) raw_term case_struct_tree * (empty,unit,type_expression) raw_term list
      =
        match cs with
            | CSFail -> error "match failure"
            | CSStruct fields ->
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
            | CSCase(x,clauses) ->
                try
                    let v,sigma = extract_value x sigma in
                    match get_head v,get_args v with
                        | Const(c,_,_),args ->
                            let xs,cl = (try List.assoc c clauses with Not_found -> assert false) in
                            let tau,rest' = combine_suffix xs args in
                            rewrite_case_struct (tau@sigma) (rest'@rest) cl
                        | _ -> error (fmt "typing error with %s" (string_of_plain_term v))
                with Not_found -> assert false
    in

    let rec
    rewrite (v:(empty,unit,type_expression) raw_term) : (empty,unit,type_expression) raw_term
      =
        (* debug "rewrite %s" (string_of_plain_term v); *)
        try
            let result,n = Memo.find v !table
            in counter := !counter+n;
            result
        with Not_found ->
            let counter0 = !counter in
            let result =
                let args = explode v in
                let h,args = (try List.hd args,List.tl args with _ -> assert false) in
                let args = List.map nf args in
                match h with
                    | Const _ | Angel _ | Daimon _ -> implode (h::args)

                    | App _ -> assert false
                    | Sp(s,_) -> s.bot
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
                               | Not_found -> implode (h::args) (* f was a free variable *)
                        end
            in
            table := Memo.add v (result,!counter-counter0) !table;    (* TODO provokes a problem for pow 1 (pow 1 1) *)
            result
    and

    nf (v:(empty,unit,type_expression) raw_term) : (empty,unit,type_expression) raw_term
      =
        let n = !counter in
        let v = rewrite v in
        if n = !counter
        then v
        else nf v
    in

    let _,result,_ = infer_type_term env (nf v) in
    if verbose 2 then msg "%d reduction%s made" !counter (if !counter > 1 then "s" else "");
    result
