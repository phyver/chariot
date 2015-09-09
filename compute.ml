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

let rec reduce env (v:(empty,'p,'t) raw_term) : plain_term frozen_term
  =

    let counter = ref 0 in

    (* remove Frozen constructors *)
    let rec unfreeze (v:plain_term frozen_term) : plain_term
      = match v with
        | Angel() -> Angel()
        | Daimon() -> Daimon()
        | Const(c,(),()) -> Const(c,(),())
        | Proj(d,(),()) -> Proj(d,(),())
        | Var(x,()) -> Var(x,())
        | App(v1,v2) -> App(unfreeze v1,unfreeze v2)
        | Struct(fields,(),()) -> Struct(List.map (second unfreeze) fields,(),())
        | Sp(Frozen(v),()) -> v
    in

    (* add Frozen constructors in structures *)
    let rec freeze (v:plain_term) : plain_term frozen_term
      = match v with
        | Angel() -> Angel()
        | Daimon() -> Daimon()
        | Const(c,(),()) -> Const(c,(),())
        | Proj(d,(),()) -> Proj(d,(),())
        | Var(x,()) -> Var(x,())
        | App(v1,v2) -> App(freeze v1,freeze v2)
        | Struct(fields,(),()) -> Struct(List.map (function d,v -> d,Sp(Frozen v,())) fields,(),())
        | Sp(s,_) -> s.bot
    in

    (* substitution on frozen terms *)
    let rec subst_frozen_term sigma (v:plain_term frozen_term) : plain_term frozen_term
      = match v with
        | Var(x,t) -> (try List.assoc x sigma with Not_found -> Var(x,t))
        | Angel t -> Angel t
        | Daimon t -> Daimon t
        | Const(c,p,t) -> Const(c,p,t)
        | Proj(d,p,t) -> Proj(d,p,t)
        | App(v1,v2) -> App(subst_frozen_term sigma v1, subst_frozen_term sigma v2)
        | Struct(fields,p,t) -> Struct(List.map (second (subst_frozen_term sigma)) fields,p,t)
        | Sp(Frozen(v),t) -> Sp(Frozen(subst_term (List.map (second unfreeze) sigma) v),t)      (* we need to unfreeze below the first Frozen constructor *)
    in

    let rec
    normal_form (v:plain_term frozen_term) : plain_term frozen_term
      =
        (* debug "nf %s (counter:%d)" (string_of_unfolded_term v) !counter ; *)
        let n = !counter in
        let v = rewrite v in
        if n = !counter
        then v
        else normal_form v

    and
    rewrite (v:plain_term frozen_term) : plain_term frozen_term
      = let args = get_args v in
        let args = List.map normal_form args in
        let h = get_head v in
        (* debug "h = %s ; args = %s" (string_of_unfolded_term h) (string_of_list ", " string_of_unfolded_term args); *)
        (* let h = normal_form h in *)
        match h with
            | Angel _ -> Angel()
            | Daimon _ -> raise Exit
            | Const _ -> app h args
            | Sp(Frozen _,_) | Struct _ -> app h args
            | App _ -> assert false
            | Proj(d,_,_) ->
                begin
                    let st = try List.hd args with Failure "hd" -> assert false in
                    match st with
                        | Struct(fields,_,_) ->
                            begin
                                let v = try List.assoc d fields with Not_found -> assert false in
                                (* let v = unfreeze v in *)
                                match v with
                                    | Sp(Frozen(v),()) -> normal_form (map_raw_term bot id id v)
                                    | v -> normal_form v
                            (* | Sp(Frozen v,_) -> *)
                            (*     let v = remove_struct v in *)
                            (*     rewrite (app h (v::(List.tl args))) *)
                            end
                        | _ -> assert false
                end
            | Var(f,_) ->
                begin
                    try
                        let xs,ct = get_function_case_struct env f in
                        let sigma,rest_args = combine_suffix xs args in
                        let ct = map_case_struct (map_raw_term id id (k())) ct in
                        incr counter;
                        let v = subst_case sigma ct in
                        app v rest_args
                    with
                        | Not_found -> debug "OOPS f=%s" f; assert false
                        | Invalid_argument "combine_suffix" -> app h args
                end

    and
    subst_case (sigma:(var_name * plain_term frozen_term) list) ct
      : plain_term frozen_term
      =
        (* debug "ct = %s with sigma = %s" (string_of_case_struct_term ct) (string_of_list ", " (function x,t -> fmt "%s=%s" x (string_of_frozen_term t)) sigma); *)
        match ct with
            | CSFail -> error "match failure"
            | CSLeaf v ->
                let v = freeze v in
                subst_frozen_term sigma v
            | CSStruct(fields) ->
                (* debug "fields1 = %s" (string_of_list " ; " (function d,t -> fmt "%s=%s" d (string_of_unfolded_term t)) sigma); *)
                let fields = List.map (second (subst_case sigma)) fields in
                let fields = List.map (second unfreeze) fields in
                let fields = List.map (function d,v -> d,Sp(Frozen(v),())) fields in
                (* debug "fields2 = %s" (string_of_list " ; " (function d,t -> fmt "%s=%s" d (string_of_unfolded_term t)) sigma); *)
                Struct(fields,(),())
            | CSCase(x,ds,cases) ->
                let v = try List.assoc x sigma with Not_found -> assert false in
                let v = implode (v::(List.map (fun d -> Proj(d,(),())) ds)) in
                let v = normal_form v in
                match get_head v,get_args v with
                    | Const(c,_,_),args ->
                        let xs,ct = try List.assoc c cases with Not_found -> assert false in
                        let tau = List.combine xs args in
                        subst_case (sigma@tau) ct
                    | _ -> assert false
    in

    try
        let v:plain_term frozen_term = map_raw_term bot (k()) (k()) v in
        let result = normal_form v in
        if verbose 2 then msg "%d reduction%s made" !counter (if !counter > 1 then "s" else "");
        result
    with Exit ->
        if verbose 2 then msg "%d reduction%s made" !counter (if !counter > 1 then "s" else "");
        Daimon()

