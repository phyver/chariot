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


open Env
open Utils
open State
open Pretty
open Misc



type match_pattern = type_expression term list

let explode_pattern (v:type_expression term) : match_pattern
  =
    let rec explode_pattern_aux v = match get_head v, get_args v with
        | (Var _ as f), args -> f::args
        | (Proj _ as p), v::args -> (explode_pattern_aux v)@(p::args)
        | _,_ -> assert false
    in
    explode_pattern_aux v

let  is_var = function
      | Var _::_ -> 0
      | (Proj _)::_ -> 1
      |  _::_ -> 2
      | [] -> 3

let choose_constructor (c:const_name) (clauses:(match_pattern*'t term) list)
  : (match_pattern*'t term) list
  = List.filter
        (fun q ->
            match get_head (List.hd (fst q)) with
                | Const(c',_,_) when c=c' -> true
                | Const(c',_,_) (*when c<>c'*) -> false
                | Proj(d,_,_) when c=d -> true
                | Proj(d,_,_) (*when c<>d*) -> false
                | _ -> assert false)
        clauses

let counter = ref 0
let new_var () =
    incr counter;
    "x"^(sub_of_int !counter)

let string_of_clause (pat,def) = fmt "[%s] -> %s" (string_of_list " " s_o_u pat) (s_o_u def)

let rec
convert_match env (xs:var_name list)
                  (clauses:(match_pattern*type_expression term) list)
                  (fail: type_expression case_struct_term)
  : type_expression case_struct_term
  =
    (* debug "clauses: {%s}" (string_of_list "," string_of_clause clauses); *)
      match xs,clauses with
        | [],[] -> fail
        | x::xs,[] -> fail  (* TODO: keep types and check that x is not in a type with 0 constructor *)
        | [],[([],v)] -> map_special_term (fun s->s.bot) identity v
        | [],([],v)::clauses -> debug "TODO: useless case..."; map_special_term (fun s->s.bot) identity v
        (* | [],_ -> assert false *)

        | xs,clauses ->
            let part_clauses = partition (function p,_ -> is_var p) clauses in
            (* debug "part_clauses: %s" (string_of_list "  |  " (fun clauses -> "{" ^ string_of_list ", " string_of_clause clauses ^ "}") part_clauses); *)
            List.fold_right (fun clauses e -> convert_match_aux env xs clauses e) part_clauses fail

  and

convert_match_aux env xs clauses fail
  =
    (* debug "xs: [%s]" (string_of_list ", " identity xs); *)
    (* debug "clauses: {%s}" (string_of_list "," string_of_clause clauses); *)
    match xs,clauses with
        | [],[] -> assert false

        (* variable case *)
        | x::xs,(Var _::_,_)::_ ->
            begin
                let clauses = List.map (fun cl -> match cl with
                                            | (Var(y,t)::ps,def) -> (ps,subst_term [y,Var(x,t)] def)
                                            | _ -> assert false)
                                        clauses
                in
                convert_match env xs clauses fail
            end

        (* projection case *)
        | xs,(Proj(d,_,t)::_,_)::_ ->
            begin
                let constants = get_other_constants env d in
                let struct_fields = List.map
                    (fun d' ->
                        let arity = (get_constant_arity env d') - 1 in
                        let new_xs = repeat () arity in
                        let new_xs = List.map new_var new_xs in

                        let clauses = List.map
                                    (function pat,def ->
                                        get_args (List.hd pat) @ (List.tl pat) , def
                                    )
                                    (choose_constructor d' clauses)
                        in
                        d', (new_xs, convert_match env (new_xs@xs) clauses fail)
                    )
                    constants
                in
                Special(Struct(struct_fields),get_first_arg_type t)
            end

        (* constructor case *)
        | x::xs,(pattern::_,_)::_ ->
            begin
                let c,t = (match get_head pattern with Const(c,_,t) -> c,t | _ -> assert false) in
                let constants = get_other_constants env c in
                let case_clauses = List.map
                    (fun c' ->
                        let arity = get_constant_arity env c' in
                        let new_xs = repeat () arity in
                        let new_xs = List.map new_var new_xs in
                        let clauses = List.map
                                    (function pat,def ->
                                        get_args (List.hd pat) @ (List.tl pat) , def
                                    )
                                    (choose_constructor c' clauses)
                        in
                        c', (new_xs, convert_match env (new_xs@xs) clauses fail)
                    )
                    constants in
                Special(Case(x,case_clauses), get_result_type t)
            end

        | _ -> assert false


let simplify_case_struct v =
    let rec rename sigma v
      = match v with
            | Var(x,t) -> (try Var(List.assoc x sigma,t) with Not_found -> v)
            | Const _ | Proj _ | Angel _ | Special(CaseFail,_)-> v
            | App(v1,v2,t) -> App(rename sigma v1, rename sigma v2, t)
            | Special(Case(x,cases),t) ->
                let x = (try List.assoc x sigma with Not_found -> x) in
                let cases = List.map (function c,(xs,v) -> c,(xs,rename sigma v)) cases in
                (* NOTE: I assume a kind of Barendregt condition is satisfied by the terms... *)
                Special(Case(x,cases), t)
            | Special(Struct(fields),t) ->
                let fields = List.map (function d,(xs,v) -> d,(xs,rename sigma v)) fields in
                (* NOTE: I assume a kind of Barendregt condition is satisfied by the terms... *)
                Special(Struct(fields), t)
    in

    let rec simplify_aux branch v
      = match v with
            | Var _ | Const _ | Proj _ | Angel _ | Special(CaseFail,_) -> v
            | App(v1,v2,t) -> App(simplify_aux branch v1, simplify_aux branch v2, t)
            | Special(Case(x,cases),t) ->
                begin try
                    let c,xs = List.assoc x branch in
                    let ys,v = List.assoc c cases in
                    let v = rename (List.combine ys xs) v in
                    simplify_aux branch v
                with Not_found ->
                    let cases = List.map (function c,(xs,v) -> c,(xs,simplify_aux ((x,(c,xs))::branch) v)) cases in
                    Special(Case(x,cases),t)
                end
            | Special(Struct(fields),t) ->
                Special(Struct(List.map (function d,(xs,v) -> d,(xs,simplify_aux branch v)) fields),t)
    in
    simplify_aux [] v

let is_exhaustive f args v =
    let rec get_failure branch v
      = match v with
            | Var _ | Const _ | Proj _ | Angel _ -> []
            | Special(CaseFail,_) -> [branch]
            | App(v1,v2,_) -> (get_failure branch v1) @ (get_failure branch v2)
            | Special(Case(x,cases),_) ->
                List.concat (List.map (function c,(xs,v) -> get_failure ((x,(c,xs))::branch) v) cases)
            | Special(Struct(fields),_) ->
                List.concat (List.map (function d,(xs,v) -> get_failure ((".",(d,xs))::branch) v) fields)
    in

    let string_of_failure branch =
        let fail = List.fold_right
                        (fun xcxs fail ->
                            match xcxs with
                                | ".",(d,xs) ->
                                    app (Proj(d,None,())) (fail::(List.map (fun x->Var(x,())) xs))
                                | x,(c,xs) ->
                                    let v = app (Const(c,None,())) (List.map (fun x->Var(x,())) xs) in
                                    subst_term [x,v] fail
                        )
                        branch
                        (app
                            (Var(f,()))
                            (List.map (fun x -> Var(x,())) args)
                        )
        in
        string_of_term fail
    in
    match get_failure [] v with
        | [] -> true
        | failures ->
            warning "failures:\n  %s" (string_of_list "\n  " string_of_failure failures);
            false

let add_args_clause args clauses =
    let arity = List.length args in
    let args = List.rev args in
    let rec args_aux n xs acc =
        match n,xs with
            | n,_ when n<=0 -> acc
            | n,x::xs -> args_aux (n-1) xs (x::acc)
            | _,[] -> assert false
    in
    let get_args n = args_aux n args [] in

    List.map (function ps,v ->
        let n = arity - (List.length ps) in
        let xs = get_args n in
        ps@xs, typed_app v xs
    ) clauses


let check_exhaustivity env (t:type_expression) (f:var_name) (clauses:(type_expression pattern*type_expression term) list) : bool
  =
    counter := 0;
    let arity = type_arity t in
    let args = repeat () arity in
    let args = List.map new_var args in
    let targs = get_args_type t in
    let term_args = List.map2 (fun x t -> Var(x,t)) args targs in

    let clauses = List.map (first (fun p -> List.tl (explode_pattern p))) clauses in (* List.tl to remove function name *)
    let clauses = add_args_clause term_args clauses in

    let fail = Special(CaseFail,get_result_type t) in
    let cp = convert_match env args clauses fail in
    (* debug "obtained:\n    %s %s |--> %s" f (string_of_list " " identity args) (string_of_case_struct_term cp); *)
    let cp = simplify_case_struct cp in
    (* debug "after simplification:\n    %s %s |--> %s" f (string_of_list " " identity args) (string_of_case_struct_term cp); *)

    is_exhaustive f args cp
