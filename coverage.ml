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



type 'p match_pattern = (empty,'p,type_expression) raw_term list

let explode_pattern (v:(empty,'p,type_expression) raw_term) : 'p match_pattern
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

let choose_constructor (c:const_name) (clauses:(int*'p match_pattern*(empty,'p,type_expression) raw_term) list)
  : (int*'p match_pattern*(empty,'p,type_expression) raw_term) list
  = List.filter
        (fun (_,pat,def) ->
            match get_head (List.hd pat) with
                | Const(c',_,_) when c=c' -> true
                | Const(c',_,_) (*when c<>c'*) -> false
                | Proj(d,_,_) when c=d -> true
                | Proj(d,_,_) (*when c<>d*) -> false
                | _ -> assert false)
        clauses

let counter = ref 0
let new_var () =
    incr counter;
    "x"^(string_of_sub !counter)

let string_of_clause (pat,def) = fmt "[%s] -> %s" (string_of_list " " string_of_plain_term pat) (string_of_plain_term def)

let rec
convert_match env (xs:var_name list)
                  (clauses:(int*'p match_pattern*(empty,'p,type_expression) raw_term) list)
                  (fail: (int*(empty,'p,type_expression) raw_term) case_struct_tree)
  : (int * (empty,'p,type_expression) raw_term) case_struct_tree
  =
    (* debug "clauses: {%s}" (string_of_list "," string_of_clause clauses); *)
      match xs,clauses with
        | [],[] -> fail
        | x::xs,[] -> fail  (* TODO: keep types and check that x is not in a type with 0 constructor *)
        | [],[(n,[],v)] -> CSLeaf(n,map_raw_term (fun s->s.bot) id id v)
        | [],(n,[],v)::clauses ->  CSLeaf(n,map_raw_term (fun s->s.bot) id id v)
        (* | [],_ -> assert false *)

        | xs,clauses ->
            let part_clauses = partition (function _,p,_ -> is_var p) clauses in
            (* debug "part_clauses: %s" (string_of_list "  |  " (fun clauses -> "{" ^ string_of_list ", " string_of_clause clauses ^ "}") part_clauses); *)
            List.fold_right (fun clauses e -> convert_match_aux env xs clauses e) part_clauses fail

  and

convert_match_aux env xs clauses fail
  =
    (* debug "xs: [%s]" (string_of_list ", " id xs); *)
    (* debug "clauses: {%s}" (string_of_list "," string_of_clause clauses); *)
    match xs,clauses with
        | [],[] -> assert false

        (* variable case *)
        | x::xs,(_,Var _::_,_)::_ ->
            begin
                let clauses = List.map (fun cl -> match cl with
                                            | (n,Var(y,t)::ps,def) -> (n,ps,subst_term [y,Var(x,t)] def)
                                            | _ -> assert false)
                                        clauses
                in
                convert_match env xs clauses fail
            end

        (* projection case *)
        | xs,(_,Proj(d,_,t)::_,_)::_ ->
            begin
                let constants = get_other_constants env d in
                let struct_fields = List.map
                    (fun d' ->
                        let arity = (get_constant_arity env d') - 1 in
                        let new_xs = repeat () arity in
                        let new_xs = List.map new_var new_xs in

                        let clauses = List.map
                                    (function n,pat,def ->
                                        n,get_args (List.hd pat) @ (List.tl pat) , def
                                    )
                                    (choose_constructor d' clauses)
                        in
                        d', (new_xs, convert_match env (new_xs@xs) clauses fail)
                    )
                    constants
                in
                CSStruct(struct_fields)
            end

        (* constructor case *)
        | x::xs,(_,pattern::_,_)::_ ->
            begin
                let c,t = (match get_head pattern with Const(c,_,t) -> c,t | _ -> assert false) in
                let constants = get_other_constants env c in
                let case_clauses = List.map
                    (fun c' ->
                        let arity = get_constant_arity env c' in
                        let new_xs = repeat () arity in
                        let new_xs = List.map new_var new_xs in
                        let clauses = List.map
                                    (function n,pat,def ->
                                        n,get_args (List.hd pat) @ (List.tl pat) , def
                                    )
                                    (choose_constructor c' clauses)
                        in
                        c', (new_xs, convert_match env (new_xs@xs) clauses fail)
                    )
                    constants in
                CSCase(x,case_clauses)
            end

        | _ -> assert false


let simplify_case_struct v =
    let rec rename_var_term sigma v = match v with
        | Var(x,t) -> (try Var(List.assoc x sigma,t) with Not_found -> v)
        | Angel _ | Daimon _ | Proj _ | Const _ -> v
        | Sp(s,_) -> s.bot
        | App(v1,v2) -> App(rename_var_term sigma v1,rename_var_term sigma v2)
    in

    let rec rename sigma v
      = match v with
            | CSFail -> CSFail
            (* | Var(x,t) -> (try Var(List.assoc x sigma,t) with Not_found -> v) *)
            (* | Const _ | Proj _ | Angel _ | Sp(CSFail,_)-> v *)
            (* | App(v1,v2) -> App(rename sigma v1, rename sigma v2) *)
            | CSCase(x,cases) ->
                let x = (try List.assoc x sigma with Not_found -> x) in
                let cases = List.map (function c,(xs,v) -> c,(xs,rename sigma v)) cases in
                (* NOTE: I assume a kind of Barendregt condition is satisfied by the terms... *)
                CSCase(x,cases)
            | CSStruct(fields) ->
                let fields = List.map (function d,(xs,v) -> d,(xs,rename sigma v)) fields in
                (* NOTE: I assume a kind of Barendregt condition is satisfied by the terms... *)
                CSStruct(fields)
            | CSLeaf(n,v) -> CSLeaf(n,rename_var_term sigma v)
    in

    let rec simplify_aux branch v
      = match v with
            | CSFail -> CSFail
            | CSCase(x,cases) ->
                begin try
                    let c,xs = List.assoc x branch in
                    let ys,v = List.assoc c cases in
                    let v = rename (List.combine ys xs) v in
                    simplify_aux branch v
                with Not_found ->
                    let cases = List.map (function c,(xs,v) -> c,(xs,simplify_aux ((x,(c,xs))::branch) v)) cases in
                    CSCase(x,cases)
                end
            | CSStruct(fields) ->
                CSStruct(List.map (function d,(xs,v) -> d,(xs,simplify_aux branch v)) fields)
            | CSLeaf v -> CSLeaf v
    in
    simplify_aux [] v


let is_exhaustive f args v =
    let rec get_failure branch v
      = match v with
            | CSLeaf _ -> []
            | CSFail -> [branch]
            | CSCase(x,cases) ->
                List.concat (List.map (function c,(xs,v) -> get_failure ((x,(c,xs))::branch) v) cases)
            | CSStruct(fields) ->
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
        string_of_plain_term fail
    in
    match get_failure [] v with
        | [] -> true
        | failures ->
            warning "match failures:\n  %s" (string_of_list "\n  " string_of_failure failures);
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

    List.map (function n,ps,v ->
        let a = arity - (List.length ps) in
        let xs = get_args a in
        n,ps@xs, app v xs
    ) clauses

let rec remove_clause_numbers cs
  = match cs with
            | CSCase(x,cases) -> CSCase(x,List.map (function c,(xs,cs) -> c,(xs,remove_clause_numbers cs)) cases)
            | CSStruct(fields) -> CSStruct(List.map (function d,(xs,cs) -> d,(xs,remove_clause_numbers cs)) fields)
            | CSFail -> CSFail
            | CSLeaf(n,v) -> CSLeaf(v)

let extract_clause_numbers cs
  = let rec extract_clause_numbers_aux cs
      = match cs with
            | CSCase(_,cases) | CSStruct(cases) -> List.concat (List.map (function _,(_,cs) -> extract_clause_numbers_aux cs) cases)
            | CSFail -> []
            | CSLeaf(n,v) -> [n]
    in uniq (extract_clause_numbers_aux cs)

let convert_cs_to_clauses (f:var_name) (xs:var_name list) (cs:(empty,'p,type_expression) raw_term case_struct_tree)
  : ((empty, unit, unit) raw_term * (empty, 'p, unit) raw_term) list
  (* I need unit for priorities on the left because I need to invent priorities in the convert_cs_to_clauses_aux function *)
  = 
    let rec convert_cs_to_clauses_aux pat (cs:(empty,'p,type_expression) raw_term case_struct_tree)
      = match cs with
        | CSFail -> []
        | CSLeaf(v) -> [pat,map_type_term (fun t->()) v]
        | CSCase(x,cases) ->
            List.concat (List.map (function c,(xs,cs) ->
                                let xs = List.map (function x->Var(x,())) xs in
                                let c = app (Const(c,(),())) xs in
                                let pat = subst_term [x,c] pat in
                                convert_cs_to_clauses_aux pat cs)
                            cases)
        | CSStruct(fields) ->
            List.concat (List.map (function d,(xs,cs) ->
                                let xs = List.map (function x->Var(x,())) xs in
                                let d = Proj(d,(),()) in
                                let pat = implode (pat::d::xs) in
                                convert_cs_to_clauses_aux pat cs)
                            fields)
    in

    let pat = app (Var(f,())) (List.map (fun x -> Var(x,())) xs) in

    let clauses = convert_cs_to_clauses_aux pat cs in

    (* debug "new clauses:\n  %s" (string_of_list "\n  " (function p,d -> fmt "%s => %s" (string_of_plain_term p) (string_of_plain_term d)) clauses); *)

    clauses


let rec map_case_struct f v = match v with
    | CSFail -> CSFail
    | CSStruct fields -> CSStruct (List.map (function d,(xs,v) -> d,(xs,map_case_struct f v)) fields)
    | CSCase(x,cases) -> CSCase(x,(List.map (function c,(xs,v) -> c,(xs,map_case_struct f v)) cases))
    | CSLeaf v -> CSLeaf (f v)

let process_empty_clause env (args:(var_name*type_expression) list) (tres:type_expression)
  : var_name list * (empty,unit,type_expression) raw_term case_struct_tree
  = let xs = List.map fst args in

    let rec process_args args = match args with
        | (x,Data(tname,_))::_ when is_inductive env tname && get_type_constants env tname = [] ->
            xs, CSCase(x,[])
        | _::args -> process_args args
        | [] -> xs,CSFail
    in

    match tres with
        | Data(tname,_) when not (is_inductive env tname) && get_type_constants env tname = [] ->
            xs, CSStruct []
        | _ -> process_args args

let case_struct_of_clauses
        env
        (f:var_name)
        (t:type_expression)
        (clauses:((empty,'p,type_expression) raw_term*(empty,'p,type_expression) raw_term) list)
    : var_name *
      ((empty,'p,type_expression) raw_term *
      (empty,'p,type_expression) raw_term) list *
      var_name list *
      (empty,unit,type_expression) raw_term case_struct_tree
  =
    (* debug "case_struct_of_clauses for function %s" f; *)
    counter := 0;
    let arity = type_arity t in
    let args = repeat () arity in
    let args = List.map new_var args in
    let targs = get_args_type t in
    let term_args = List.map2 (fun x t -> Var(x,t)) args targs in

    let clauses = List.map2 (fun n cl -> n,fst cl,snd cl) (range 1 (List.length clauses)) clauses in

    match clauses with
        | [] ->
            let t_res = get_result_type t in
            let args,cs = process_empty_clause env (List.map (function Var(x,t) -> x,t | _ -> assert false) term_args) t_res in
            f,[],args,cs
        | clauses ->
            let cs =
                let fail = CSFail in
                let clauses = List.map (function n,p,def -> n,List.tl (explode_pattern p),def) clauses in (* List.tl to remove function name *)
                let clauses = add_args_clause term_args clauses in
                convert_match env args clauses fail
            in

            (* debug "obtained:\n    %s %s |--> %s" f (string_of_list " " id args) (string_of_case_struct_term cs); *)
            let cs = simplify_case_struct cs in
            (* debug "after simplification:\n    %s %s |--> %s" f (string_of_list " " id args) (string_of_case_struct_term cs); *)

            let ns = extract_clause_numbers cs in
            let clauses = List.filter
                (function n,pat,def ->
                    if not (List.mem n ns)
                    then (
                        warning "useless clause %d: %s = %s" n (string_of_plain_term pat) (string_of_plain_term def); option "keep_useless_clauses")
                    else true)
                clauses
            in

            let clauses = List.map (function _,lhs,rhs-> lhs,rhs) clauses in
            let cs = remove_clause_numbers cs in

            f,clauses,args,map_case_struct (fun v -> map_raw_term (fun s->s.bot) (k()) id v) cs

