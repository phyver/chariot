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

let rec subst_struct_term sigma v
    = match v with
        | Angel _ | Daimon _ | Const _ | Proj _ -> v
        | App(v1,v2) -> App(subst_struct_term sigma v1, subst_struct_term sigma v2)
        | Var(x,()) -> (try List.assoc x sigma with Not_found -> v)
        | Sp(Struct fs,()) -> Sp(Struct (List.map (function d,v -> d,subst_struct_term sigma v) fs),())

let aux_function_counter = ref 0
let new_aux () = incr aux_function_counter; Var("_aux"^(string_of_sub !aux_function_counter),())

let aux_functions = ref []

let remove_match_struct (clauses:((unit,'t) struct_term*(unit,'t) struct_term) list)
  : (plain_term*(unit,'t) struct_term) list
  =

    let arg_counter = ref 0 in
    let new_var () = incr arg_counter; "x"^(string_of_sub !arg_counter) in

    let rec process_arg (pat:(unit,'t) struct_term)
      :  plain_term * (var_name*(unit,'t) struct_term) list
      = match pat with
            | Var(x,()) -> let y=new_var() in Var(y,()),[y,Var(x,())]
            | Angel _ | Daimon _ -> assert false
            | Const(c,p,()) -> Const(c,p,()),[]
            | Proj(d,p,()) -> Proj(d,p,()),[]
            | App(u1,u2) ->
                let u1,sigma1=process_arg u1 in
                let u2,sigma2=process_arg u2 in
                App(u1,u2), sigma1@sigma2
            | Sp(Struct fields,()) -> let y=new_var() in Var(y,()),[y,Sp(Struct fields,())]
    in

    let process_clause_aux (lhs,rhs:(unit,'t) struct_term*(unit,'t) struct_term)
      : (plain_term*(unit,'t) struct_term) * ((unit,'t) struct_term*(unit,'t) struct_term) option
      =
        arg_counter := 0;

        let f,lhs_pattern =
            match explode lhs with f::args -> f,args | [] -> assert false in

        (* we need to change the type of f from (unit,'t) struct_term to plain_term *)
        let f = match f with Var(f,()) -> Var(f,()) | _ -> assert false in

        (* process the lhs *)
        let lhs_pattern,sigma =
            let tmp = List.map process_arg lhs_pattern in
            List.map fst tmp, List.concat (List.map snd tmp)
        in


        if List.for_all (function _,Var _ -> true | _,_ -> false) sigma
        then begin
            (map_raw_term (fun _ -> assert false) id id lhs, rhs) , None
        end
        else
            let lhs = implode (f::lhs_pattern) in
            let f_aux = try List.assoc lhs !aux_functions
                        with Not_found ->
                            let f_aux=new_aux() in
                            aux_functions := (lhs,f_aux)::!aux_functions;
                            f_aux
            in
            let args_aux = List.concat (List.map
                                (function
                                    | y,Var(x,()) -> [Var(y,())]
                                    | y,Sp(Struct fields,()) -> List.map (function d,_ -> App(Proj(d,(),()),Var(y,()))) fields
                                    | _ -> assert false
                                )
                                sigma
                           )
            in
            let new_rhs = implode (f_aux::args_aux) in

            let new_args_aux = List.concat (List.map
                                (function
                                    | y,Var(x,()) -> [Var(x,())]
                                    | y,Sp(Struct fields,()) -> List.map (function _,v -> v) fields
                                    | _ -> assert false
                                )
                                sigma
                           )
            in

            let lhs_new_clause = implode (f_aux::new_args_aux) in

            let new_clause = lhs_new_clause, rhs in

            (implode (f::lhs_pattern),new_rhs) , Some new_clause

    in

    let rec process_clause (cl:(unit,'t) struct_term*(unit,'t) struct_term)
      : (plain_term*(unit,'t) struct_term) list
      =
        match process_clause_aux cl with
            | cl,None ->
                (* debug "finished with %s => %s\n" (string_of_plain_term (fst cl)) (string_of_struct_term (snd cl)); *)
                [cl]
            | cl,Some cl' ->
                (* debug "new processed clause: %s => %s" (string_of_plain_term (fst cl)) (string_of_struct_term (snd cl)); *)
                (* debug "new clause to process: %s => %s\n" (string_of_struct_term (fst cl')) (string_of_struct_term (snd cl')); *)
                cl::(process_clause cl')
    in

    List.concat (List.map process_clause clauses)







let remove_term_struct (clauses:(plain_term*(unit,'t) struct_term) list)
  : (plain_term*plain_term) list
  =

    let rec extract_variables_from_struct (v:(unit,'t) struct_term) : var_name list
      = 
        match get_head v with
            | Var(x,()) -> [x]
            | Angel _ | Daimon _ | Const _ | Proj _ -> []
            | Sp(Struct fields,_) ->
                    List.fold_left (fun r dv -> merge_uniq r (extract_variables_from_struct (snd dv))) [] fields
            | App _ -> assert false
    in

    let rec process_term (v:(unit,'t) struct_term)
      : plain_term * (plain_term * (unit,'t) struct_term) list
      =
        let args,new_clauses =
            let tmp = List.map process_term (get_args v) in
            List.map fst tmp , List.concat (List.map snd tmp)
        in

        match get_head v with
            | Sp(Struct fields,_) ->
                assert (args=[]);
                let f_aux = new_aux () in
                let params = extract_variables_from_struct v in
                let new_f = app f_aux (List.map (fun x -> Var(x,())) params) in
                let new_clauses = List.map (function d,v -> App(  Proj(d,(),()) , new_f) , v) fields in
                new_f , new_clauses

            | Angel _ -> app (Angel()) args , new_clauses
            | Daimon _ -> app (Daimon()) args , new_clauses
            | Var(x,_) -> app (Var(x,())) args , new_clauses
            | Proj(d,p,_) -> app (Proj(d,p,())) args , new_clauses
            | Const(c,p,_) -> app (Const(c,p,())) args , new_clauses
            | App _ -> assert false
    in

    let rec process_clause (lhs,rhs:(plain_term*(unit,'t) struct_term))
      : (plain_term*plain_term) list
      = match process_term rhs with
            | rhs,[] ->
                (* debug "finished with %s => %s\n" (string_of_plain_term lhs) (string_of_plain_term rhs); *)
                [lhs,rhs]
            | rhs,new_clauses ->
                (* debug "new processed clause: %s => %s" (string_of_plain_term lhs) (string_of_plain_term rhs); *)
                (* debug "new clause to process: %s => %s\n" (string_of_struct_term (fst cl')) (string_of_struct_term (snd cl')); *)
                (lhs,rhs)::(List.concat (List.map process_clause new_clauses))
    in

    List.concat (List.map process_clause clauses)





let remove_struct_defs (defs:(var_name * type_expression option * ((unit,'t) struct_term*(unit,'t) struct_term) list) list)
  : (var_name * type_expression option * (plain_term*plain_term) list) list
  =
    let types = List.map (function f,t,_ -> f,t) defs in
    let clauses = List.concat (List.map (function f,_,clauses -> clauses) defs) in
    let new_clauses = remove_match_struct clauses in
    let new_clauses = remove_term_struct new_clauses in

    let new_defs = List.map (function lhs,rhs -> get_function_name lhs, (lhs,rhs)) new_clauses in
    let new_defs =
        let aux_funs,old_funs = List.partition (function f,_ -> f.[0] = '_') new_defs in
        let aux_funs = List.stable_sort (fun cl1 cl2 -> compare (fst cl1) (fst cl2)) aux_funs in
        old_funs @ aux_funs
    in

    let new_defs = partition (function f,_ -> f) new_defs in
    let new_defs = List.map
                    (function
                        | [] -> assert false
                        | ((f,_)::_) as clauses ->
                            let t = (try List.assoc f types with Not_found -> None) in
                            f,t,List.map (function _,cl -> cl) clauses)
                    new_defs
    in

    (* List.iter (function f,t,cls -> *)
    (*     List.iter (function lhs,rhs -> *)
    (*         debug "%s => %s" (string_of_plain_term lhs) (string_of_plain_term rhs) *)
    (*     ) *)
    (*     cls *)
    (* ) new_defs; *)

    new_defs


