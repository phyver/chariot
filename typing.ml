(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
totality checker for recursive definitions involving nested least and
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


(*
 * operations on type and type inference
 *)
open Misc
open Env
open Utils
open State
open Pretty


(* let compose_type_substitution (sigma1:type_substitution) (sigma2:type_substitution) : type_substitution *)
(*   = debug "compose [%s] and [%s]" (string_of_type_substitution sigma1)(string_of_type_substitution sigma2); *)
(*     let sigma = compose_type_substitution sigma1 sigma2 in *)
(*     debug "result12 %s" (string_of_type_substitution sigma); *)
(*     debug "result21 %s\n" (string_of_type_substitution (compose_type_substitution sigma2 sigma1)); *)
(*     sigma *)


(* generate fresh variables *)
let fresh_variable_nb = ref 0
let list_type_variables = ref []
let reset_fresh_variable_generator ts =
    fresh_variable_nb := 0;
    list_type_variables := List.fold_left (fun r t -> union_uniq r (extract_type_variables t)) [] ts
let fresh_variable () =
    let alpha = ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"] in
    let stop = ref false in
    let x = ref "" in
    while (not !stop)
    do
        let n = !fresh_variable_nb / 26 in
        let var = !fresh_variable_nb mod 26 in
        x := (List.nth alpha var) ^ (if n = 0 then "" else (string_of_int n));
        incr fresh_variable_nb;
        stop := not (List.mem !x !list_type_variables)
    done;
    list_type_variables := !x::!list_type_variables;
    TVar(!x)

(* instantiate all the variables from a type with fresh variables *)
let instantiate_type (t:type_expression) : type_expression =
    let vars = extract_type_variables ~stable:true t in
    let sigma = List.map (fun x -> (x,fresh_variable())) vars in
    subst_type sigma t

(* check if a variable occurs inside a type *)
let rec occur_type (x:type_name) (t:type_expression) : bool = match t with
    | TVar(y) -> x=y
    | Arrow(t1,t2) -> occur_type x t1 || occur_type x t2
    | Data(_,args) -> List.exists (occur_type x) args

(* computes the most general unifier of t1 and t2
 * NOTE: priority is given to t1: if t2 is an instance t1, then the
 * substitution we compute doesn't affect t2 *)
let unify_type_mgu (t1:type_expression) (t2:type_expression) : type_substitution =
    if verbose 4 then (debug "looking for mgu of %s and %s" (string_of_type t1) (string_of_type t2));

    let rec mgu_aux (eqs:(type_expression*type_expression) list ) acc = match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> mgu_aux eqs acc
            | (Data(t1, args1),Data(t2, args2))::eqs when t1=t2 ->
                begin
                    try mgu_aux ((List.combine args1 args2)@eqs) acc
                    with Invalid_argument _ -> error ("datatype " ^ t1 ^ " appears with different arities")
                end
            | (Arrow(t1,t2),Arrow(s1,s2))::eqs -> mgu_aux ((t1,s1)::(t2,s2)::eqs) acc
            (* do not change order of next two cases *)
            | (t, TVar(x))::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    mgu_aux eqs ((x,t)::acc)
            | (TVar(x), t)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let acc = List.map (function (_x,_t) -> (_x, subst_type [x,t] _t)) acc in
                    mgu_aux eqs ((x,t)::acc)
            | (TVar _,_)::_
            | (_,TVar _)::_ -> unificationError "cannot unify: loop"
            | (Arrow _,Data _)::_
            | (Data _,Arrow _)::_ -> unificationError "cannot unify arrow and data type"
            | ((Data _ as t1), (Data _ as t2))::_ ->
                unificationError (fmt "cannot unify datatypes %s and %s"
                    (string_of_type t1)
                    (string_of_type t2))
    in
    mgu_aux [ (t1,t2) ] []

(* unify the types t1 and t2 by applying the mgu to either one of them *)
let unify_type (t1:type_expression) (t2:type_expression) : type_expression
  = let sigma = unify_type_mgu t1 t2 in
    let _t1 = subst_type sigma t1 in
    let _t2 = subst_type sigma t2 in
    assert (_t1 = _t2);
    _t1

(* check if t1 is an instance of t2
 * NOTE: it relies on the mgu giving priority to its first argument *)
let is_instance t1 t2
  = try
        let sigma = unify_type_mgu t1 t2 in
        t1 = subst_type sigma t1
    with UnificationError _ -> false

(* check if two types are equal, up to renaming of free variables *)
let equal_type t1 t2 = (is_instance t1 t2) && (is_instance t2 t1)

(* add one variable into a sorted context *)
let rec add_to_context (x,t) context
  = match context with
        | [] -> [(x,t)]
        | (y,s)::_ when x<y -> (x,t)::context
        | (y,s)::context when x>y -> (y,s)::(add_to_context (x,t) context)
        | (y,s)::context (* when x=y *) -> (x,unify_type s t)::context

(* merge 2 lists of context and return the corresponding substitution *)
let merge_context (cs1:(var_name*type_expression) list) (cs2:(var_name*type_expression) list)
    :(var_name*type_expression) list * (type_name*type_expression) list
  =
    let rec merge_context_aux cs1 cs2 sigma = match cs1,cs2 with
        | [],cs | cs,[] -> cs,sigma
        | (x1,t1)::cs1, (x2,_)::_ when x1<x2 ->
            let cs,sigma = merge_context_aux cs1 cs2 sigma in
            (x1,t1)::cs , sigma
        | (x1,_)::_, (x2,t2)::cs2 when x1>x2 ->
            let cs,sigma = merge_context_aux cs1 cs2 sigma in
            (x2,t2)::cs , sigma
        | (x1,t1)::cs1, (x2,t2)::cs2 (*when x1=x2*) ->
            let tau = unify_type_mgu t1 t2 in
            let cs1 = List.map (second (subst_type tau)) cs1 in
            let cs2 = List.map (second (subst_type tau)) cs2 in
            let cs,sigma = merge_context_aux cs1 cs2 sigma in
            (x1,subst_type tau t1)::cs , compose_type_substitution tau sigma
    in
    let cs,sigma = merge_context_aux cs1 cs2 [] in
    List.map (second (subst_type sigma)) cs, sigma

(* infers most general type of "u" in environment "env"
 *   - "context" contains the type of some free variables (the function
 *     being defined for exemple)
 *   - "sigma" contains some type substitution that we need to apply
 *
 * the result is the type of the term together with
 *   - the updated types of the free variables: we can discover new free
 *     variables, or discover some new context on existing variables
 *   - the updated list of type substitutions: we can discover that type 'x is
 *     supposed to be nat.
 *  - a list of datatypes that were used during inference (useful for putting
 *    priorities of constants for the termination checker)
 *)

let infer_type (env:environment)
               (v:('empty,'p,'t) raw_term)
               (context:(var_name*type_expression) list)    (* context for the types of free variables *)
  : type_expression * (empty,'p,type_expression) raw_term * (var_name*type_expression) list * (type_name*type_expression) list
  = if verbose 2 then debug "infering type for %s" (string_of_plain_term v);

    let rec infer_type_aux (v:(empty,'p,'t) raw_term) context
      : type_expression * (empty,'p,type_expression) raw_term * (var_name*type_expression) list * (type_name*type_expression) list
      (* : type_expression * (var_name*type_expression) list * (type_name*type_expression) list *)
      =
          if verbose 4
          then (
            debug "infering type of (recursive call) %s" (string_of_plain_term v);
            debug "\twith context %s" (string_of_list" , " (function x,t -> x^":"^(string_of_type t)) context);
            print_newline()
        );
        match v with
            | Angel _ ->
                let t = instantiate_type (TVar("angel")) in
                t, Angel(t), context, []
            | Daimon _ ->
                let t = instantiate_type (TVar("daimon")) in
                t, Daimon(t), context, []
            | Var(x,_) ->
                begin
                    try let t = List.assoc x context in
                    t, Var(x,t), context, []
                    with Not_found ->
                        begin
                            try
                                let t = get_function_type env x in
                                let t = instantiate_type t in
                                (t, Var(x,t), context, [])
                            with Not_found ->
                                let t = instantiate_type (TVar("type_"^x)) in
                                (t, Var(x,t), add_to_context (x,t) context, [])
                        end
                end
            | Const(c,p,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env c) in
                        if is_projection env c then error (fmt "typing problem: %s is not a constructor" c);    (* FIXME: this should be done by a check_term function *)
                        (t, Const(c,p,t) , context, [])
                    with Not_found -> error (fmt "cannot infer type of constant %s" c)
                end
            | Proj(d,p,_) ->
                begin
                    try
                        let t = instantiate_type (get_constant_type env d) in
                        if not (is_projection env d) then error (fmt "typing problem: %s is not a destructor" d);     (* FIXME: this should be done by a check_term function *)
                        (t, Proj(d,p,t) , context, [])
                    with Not_found -> error (fmt "typing problem: cannot infer type of constant %s" d)
                end
            | Struct(fields,p,_) ->
                begin
                    match fields with
                        | [] ->
                            begin
                                try
                                    let tname = get_unit_type env in
                                    let t = Data(tname,[]) in
                                    t,Struct([],p,t),context,[]
                                with Not_found -> error "no type defined for the empty structure"
                            end
                        | (d,_)::_ ->
                            let t = instantiate_type (get_first_arg_type (try get_constant_type env d with Not_found -> error (fmt "cannot infer type of constant %s" d))) in

                            let t,fields,context,sigma
                              = List.fold_left
                                    (fun r dv ->
                                        let d,v = dv in
                                        let t,fields,context,sigma = r in
                                        let t',v',context,sigma2 = infer_type_aux v context in
                            (* debug ~indent:6 "%s is of type %s in context %s" (string_of_plain_term v) (string_of_type t') (string_of_context context); *)
                            (* debug ~indent:6 "sigma2: %s" (string_of_type_substitution sigma2); *)
                                        let sigma = compose_type_substitution sigma sigma2 in
                            (* debug ~indent:6 "sigma: %s" (string_of_type_substitution sigma); *)
                                        let t = subst_type sigma t in

                                        let sigma3 = match instantiate_type (try get_constant_type env d with Not_found -> error (fmt "cannot infer type of constant %s" d)) with
                                                        | Arrow(t1,t2) ->
                                                            let tau1 = unify_type_mgu t1 t in
                            (* debug "tau1: %s" (string_of_type_substitution tau1); *)
                                                            let tau2 = unify_type_mgu t2 t' in
                            (* debug "tau2: %s" (string_of_type_substitution tau2); *)
                                                            compose_type_substitution tau1 tau2
                                                        | _ -> assert false
                                        in
                                        let context = List.map (second (subst_type sigma3)) context in
                                        let t = subst_type sigma3 t in

                            (* debug "sigma3: %s" (string_of_type_substitution sigma3); *)
                                        let sigma = compose_type_substitution sigma sigma3 in
                            (* debug "sigma final: %s" (string_of_type_substitution sigma); *)

                                        t,(d,v')::fields , context , sigma
                                        )
                                    (t,[],context,[])
                                    fields
                            in

                            (* debug "context %s" (string_of_context context); *)
                            let t = subst_type sigma t in

                            (t,Struct(List.rev fields,p,t) , context, sigma)
                end
            | App(v1,v2) ->
                begin
                    (* do not interchange the order of the next two lines! *)
                    (* TODO: understand why *)
                    let t2,v2,context,sigma2 = infer_type_aux v2 context in
                    let t1,v1,context,sigma1 = infer_type_aux v1 context in
                    (* debug "1"; *)
                    let sigma = compose_type_substitution sigma2 sigma1 in  (* do not interchange sigma3 sigma *)

                    let tfunc = instantiate_type (Arrow(TVar("arg"),TVar("result"))) in
                    let sigma3 = unify_type_mgu t1 tfunc in
                    (* debug "sigma: %s" (string_of_type_substitution sigma); *)
                    (* debug "sigma3: %s" (string_of_type_substitution sigma3); *)
                    let tfunc = subst_type sigma3 tfunc in
                    (* debug "2 OK?"; *)
                    let sigma = compose_type_substitution sigma sigma3 in   (* do not interchange sigma3 and sigma *)
                    (* debug " composition: %s\n" (string_of_type_substitution sigma); *)

                    let targ,tres = match tfunc with
                        | Arrow(a,b) -> a,b
                        | _ -> assert false
                    in

                    let sigma4 = unify_type_mgu t2 targ in
                    (* debug "3 OK?"; *)
                    let sigma = compose_type_substitution sigma sigma4 in (* do not interchange sigma4 and sigma *)

                    let context = List.map (second (subst_type sigma)) context in
                    let tres = subst_type sigma tres in
                    tres,App(v1,v2),context,sigma
                end
            | Sp(v,_) -> v.bot
    in

    try
        let t,v,context,sigma = infer_type_aux v context in
        let v = subst_type_term sigma v in
        if verbose 3
        then (
            debug "infered type of %s : %s" (string_of_plain_term v) (string_of_type t);
            debug "\twith free variables: %s" (string_of_context context);
            debug "\tand types: %s" (string_of_type_substitution sigma);
            print_newline()
        );


        (* debug "sigma %s" (string_of_type_substitution sigma); *)
        (* debug "before:"; print_typed_subterms v; *)
        let v = subst_type_term sigma v in
        (* debug "after:"; print_typed_subterms v; *)

        t,v,context,sigma
    with UnificationError e -> error (fmt "unification error when typing %s: %s" (string_of_plain_term v) e)

let infer_type_term (env:environment) (v:(empty,'p,'t) raw_term)
  : type_expression * (empty,'p,type_expression) raw_term * (var_name*type_expression) list
  = reset_fresh_variable_generator [];
    let t,v,context,_ = infer_type env v [] in
    t,
    v,
    context

let infer_type_clause (env:environment)
                      (context:(var_name*type_expression) list)     (* should contain context for __ALL__ the functions *)
                      (lhs_pattern:(empty,'p,'t) raw_term)
                      (rhs_def:(empty,'p,'t) raw_term)
  : (var_name*type_expression) list * (empty,'p,type_expression) raw_term * (empty,'p,type_expression) raw_term
  =

    let funs = List.map fst context in

    (* infer type of LHS, getting the type context on the variables (and the function itself) *)
    (* reset_fresh_variable_generator []; *)
    (* I need to reset the generator only once for each bunch of recursive definitions. Otherwise, there can be some interference between clauses, like
        val test1 x = []
          | test1 [] = []
    *)
    let infered_type_lhs, lhs_pattern, context_lhs,sigma = infer_type { env with functions=[] } lhs_pattern context in

    let variables = extract_pattern_variables lhs_pattern in

    (* print_typed_subterms lhs_pattern; *)

    (* infer type of RHS *)
    let infered_type_rhs, rhs_def, context,sigma' = infer_type env rhs_def context_lhs in
    (* print_typed_subterms rhs_def; *)

    let sigma = compose_type_substitution sigma sigma' in

    (* unify types of LHS and RHS *)
    let tau = unify_type_mgu infered_type_rhs infered_type_lhs in
    let sigma = compose_type_substitution sigma tau in

    (* update context ant types of lhs/rhs *)
    let context = List.map (second (subst_type sigma)) context in
    let lhs_pattern = subst_type_term sigma lhs_pattern in
    let rhs_def = subst_type_term sigma rhs_def in
    (* print_typed_subterms lhs_pattern; *)

    (* remove variables from context *)
    let context = List.filter (function x,t -> not (List.mem x variables)) context in

    (* check that no remaining variables is left *)
    List.iter (function f,_ -> if not (List.mem f funs) then error (fmt "variable %s is free" f)) context;

    if verbose 4
    then (
        debug "infered type of pattern: %s" (string_of_type infered_type_lhs);
        debug" and infered type of definition: %s" (string_of_type infered_type_rhs);
        debug "\tgiving %s" (string_of_type (subst_type sigma infered_type_rhs));
        debug "\ttypes: %s" (string_of_list "," (function x,t -> "'"^x^"="^(string_of_type t)) sigma);
        debug "\twith context: %s" (string_of_list "," (function x,t -> x^":"^(string_of_type t)) context);
        );

    (* the type of the RHS should be an instance of the type of the LHS *)
    (* oups: val s.Tail = ??? doesn't work with this... *)
    (* if not (infered_type_rhs = subst_type sigma infered_type_rhs) *)
    (* then error ("rhs and lhs do not have the same type"); *)

   context, lhs_pattern,rhs_def



let infer_type_defs
    (env:environment)
    (defs:(var_name * type_expression option * ((empty,'p,'t) raw_term * (empty,'p,'t) raw_term) list) list)
    : (var_name * type_expression * ((empty,'p,type_expression) raw_term * (empty,'p,type_expression) raw_term) list) list
  =
    reset_fresh_variable_generator [];

    (* all the clauses *)
    let clauses = List.concat (List.map (function f,_,clauses -> (List.map (function lhs,rhs -> f,lhs,rhs) clauses)) defs) in

    (* the types of functions, as given by the user *)
    let given_types = List.sort compare (List.concat (List.map (function f,t,_ -> match t with None -> [] | Some t -> [f,t]) defs)) in

    (* initial context on the functions *)
    let initial_context = List.sort compare (List.map (function f,t,_ -> match t with None -> (f,TVar("type_"^f)) | Some t -> (f,t)) defs) in

    let all_context,clauses = List.split (
        List.map
            (function f,lhs,rhs ->
                let context = List.map (second instantiate_type) initial_context in
                let context, lhs,rhs = infer_type_clause env context lhs rhs in
                (context, (f,lhs,rhs))
            )
            clauses)
    in

    (* debug "contexts:\n  %s" (string_of_list "\n  " string_of_context all_context); *)

    let context,sigma =
        List.fold_left
            (fun r context ->
                let context',sigma' = r in
    (* debug "merge contexts  %s and %s" (string_of_context context) (string_of_context context'); *)
                let context,sigma = merge_context context context' in
    (* debug "result:  %s" (string_of_context context); *)
    (* debug "with sigma: %s" (string_of_type_substitution sigma); *)
    (* debug "sigma': %s" (string_of_type_substitution sigma'); *)
                let sigma = compose_type_substitution sigma' sigma in
    (* debug "new sigma: %s" (string_of_type_substitution sigma); *)
                context,sigma
                )
            ([],[])
            all_context
    in
    (* debug "final context:  %s" (string_of_context context); *)

    (* debug "SIGMA: %s" (string_of_type_substitution sigma); *)
    (* debug "BEFORE"; *)
        (* List.iter (function f,lhs,rhs -> *)
        (*     print_typed_subterms lhs; *)
        (*     print_string "\n     ==>\n\n"; *)
        (*     print_typed_subterms rhs; *)
        (*     print_newline() *)
    (* ) clauses; *)

    let clauses = List.map (function f,lhs,rhs -> (f,subst_type_term sigma lhs,subst_type_term sigma rhs)) clauses in
    (* debug "AFTER"; *)
    (*     List.iter (function f,lhs,rhs -> *)
    (*         print_typed_subterms lhs; *)
    (*         print_string "\n     ==>\n\n"; *)
    (*         print_typed_subterms rhs; *)
    (*         print_newline() *)
    (* ) clauses; *)

    (* simplify type variables *)
    let tvars = uniq ~stable:true (List.concat (List.map (function _,t -> extract_type_variables ~stable:true t) context)) in
    reset_fresh_variable_generator [];
    let sigma = List.map (fun x -> x,instantiate_type (TVar x)) tvars in
    let clauses = List.map (function f,lhs,rhs -> (f,subst_type_term sigma lhs,subst_type_term sigma rhs)) clauses in

    (* putting everything back together *)
    let typed_defs = unflatten (function f,lhs,rhs -> f,(lhs,rhs)) clauses in

    let defs = List.map (function f,t,cls ->
                            let new_clauses =
                                try List.assoc f typed_defs
                                with Not_found -> assert (cls=[]);[]
                            in f,new_clauses)
                      defs in

    (* chooses appropriate type to show the user *)
    let choose_type f =
        try
            let tf = List.assoc f given_types in
            reset_fresh_variable_generator [tf];
            try
                let t = instantiate_type (List.assoc f context) in
                if is_instance tf t
                then tf
                else error (fmt "function %s cannot be coerced to type %s" f (string_of_type tf))
            with Not_found -> tf    (* if f is not in the context, it means there were no associated
                                     * clause. The type was necessarily given by the user *)
        with Not_found ->   (* if no type was given by the user *)
            try
                let t = List.assoc f context in
                reset_fresh_variable_generator [];
                instantiate_type t
                (* t *)
            with Not_found -> assert false  (* in this case, the function f must appear in the
                                             * context as there is at least one corresponding clause *)
    in

    let defs = List.map (function f,cls -> f,choose_type f,cls) defs in

    defs
