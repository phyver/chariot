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

exception Impossible_case


(* operation on coefficients *)
let op_coeff c = List.map (function (p,w) -> p, op_weight w) c

let collapse_weight_in_coeff b c = List.map (function p,w -> p,collapse_weight b w) c

(* misc operations on approximations *)
let rec add_coeff c1 c2
  = match c1,c2 with
        | [],c | c,[] -> c
        | (p1,w1)::c1,(p2,w2)::c2 when p1=p2 ->
            begin
                match add_weight w1 w2 with
                    | Num 0 -> add_coeff c1 c2
                    | w -> (p1,w)::add_coeff c1 c2
            end
        | (p1,w1)::c1,(p2,w2)::_ when p1<p2 -> (p1,w1)::add_coeff c1 c2
        | (p1,w1)::_,(p2,w2)::c2 when p1>p2 -> (p2,w2)::add_coeff c1 c2
        | _,_ -> assert false
(* let add_coeff c1 c2 = *)
(*     debug "add"; *)
(*     debug "c1: %s" (string_of_coeff c1); *)
(*     debug "c2: %s" (string_of_coeff c2); *)
(*     let r = add_coeff c1 c2 in *)
(*     debug "result: %s" (string_of_coeff r); *)
(*     r *)


let rec sup_coeff c1 c2
  = match c1,c2 with
        | [],c | c,[] -> c
        | (p1,w1)::c1,(p2,w2)::c2 when p1=p2 -> (p1,sup_weight w1 w2)::sup_coeff c1 c2
        | (p1,w1)::c1,(p2,w2)::_ when p1<p2 -> (p1,w1)::sup_coeff c1 c2
        | (p1,w1)::_,(p2,w2)::c2 when p1>p2 -> (p2,w2)::sup_coeff c1 c2
        | _,_ -> assert false
(* let sup_coeff c1 c2 = *)
(*     debug "sup"; *)
(*     debug "c1: %s" (string_of_coeff c1); *)
(*     debug "c2: %s" (string_of_coeff c2); *)
(*     let r = sup_coeff c1 c2 in *)
(*     debug "result: %s" (string_of_coeff r); *)
(*     r *)

let rec approx_coeff c1 c2  (* check if c1 is an approximation for c2 *)
  = match c1,c2 with
        | [],c2 -> List.for_all (function (_,w2) -> less_weight w2 (Num 0)) c2
        | c1,[] -> List.for_all (function (_,w1) -> less_weight (Num 0) w1) c1
        | (p1,w1)::c1,(p2,w2)::c2 when p1=p2 -> less_weight w2 w1 && approx_coeff c1 c2
        | (p1,w1)::c1,(p2,w2)::_ when p1<p2 -> less_weight (Num 0) w1 && approx_coeff c1 c2
        | (p1,w1)::_,(p2,w2)::c2 when p1>p2 -> less_weight w2 (Num 0) && approx_coeff c1 c2
        | _,_ -> assert false
(* let approx_coeff c1 c2 = *)
(*     debug "approx"; *)
(*     debug "c1: %s" (string_of_coeff c1); *)
(*     debug "c2: %s" (string_of_coeff c2); *)
(*     approx_coeff c1 c2 *)



let rec collapse_weight_in_term (b:int) (v:approx_term)
  = match v with
        | Var _ | Const _ | Proj _ | Angel _ | Daimon _ -> v
        | App(u1,u2) -> App(collapse_weight_in_term b u1, collapse_weight_in_term b u2)
        | Sp(AppRes(c),t) -> Sp(AppRes(collapse_weight_in_coeff b c),t)
        | Sp(AppArg [],_) -> assert false
        | Sp(AppArg xcs,t) -> Sp(AppArg(List.map (function x,c -> x, collapse_weight_in_coeff b c) xcs),t)

let collapse_weight_in_pattern b (f,ps) =
    (f,List.map (collapse_weight_in_term b) ps)



(* collapse all projections in a list of pattern arguments *)
let collapse_proj (args:approx_term list) : coeff
  =
    let rec collapse_proj_aux args acc
      = match args with
            | Sp(AppRes(c),_)::args ->
                collapse_proj_aux args (add_coeff acc c)
            | Proj(_,p,_)::args -> collapse_proj_aux args (add_coeff acc [p,Num 1])
            | _::args -> collapse_proj_aux args acc
            | [] -> acc
    in collapse_proj_aux args []

(* add some pattern arguments to an existing pattern, simplifying when an AppRes is found *)
let add_pattern_args (f,args1:sct_pattern) (args2:approx_term list) : sct_pattern =
    let rec aux args = match args with
        | [] -> []
        | (Sp(AppRes _,t))::_ ->
                let c = collapse_proj args in
                [Sp(AppRes c,t)]
        | u::args -> u::(aux args)
    in f,aux(args1@args2)
(* let add_pattern_args (f,ps) qs = *)
(*     debug "before: %s" (string_of_sct_pattern (f,ps@qs)); *)
(*     let r = add_pattern_args (f,ps) qs in *)
(*     debug "after: %s" (string_of_sct_pattern r); *)
(*     r *)


(* simplify a sum of approximations
 * NOTE: the argument is given as an approx_term because it can be an Angel of a Daimon *)
let simplify_coeffs (v:approx_term) : approx_term =
    let rec simplify_aux = function
        | [] -> []
        | [x] -> [x]
        | (x1,c1)::((x2,_)::_ as xcs) when x1<x2 -> (x1,c1)::(simplify_aux xcs)
        | (x1,c1)::(x2,c2)::xcs ->
                assert (x1=x2);
                let c = sup_coeff c1 c2 in
                simplify_aux ((x1,c)::xcs)
    in
    match v with
        | Angel() | Daimon() -> v
        | Sp(AppArg(xcs),()) ->
            let xcs = List.sort (fun xc1 xc2 -> compare (fst xc1) (fst xc2)) xcs in
            Sp(AppArg(simplify_aux xcs),())
        | _ -> assert false
(* let simplify_coeffs v = *)
(*     let r = simplify_coeffs v in *)
(*     debug "simplify_coeffs"; *)
(*     debug "v: %s" (string_of_approx_term v); *)
(*     debug "result: %s" (string_of_approx_term r); *)
(*     r *)


(* merge two sums of approximations *)
let merge_approx v1 v2 =
    let rec merge_aux xcs1 xcs2 = match xcs1,xcs2 with
        | xcs1 , [] | [] , xcs1 -> xcs1
        | (x1,c1)::xcs1 , (x2,_)::_ when x1<x2 -> (x1,c1)::(merge_aux xcs1 xcs2)
        | (x1,_)::_ , (x2,c2)::xcs2 when x1>x2 -> (x2,c2)::(merge_aux xcs1 xcs2)
        | (x1,c1)::xcs1 , (x2,c2)::xcs2 (*when x1=x2*) ->
                let c = sup_coeff c1 c2 in
                (x1,c)::(merge_aux xcs1 xcs2)
    in
    match v1,v2 with
        | Angel(),v | v,Angel() -> v
        | Daimon(),_ | _,Daimon() -> Daimon()
        | Sp(AppArg(xcs1),()) , Sp(AppArg(xcs2),()) ->
            let xcs1 = List.sort (fun xc1 xc2 -> compare (fst xc1) (fst xc2)) xcs1 in
            let xcs2 = List.sort (fun xc1 xc2 -> compare (fst xc1) (fst xc2)) xcs2 in
            Sp(AppArg(merge_aux xcs1 xcs2),())
        | _,_ -> raise (Invalid_argument "merge_approx")
(* let merge_approx v1 v2 = *)
(*     let r = merge_approx v1 v2 in *)
(*     debug "merge_approx"; *)
(*     debug "v1: %s" (string_of_approx_term v1); *)
(*     debug "v2: %s" (string_of_approx_term v2); *)
(*     debug "result: %s" (string_of_approx_term r); *)
(*     r *)



(* collapse all the constructors from a contructorn pattern with approximations *)
let collapse0 ?(coeff=[]) (p:approx_term) : approx_term =
    let rec collapse0_aux coeff p =
        match get_head p,get_args p with
            | Var(x,_),[] -> Sp(AppArg([ x,coeff ]),())
            | Angel _,[] -> raise (Invalid_argument "collapse0_aux: Angel")
            | Daimon _,[] -> raise (Invalid_argument "collapse0_aux: Daimon")
            | Sp (AppArg xcs,_),[] -> Sp(AppArg(List.map (function x,c -> x,add_coeff coeff c) xcs),())
            | Const(_,prio,_),[] -> let c = add_coeff coeff [prio,Num 1] in Sp(AppArg([ "()",c ]),())
            | Const(_,prio,_),ps ->
                begin
                    let coeff = add_coeff coeff [prio,Num 1] in
                    let approx_s = List.map (collapse0_aux coeff) ps in
                    List.fold_left
                        (fun v1 v2 -> merge_approx v1 (simplify_coeffs v2))
                        (Angel())
                        approx_s  (* NOTE: not necessary to simplify v1: it is the recursive call and is simplified *)

                end
            | Proj(_,prio,_),p::ps ->       (* TODO: there shouldn't be any
            projection inside pattern arguments when doing the SCT, but there
            can be when constructing the initial call graph or during testing from parser.mly...
            ==> add argument to allow / disallow projections... *)
                let coeff = add_coeff coeff [prio,Num 1] in
                collapse0_aux coeff p

            | Proj(_,prio,_),[] -> assert false
            | Sp (AppArg [],_),_ -> assert false
            | Sp (AppRes _,_),[] -> assert false
            | Sp (AppArg _,_),_::_ -> assert false
            | Sp (AppRes _,_),_::_ -> assert false
            | Var _,_::_ -> assert false
            | Daimon _,_ -> assert false
            | Angel _,_ -> assert false
            | App _,_ -> assert false
    in
    try
        collapse0_aux coeff p
    with Invalid_argument "collapse0_aux: Angel" -> Angel()
       | Invalid_argument "collapse0_aux: Daimon" -> Daimon()

let collapse_sct_pattern (depth:int) (f,ps:sct_pattern) : sct_pattern
  =
    (* collapse the constructors at given depth from a constructor pattern with approximations *)
    let rec collapse_const d p =
        match get_head p,get_args p with
            | Sp (AppArg [],_),_ -> assert false
            | (Var _ | Angel _ | Daimon _ | Sp (AppArg _,_)),[] -> p
            | (Var _ | Angel _ | Daimon _ | Sp (AppArg _,_)),_::_ -> assert false
            | Const(c,prio,_),ps when d>0 -> app (Const(c,prio,())) (List.map (collapse_const (d-1)) ps)
            | Const _,_ (* when d=0*) -> collapse0 p
            | Proj(x,prio,_),p::ps when d>0 -> app (Proj(x,prio,())) (List.map (collapse_const (d-1)) (p::ps))
            | Proj _,_::_ (*when d=0*) -> collapse0 p
            | Proj _,[] -> assert false
            | Sp(AppRes _,_),_ -> assert false
            | App _,_ -> assert false
    in

    (* collapse the pattern of a definition at a given depth *)
    let rec collapse_depth dp ps
      = match ps with
        | [] -> []
        | (Proj _ as d)::ps when dp>0 ->
            d::(collapse_depth (dp-1) ps)
        | (Proj(_,prio,t))::ps (*when dp=0*) ->
            let c = collapse_proj ((Sp(AppRes([prio,Num 1]),t))::ps) in
            [Sp(AppRes(c),t)]
        | [Sp(AppRes _,_)] as ps -> ps
        | (Sp(AppRes _,_))::_ -> assert false
        | p::ps -> (collapse_const depth p)::(collapse_depth dp ps)
    in

    (* debug "collapse_sct_pattern = %s" (string_of_sct_pattern pattern); *)

    f,collapse_depth depth ps



(* composition:
 *
 *  p1 => d1  o  p2 => d2
 *  let sigma = unify p2 d1 in sigma p1 => sigma d2
 *
 * problem: how to deal with approximations
 *
 * p1 => <-1> x + <1> y  o  Node t1 t2 => d2
 *
 * p1 => <-1> x + <1> y  o  t => d2[t1:=<-1>t, t2:=<-1>t]   =   ...
 *)

let rec subst_sct_term sigma v
  = match v with
        | Var(x,t) -> (try List.assoc x sigma with Not_found -> Var(x,t))
        | (Angel _|Daimon _|Const _|Proj _|Sp(AppRes _,_)) as v -> v
        | App(v1,v2) -> App(subst_sct_term sigma v1, subst_sct_term sigma v2)
        | Sp(AppArg [],_) -> assert false
        | Sp(AppArg xcs,_) ->
                List.fold_left
                    (fun v xc ->
                        let x,c = xc in
                        let u = try collapse0 ~coeff:c (List.assoc x sigma)
                                with Not_found -> Sp(AppArg([x,c]),()) in
                        merge_approx v u
                    )
                    (Angel())
                    xcs
(* let subst_sct_term sigma v = *)
(*     debug "sigma = %s" (string_of_list " , " (function x,v -> fmt "%s:=%s" x (string_of_approx_term v)) sigma); *)
(*     debug "before %s" (string_of_approx_term v); *)
(*     let v = subst_sct_term sigma v in *)
(*     debug "after %s" (string_of_approx_term v); *)
(*     v *)


(* normalize a clause by moving all the approximations from the LHS to the RHS:
 *    A  (<1>x+<2>y) z  =>  B  x y z
 * is transformed into
 *    A  a  b  =>  B  <-1>a  <-2> a b
 *)

let normalize_sct_clause (lhs,rhs : sct_clause)
  : sct_clause
  =
    let f_l,patterns_l = lhs in
    let f_r,patterns_r = rhs in

    (* debug "normalize with %s" (string_of_sct_clause (lhs,rhs)); *)

    (* TODO: rename dangling variables on the RHS to "!x" *)

    (* debug "normalizing %s" (string_of_sct_clause (lhs,rhs)); *)
    let n = ref 0
    in

    let new_var () = incr n; "x"^string_of_sub !n
    in

    (* process a constructor pattern to get the approximations:
     * <w1>x1 + <w2>x2
     * on the left is going to be replaced by a fresh variable y
     * and generate a substitution
     * x1:=<-w1>y  ;  x1:=<-w2>y
     *)
    let rec process_const_pattern p =
        match get_head p, get_args p with

            | Var(x,t),[] -> let y = new_var() in Var(y,t) , [x,Var(y,t)]
            | Var _,_ -> assert false

            | Const(c,p,t), args ->
                let tmp = List.map process_const_pattern args in
                let sigma = List.concat (List.map snd tmp) in
                let args = List.map fst tmp in
                (app (Const(c,p,t)) args , sigma)

            | Sp(AppArg [],_),_ -> assert false
            | Sp(AppArg xcs,_),[] ->
                let x = new_var() in
                (Var(x,()), List.map (function (y,c) -> (y,Sp(AppArg [x, op_coeff c],()))) xcs)

            | _ -> assert false
    in

    (* process the lhs of a clause to extract:
     *   - a new lhs without approximation
     *   - a substitution to replace some RHS variables by approximations
     *   - an approximation to put on the result of the RHS
     *)
    let rec process_lhs l_patterns =
        match l_patterns with
            | [] -> [] , [] , None

            | [(Sp(AppRes(c),t))] ->
                    [], [] , Some (Sp(AppRes(op_coeff c),t))
            | (Sp(AppRes(_),_))::_ -> assert false

            | (Proj _ as p)::l_patterns ->
                let l_patterns,sigma,app_res = process_lhs l_patterns in
                (p::l_patterns) , sigma , app_res

            | pat::l_patterns ->
                let pat,sigma' = process_const_pattern pat in
                let l_patterns,sigma,app_res = process_lhs l_patterns in
                (pat::l_patterns) , (sigma'@sigma) , app_res
    in
    (* let process_lhs lhs = *)
    (*     (1* debug "process_lhs with %s" (string_of_approx_term lhs); *1) *)
    (*     process_lhs lhs *)
    (* in *)

    let patterns_l,sigma,app_res = process_lhs patterns_l
    in

    let patterns_r = List.map (subst_sct_term sigma) patterns_r in

    let cl_r = match app_res with None -> (f_r,patterns_r)
                                | Some app -> add_pattern_args (f_r,patterns_r) [app]
    in

    (*   (1* debug "obtained %s" (string_of_sct_clause (lhs,rhs)) *1) *)

    (f_l,patterns_l) , cl_r


let rec rename_var x v
    = match v with
        | Var("()",_) -> v
        | Var(y,t) -> Var(y^x,t)
        | App(v1,v2) -> App(rename_var x v1, rename_var x v2)
        | Const _ | Proj _ | Angel _ | Daimon _ -> v
        | Sp(AppArg [],_) -> assert false
        | Sp(AppArg xcs,t) -> Sp(AppArg (List.map (function y,c -> if y="()" then y,c else y^x,c) xcs),t)
        | Sp(AppRes _,_) -> v
        (* | _ -> assert false *)


(* unify the rhs of a clause with the lhs of another *)
let unify ?(allow_approx=false) (f_r,patterns_r:sct_pattern) (f_l,patterns_l:sct_pattern)
  :   (var_name * approx_term) list     (* the substitution *)
    * approx_term list                  (* the arguments that were in lhs but not in rhs *)
    * approx_term list                  (* the arguments that were in rhs but not in lhs *)  (* NOTE: at most one of those lists is non-empty *)
  =

    assert (f_r = f_l);

    (* TODO: rewrite to have a list of equations as argument??? *)
    let rec unify_aux (ps_r:approx_term list) (ps_l:approx_term list)
                      (sigma:(var_name*approx_term) list)
      : (var_name*approx_term) list * approx_term list * approx_term list
      = match ps_r,ps_l with
            | [],[] -> sigma,[],[]

            | u_r::ps_r,u_l::ps_l when u_r=u_l -> unify_aux ps_r ps_l sigma

            | App(u_r,v_r)::ps_r,App(u_l,v_l)::ps_l -> unify_aux (u_r::v_r::ps_r) (u_l::v_l::ps_l) sigma

            | Sp(AppArg [],_)::_,_ -> assert false

            | Sp(AppArg xcs_r,_)::ps_r,u_l::ps_l ->
                if allow_approx
                then
                    match collapse0 u_l with
                        | Sp(AppArg(xcs_l),()) ->
                            let tau = List.map (function x,c -> (x,Sp(AppArg(List.map (function _x,_c -> _x,add_coeff _c (op_coeff c)) xcs_r),())) ) xcs_l in
                            unify_aux ps_r ps_l (tau @ (List.map (second (subst_sct_term sigma)) sigma))
                        | _ -> assert false
                else
                    assert false

            | u_r::ps_r,Sp(AppArg apps_l,_)::ps_l ->
                    assert false (*raise (UnificationError "approximation on the right not allowed during unification")*)

            | [Sp(AppRes(c),_)],ps_l ->
                if allow_approx
                then
                    let tmp = List.filter (function Proj _ | Sp(AppRes _,_) -> true | _ -> false) ps_l in
                    let tmp = List.map (function Proj(_,p,_) -> [p,Num 1] | Sp(AppRes(c),_) -> c | _ -> assert false) tmp in
                    let c = List.fold_left (fun c1 c2 -> add_coeff c1 (op_coeff c2)) c tmp in
                    (* sigma,[],[Sp(AppRes(p,w))] *)
                    sigma,[Sp(AppRes(c),())],[]
                else
                    assert false

            | ps_r,[Sp(AppRes(c),_)] ->
                    assert false (*raise (UnificationError "approximation on the right not allowed during unification")*)

            | Var(x_r,_)::ps_r,u_l::ps_l -> unify_aux (List.map (subst_sct_term [x_r,u_l]) ps_r) ps_l ((x_r,u_l)::(List.map (second (subst_sct_term [x_r,u_l])) sigma))
            | u_r::ps_r,Var(x_l,_)::ps_l -> unify_aux ps_r (List.map (subst_sct_term [x_l,u_r]) ps_l) ((x_l,u_r)::(List.map (second (subst_sct_term [x_l,u_r])) sigma))

            | ps_r,[] -> sigma,ps_r,[]
            | [],ps_l -> sigma,[],ps_l


            | Sp(AppRes(c),_)::_,_
            | _,Sp(AppRes(c),_)::_ ->
                    (* debug "OOPS"; *)
                    (* debug "ps_l = %s" (string_of_list " " string_of_approx_term ps_l); *)
                    (* debug "ps_r = %s" (string_of_list " " string_of_approx_term ps_r); *)
                    assert false

            | _,_ -> raise (UnificationError ("cannot unify " ^ (string_of_list " " string_of_approx_term ps_r) ^ " and " ^ (string_of_list " " string_of_approx_term ps_l)))
            (* TODO remove joker pattern to make sure I am not forgetting anything *)

    in

    unify_aux patterns_r patterns_l []


let compose (l1,r1:sct_clause) (l2,r2:sct_clause)
  : sct_clause
  =
    let rename s (f,pats) = (f,List.map (rename_var s) pats) in
    let l1,r1 = rename "₁" l1, rename "₁" r1 in
    let l2,r2 = rename "₂" l2, rename "₂" r2 in
    (* debug "  %s  o    %s" (string_of_sct_clause (l1,r1)) (string_of_sct_clause (l2,r2)); *)

    try
        (* debug "unify %s and %s" (string_of_sct_pattern r1) (string_of_sct_pattern l2); *)
        let sigma,context1,context2 = unify ~allow_approx:true r1 l2 in
(* debug "sigma: %s" (string_of_list " , " (function x,t -> x ^ ":=" ^ (string_of_approx_term t)) sigma); *)
(* debug "context1: %s" (string_of_list " , " string_of_approx_term context1); *)
(* debug "context2: %s" (string_of_list " , " string_of_approx_term context2); *)
        let subst (f,pats) = (f,List.map (subst_sct_term sigma) pats) in
        let l = subst l1 in
        let r = subst r2 in
(* debug "obtained %s" (string_of_sct_clause (l,r)); *)
        let r = normalize_sct_clause (add_pattern_args l context2 , add_pattern_args r context1) in
(* debug "after renormalization %s" (string_of_sct_clause r); *)
        r
    with
        UnificationError err -> raise Impossible_case


let collapse_sct_clause b d (l,r:sct_clause) : sct_clause
  =
    let l = collapse_sct_pattern d l in
    let r = collapse_sct_pattern d r in
    let l,r = normalize_sct_clause (l,r) in
    let r = collapse_weight_in_pattern b r in
    l,r


let collapsed_compose (b:int) (d:int) (c1:sct_clause) (c2:sct_clause) : sct_clause
  =
    (* debug "composing:  %s   and   %s" (string_of_sct_clause c1) (string_of_sct_clause c2); *)
    let l,r = compose c1 c2
    in
    (* debug "   l,r:  %s " (string_of_sct_clause (l,r)); *)
    let result = collapse_sct_clause b d (l,r)
    in
    (* debug "   result:  %s " (string_of_sct_clause result); *)
    result


(* check if p1 approximates p2 *)
let approximates p1 p2 =

    let rec approximates_aux pats1 pats2 =
        (* debug "pats1 = %s" (string_of_list " , " string_of_approx_term pats1); *)
        (* debug "pats2 = %s" (string_of_list " , " string_of_approx_term pats2); *)
        match pats1,pats2 with
            | [],[] -> true

            | (Angel _)::pats1,(Angel _)::pats2 -> approximates_aux pats1 pats2
            | (Angel _)::pats1,_::pats2 -> false
            | _::pats1,(Angel _)::pats2 -> approximates_aux pats1 pats2
            | (Angel _)::_,[] | [],(Angel _)::_-> false

            | (Daimon _)::pats1,_::pats2 -> approximates_aux pats1 pats2
            | _::pats1,(Daimon _)::pats2 -> false
            | (Daimon _)::_,[] | [],(Daimon _)::_ -> false

            | Proj(d1,_,_)::pats1,Proj(d2,_,_)::pats2 when d1=d2 -> approximates_aux pats1 pats2
            | Proj(d1,_,_)::_,Proj(d2,_,_)::_ (* when d1<>d2*) -> false
            | (Proj _)::_,[] | [],(Proj _)::_-> false
            | (Proj _)::_,(Const _ | Var _ | App _ )::_ -> assert false
            | Proj _::_ , Sp(AppRes _,_)::_ -> false
            | Proj _::_ , Sp(AppArg _,_)::_ -> assert false

            | Const(c1,_,_)::pats1,Const(c2,_,_)::pats2 when c1=c2 -> approximates_aux pats1 pats2
            | Const(c1,_,_)::pats1,Const(c2,_,_)::pats2 (*c1<>c2*) -> false
            | (Const _)::_,[] | [],(Const _)::_-> false
            | (Const _)::_,(Var _ | App _ )::_ -> false
            | (Const _)::_,(Proj _)::_ -> assert false
            | Const _::_ , Sp(AppArg _,_)::_ -> false
            | Const _::_ , Sp(AppRes _,_)::_ -> assert false

            | Var(x1,_)::pats1,Var(x2,_)::pats2 when x1=x2 -> approximates_aux pats1 pats2
            | Var(x1,_)::pats1,Var(x2,_)::pats2 (*x1<>x2*) -> false
            | (Var _)::_,[] | [],(Var _)::_-> false
            | (Var _)::_,(Const _ | Proj _ | App _ )::_ -> false
            | Var _::_ , Sp(AppArg _,_)::_ -> false
            | Var _::_ , Sp(AppRes _,_)::_ -> assert false

            | ((App _) as u1)::_pats1,((App _) as u2)::_pats2 ->
                    approximates_aux ((get_head u1)::(get_args u1)@_pats1) ((get_head u2)::(get_args u2)@_pats2)
            | (App _)::_,[] | [],(App _)::_-> false
            | (App _)::_,(Var _ | Const _)::_ -> false
            | (App _)::_,(Proj _)::_ -> assert false
            | App _::_ , Sp(AppRes _,_)::_ -> assert false
            | App _::_ , Sp(AppArg _,_)::_ -> false

            | Sp(AppArg [],_)::_,_
            | _,Sp(AppArg [],_)::_ -> assert false

            | Sp(AppArg apps1,t1)::pats1,Sp(AppArg apps2,t2)::pats2 ->
                    (* debug "left: %s, right: %s" *)
                    (*     (string_of_approx_term (Sp(AppArg apps1,t1))) *)
                    (*     (string_of_approx_term (Sp(AppArg apps2,t2))); *)
                let b = List.for_all (function x2,c2 ->
                        List.exists  (function x1,c1 ->
                            (* debug "x1=%s, x2=%s, p1=%s, p2=%s, w1=%s, w2=%s" x1 x2 (string_of_priority p1) (string_of_priority p2) (string_of_weight w1) (string_of_weight w2); *)
                                x1=x2 && (approx_coeff c1 c2)
                            )
                            apps1)
                            apps2
                in b && approximates_aux pats1 pats2
            | Sp(AppArg _,_)::_,u2::_pats2 ->
                    approximates_aux pats1 ((collapse0 u2)::_pats2)
            | Sp(AppArg _,_)::_,[] -> false
            | [],Sp(AppArg _,_)::_ -> false

            | [Sp(AppRes(c),_)],pats2 ->
                    begin
                        let projs = List.filter (function Sp(AppRes _,_)|Proj(_,_,_) -> true | _ -> false) pats2 in
                        let c2 = List.fold_left (fun r a2 ->
                                        match a2 with Sp(AppRes(_c),_) -> add_coeff r _c
                                                    | Proj(_,p,_) -> add_coeff r [(p,Num 1)]
                                                    | _ -> assert false
                                    )
                                    []
                                    projs
                        in
                        approx_coeff c c2
                    end
            | pats1,[Sp(AppRes(c),_)] ->
                    begin
                        let projs = List.filter (function Sp(AppRes _,_)|Proj(_,_,_) -> true | _ -> false) pats1 in
                        match projs with
                            | [] -> false       (* exact pattern on the left *)
                            | projs ->
                                let c1 = List.fold_left (fun r a1 ->
                                                match a1 with Sp(AppRes(_c),_) -> add_coeff r _c
                                                            | Proj(_,p,_) -> add_coeff r [(p,Num 1)]
                                                            | _ -> assert false
                                            )
                                            []
                                            projs
                                in
                                approx_coeff c1 c
                    end
            | Sp(AppRes _,_)::_,_ ->
                    debug "OOPS: %s" (string_of_sct_pattern ("pat1:",pats1)); assert false
            | _,(Sp(AppRes _,_))::_ ->
                    debug "OOPS: %s" (string_of_sct_pattern ("pat2:",pats2)); assert false

    in

    try
        let l1,r1 = p1 in
        let l2,r2 = p2 in
        let rename s (f,pats) = (f,List.map (rename_var s) pats) in
        let l1,r1 = rename "₁" l1, rename "₁" r1 in
        let l2,r2 = rename "₂" l2, rename "₂" r2 in
        let sigma,context1,context2 = unify l1 l2 in

        let subst (f,pats) = (f,List.map (subst_sct_term sigma) pats) in

        let r1 = subst r1 in
        let f1,pats1 = add_pattern_args r1 context2 in
        let r2 = subst r2 in
        let f2,pats2 = add_pattern_args r2 context1 in
        (* debug "r1=%s  and  r2=%s" (string_of_sct_pattern (f1,pats1)) (string_of_sct_pattern (f2,pats2)); *)

        f1 = f2 && approximates_aux pats1 pats2

    with UnificationError _ -> false

(* let approximates p1 p2 = *)
(*     let r = approximates p1 p2 in *)
(*     debug "approximates %s AND %s" (string_of_sct_clause p1) (string_of_sct_clause p2); *)
(*     if r then debug "TRUE" else debug "FALSE"; r *)


(* compatibility *)
(* similar to approximates *)
let coherent (p1:sct_clause) (p2:sct_clause) : bool =

    let rec coherent_aux pats1 pats2 =
        (* debug "pats1 = %s" (string_of_list " , " string_of_approx_term pats1); *)
        (* debug "pats2 = %s" (string_of_list " , " string_of_approx_term pats2); *)
        match pats1,pats2 with
            | [],[] -> true

            | (Angel _)::pats1,_::pats2
            | _::pats1,(Angel _)::pats2 -> coherent_aux pats1 pats2

            | (Daimon _)::pats1,_::pats2
            | _::pats1,(Daimon _)::pats2 -> coherent_aux pats1 pats2

            | Proj(d1,_,_)::pats1,Proj(d2,_,_)::pats2 when d1=d2 -> coherent_aux pats1 pats2
            | Proj(d1,_,_)::pats1,Proj(d2,_,_)::pats2 (*d1<>d2*) -> false

            | Var(x1,_)::pats1,Var(x2,_)::pats2 when x1=x2 -> coherent_aux pats1 pats2
            | Var(x1,_)::_,_ -> approximates p2 p1
            | _,Var(x2,_)::_-> approximates p1 p2

            | Const(c1,_,_)::pats1,Const(c2,_,_)::pats2 when c1=c2 -> coherent_aux pats1 pats2
            | Const(c1,_,_)::pats1,Const(c2,_,_)::pats2 (*when c1<>c2*) -> false

            | ((App _) as u1)::_pats1,((App _) as u2)::_pats2 ->
                    coherent_aux ((get_head u1)::(get_args u1)@_pats1) ((get_head u2)::(get_args u2)@_pats2)

            | Sp(AppArg [],_)::_,_
            | _,Sp(AppArg [],_)::_ -> assert false
            | Sp(AppArg xcs1,_)::pats1,Sp(AppArg xcs2,_)::pats2 ->
                    List.exists (function x2,_ ->
                    List.exists (function x1,_ ->
                            x1=x2
                        ) xcs1
                        ) xcs2 && coherent_aux pats1 pats2
                    (* FIXME: or simply "true" because both are approximations of the empty approximation?
                     * Note that the empty approximation doesn't have any decreasing argument... *)

            (* FIXME: too lax:      TODO: isn't it done?
            *     f x => f x
            * isn't coherent with
            *     f x => f <-1>x
            * note that this is sound: it may add some loops to check that aren't necessary... *)
            | (Sp(AppArg _,_) as a)::pats1,u2::pats2 ->
                begin
                    match get_head u2,get_args u2 with
                        | Const(_,p,_),args -> coherent_aux ((repeat a (List.length args))@pats1) (args@pats2)

                        | _ -> assert false
                end
            | u1::_pats1,Sp(AppArg _,_)::_ ->
                    coherent_aux ((collapse0 u1)::_pats1) pats2

            | pats1,[Sp(AppRes _,_)] -> 
                    if List.exists (function Sp(AppRes _,_) -> true | _ -> false) pats1
                    then true
                    else  approximates p2 p1
            | [Sp(AppRes _,_)],pats2 -> 
                    if List.exists (function Sp(AppRes _,_) -> true | _ -> false) pats2
                    then true
                    else approximates p1 p2

            (* TODO remove joker pattern to make sure I am not forgetting anything *)
            | _,_ -> false
    in

    try
        let l1,r1 = p1 in
        let l2,r2 = p2 in
        let rename s (f,pats) = (f,List.map (rename_var s) pats) in
        let l1,r1 = rename "₁" l1, rename "₁" r1 in
        let l2,r2 = rename "₂" l2, rename "₂" r2 in
        (* debug "        check if %s\nis coherent with %s" (string_of_sct_clause p1) (string_of_sct_clause p2); *)
        let sigma,context1,context2 = unify l1 l2 in

        (* debug "SIGMA: %s" (string_of_list ", " (function x,v -> fmt "%s=%s" x (string_of_approx_term v)) sigma); *)
        let subst (f,pats) = (f,List.map (subst_sct_term sigma) pats) in

        let r1 = subst r1 in
        let f1,pats1 = add_pattern_args r1 context2 in
        let r2 = subst r2 in
        let f2,pats2 = add_pattern_args r2 context1 in

        (* debug "  got %s and %s" (string_of_sct_pattern (f1,pats1))(string_of_sct_pattern (f2,pats2)); *)

        let r = f1 = f2 && coherent_aux pats1 pats2 in
        (* debug "%s" (string_of_bool r); *)
        r
    with UnificationError _ -> false
(* let coherent p1 p2 = *)
(*     let r = coherent p1 p2 in *)
(*     debug "coherent %s AND %s" (string_of_sct_clause p1) (string_of_sct_clause p2); *)
(*     if r then debug "TRUE" else debug "FALSE"; r *)

(* decreasing arguments *)
let decreasing (l,r : sct_clause)
  : bool
  =
    (* TODO check outside AppRes *)
    let rec decreasing_aux pats1 pats2 acc
      = match pats1,pats2 with
            | [],[] ->
                begin
                    let tmp = List.filter (function p,w -> w <> (Num 0)) acc in
                    try
                        match last tmp with
                            | (Some p,w) when even p -> negative_weight w
                            | _ -> false
                    with Invalid_argument "last" -> false
                end

            | _,[] -> assert false

            | pats1, (Sp(AppRes(c2),_))::pats2 ->
                begin
                    assert (pats2 = []);
                    let c = add_coeff
                                acc
                                (op_coeff (collapse_proj (List.map snd pats1))) in
                    let c = add_coeff c c2 in
                    let tmp = List.filter (function p,w -> w <> (Num 0)) c in
                    try
                        match last tmp with
                            | (Some p,w) when even p -> negative_weight w
                            | _ -> false
                    with Invalid_argument "last" -> false
                end

            | [],pats2 -> assert false

            | (coeff1,u1)::pats1, u2::pats2 ->
                begin
                    match get_head u1, get_args u1, get_head u2, get_args u2 with

                        | Proj(d1,p1,_),[],Proj(d2,p2,_),[] ->
                            assert (d1=d2);
                            assert (p1=p2);
                            decreasing_aux pats1 pats2 (add_coeff [p1,Num 0] acc)

                        | Proj _,_,Proj _,_ -> assert false

                        | Var(x1,_),[],_,_ ->
                            begin
                                match collapse0 u2 with
                                    | Sp(AppArg([(x,c)]),()) when x1=x ->
                                        begin
                                            let tmp = List.filter (function p,w -> w <> (Num 0)) (add_coeff c acc) in
                                            try
                                                match last tmp with
                                                    | (Some p,w) when odd p -> negative_weight w || decreasing_aux pats1 pats2 acc
                                                    | _ -> decreasing_aux pats1 pats2 acc
                                            with Invalid_argument "last" -> decreasing_aux pats1 pats2 acc
                                        end
                                    | Sp(AppArg(_),()) -> decreasing_aux pats1 pats2 acc
                                    | Daimon() -> decreasing_aux pats1 pats2 acc
                                    | Angel() -> true
                                    | _ -> assert false
                            end

                        | _,_,Var(x2,_),[] ->
                            begin
                                match collapse0 u1 with
                                    | Sp(AppArg([(x,c)]),()) when x2=x ->
                                        begin
                                            let tmp = List.filter (function p,w -> w <> (Num 0)) (add_coeff (op_coeff c) acc) in
                                            try
                                                match last tmp with
                                                    | (Some p,w) when odd p -> negative_weight w || decreasing_aux pats1 pats2 acc
                                                    | _ -> decreasing_aux pats1 pats2 acc
                                            with Invalid_argument "last" -> false
                                        end
                                            (* (match add_coeff c acc with [Some p, Num w] when odd p && w>0 -> todo "do something"; true   (1* TODO: do better *1) *)
                                            (*                                 | _ -> decreasing_aux pats1 pats2 acc) *)
                                    | Sp(AppArg(_),()) -> decreasing_aux pats1 pats2 acc  (* TODO: check *)
                                    | Daimon() -> assert false
                                    | Angel() -> assert false
                                    | _ -> assert false
                            end

                        | Const(c1,p1,_),args1,Const(c2,p2,_),args2 ->
                            assert (c1=c2);
                            assert (p1=p2);
                            let c= add_coeff coeff1 [p1,Num 0] in
                            let args1 = List.map (fun x -> c,x) args1 in
                            decreasing_aux (args1@pats1) (args2@pats2) acc


                        | _,_,Sp(AppArg [],_),_ -> assert false

                        | Const(_,p,_),args1,((Sp(AppArg apps,_)) as u2),[] ->
                            let app = add_coeff coeff1 [p,Num (-1)] in
                            let args1 = List.map (fun x -> app,x) args1 in
                            let args2 = repeat u2 (List.length args1) in
                            decreasing_aux (args1@pats1) (args2@pats2) acc

                        | _,_,Sp(AppArg _,_),_ -> assert false

                        | _,_,Angel _,_ -> true
                        | _,_,Daimon _,_ -> false

                        | Angel _,_,_,_ -> assert false
                        | Daimon _,_,_,_ -> assert false
                        | App _,_,_,_ | _,_,App _,_ -> assert false
                        | Sp _,_,_,_ -> assert false

                        | _,_,_,_ -> debug "OOPS, u1=%s and u2=%s" (string_of_approx_term u1) (string_of_approx_term u2); assert false
            (* TODO remove joker pattern to make sure I am not forgetting anything *)
                end
    in

    (* debug "check in %s and %s" (string_of_approx_term l) (string_of_approx_term (remove_result_constants r)); *)
    let f1,pats1 = l in
    let f2,pats2 = r in
    assert (f1=f2);
    decreasing_aux (List.map (fun p -> [],p) pats1) pats2 []

(* let decreasing cl = *)
(*     try decreasing cl *)
(*     with _ -> debug "OOPS %s" (string_of_sct_clause cl); assert false *)
