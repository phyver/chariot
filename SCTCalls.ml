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


let rec explode_approx v
  = let h,args = get_head v,get_args v in
    match h,args with
        | Var _,args | Const _,args | Angel _,args | Special((ApproxConst _),_),args-> h::args
        | Proj _,v::args -> (explode_approx v)@(h::args)
        | Special(ApproxProj _,_),[v] -> (explode_approx v)@[h]
        | Special(ApproxProj _,_),_ -> assert false
        | Proj _,[] -> assert false
        | App _,_ -> assert false

let term_to_sct_pattern (t:approx_term) : sct_pattern =
    match explode_approx t with
        | (Var(f,_))::args -> f,args
        | _ -> assert false

(* let explode_pattern pattern *)
(*   = *)
(*     let rec explode_aux pattern acc *)
(*       = match pattern with *)
(*             | (Var(f,_)) -> f,acc *)
(*             | App((Special (ApproxProj _,_) | Proj _) as proj,u,_) -> explode_aux u (proj::acc) *)
(*             | App(u1,u2,_) -> explode_aux u1 (u2::acc) *)
(*             | _ -> assert false *)
(*     in *)
(*     explode_aux pattern [] *)


(* collapsing the weights inside a term *)
let rec collapse_weight_in_term b u
  = match u with
        | Var _ | Const _ | Proj _ | Angel _ -> u
        | App(u1,u2) -> App(collapse_weight_in_term b u1, collapse_weight_in_term b u2)
        | Special(ApproxProj(p,w),t) -> Special(ApproxProj(p, collapse_weight b w),t)
        | Special(ApproxConst [],_) -> assert false
        | Special(ApproxConst apps,t) -> Special(ApproxConst(List.map (function p,w,x -> p, collapse_weight b w,x) apps),t)
let collapse_weight_in_pattern b (f,ps) =
    (f,List.map (collapse_weight_in_term b) ps)


(* misc operations on approximations *)

(* comparing two approximations *)
let compare_approx a1 a2     (* check if a1 is an approximation of a2, ie if a2 is more informative *)
  = match a1,a2 with
        | (Some 0,w1),(Some 0,w2) -> assert ((w1=Num 0) && (w2=Num 0)); true
        | (Some 0,w1),_ -> assert (w1=Num 0); false
        | (_,Infty), (Some 0,w2) -> assert (w2=Num 0); true
        | (_,Num w), (Some 0,w2) -> assert (w2=Num 0); w>=0

        | (None,w) , (Some _,_) -> true
        | (Some _,_),(None,w) -> false
        | (Some p1, w1) , (Some p2, w2) when p1<p2 -> true
        | (Some p1, w1) , (Some p2, w2) when p1>p2 -> false

        | (p1, Infty) , (p2, _) (*when p1=p2*) -> true
        | (p1, _) , (p2, Infty) (*when p1=p2*) -> false
        | (p1, Num w1) , (p2, Num w2) (*when p1=p2*) -> w2 <= w1

(* composing two approximations, for constructors *)
let sup_approx a1 a2
  = match a1,a2 with
        | (None,w1) , (None,w2) -> (None, sup_weight w1 w2)
        | (Some p1, w1) , (Some p2, w2) when p1<p2 -> (Some p2, w2)
        | (Some p1, w1) , (Some p2, w2) when p1>p2 -> (Some p1, w1)
        | (Some p1, w1) , (Some p2, w2) (*when p1=p2*) -> (Some p1, sup_weight w1 w2)
        | (None,w) , (Some _,_) | (Some _,_),(None,w) -> (None, w)

(* composing two approximations, for destructors *)
let add_approx a1 a2
  = match a1,a2 with
        | (None,w1) , (None,w2) -> (None, add_weight w1 w2)
        | (Some p1, w1) , (Some p2, w2) when p1<p2 -> (Some p2, w2)
        | (Some p1, w1) , (Some p2, w2) when p1>p2 -> (Some p1, w1)
        | (Some p1, w1) , (Some p2, w2) (*when p1=p2*) -> (Some p1, add_weight w1 w2)
        | (None,w) , (Some _,_) | (Some _,_),(None,w) -> (None, w)

let collapse_apps_proj args
  =
    let rec collapse_apps_proj_aux args acc
      = match args with
            | Special(ApproxProj(p1,w1),_)::args ->
                collapse_apps_proj_aux args (add_approx acc (p1,w1))
            | Proj(_,p,_)::args -> collapse_apps_proj_aux args (add_approx acc (p,Num 1))
            | _::args -> collapse_apps_proj_aux args acc
            | [] -> acc
    in collapse_apps_proj_aux args (Some 0,Num 0)

let app_all (f,args1:sct_pattern) (args2:approx_term list) : sct_pattern =
    let rec aux args = match args with
        | [] -> []
        | (Special(ApproxProj _,t))::_ ->
                let p,w = collapse_apps_proj args in
                [Special(ApproxProj(p,w),t)]
        | u::args -> u::(aux args)
    in f,aux(args1@args2)
(* let app_all (f,ps) qs = *)
(*     debug "before: %s" (string_of_sct_pattern (f,ps@qs)); *)
(*     let r = app_all (f,ps) qs in *)
(*     debug "after: %s" (string_of_sct_pattern r); *)
(*     r *)


(* simplify a sum of approximations *)
let simplify_approx aps =
    let aps = List.sort (fun t1 t2 -> let _,_,x1 = t1 and _,_,x2 = t2 in compare x1 x2) aps in
    let rec simplify_aux = function
        | [] -> []
        | [x] -> [x]
        | (p1,w1,x1)::(((_,_,x2)::_) as aps) when x1<x2 -> (p1,w1,x1)::(simplify_aux aps)
        | (p1,w1,x1)::(p2,w2,x2)::aps (*when x1<x2*) ->
                assert (x1=x2);
                let p,w = sup_approx (p1,w1) (p2,w2) in
                simplify_aux ((p,w,x1)::aps)
    in
    simplify_aux aps

(* merge two sums of approximations *)
let merge_approx as1 as2 =
    let as1 = List.sort (fun t1 t2 -> let _,_,x1 = t1 and _,_,x2 = t2 in compare x1 x2) as1 in
    let as2 = List.sort (fun t1 t2 -> let _,_,x1 = t1 and _,_,x2 = t2 in compare x1 x2) as2 in
    let rec merge_aux as1 as2 = match as1,as2 with
        | as1 , [] | [] , as1 -> as1
        | (p1,w1,x1)::as1 , (_,_,x2)::_ when x1<x2 -> (p1,w1,x1)::(merge_aux as1 as2)
        | (_,_,x1)::_ , (p2,w2,x2)::as2 when x1>x2 -> (p2,w2,x2)::(merge_aux as1 as2)
        | (p1,w1,x1)::as1 , (p2,w2,x2)::as2 (*when x1=x2*) ->
                let (p,w) = sup_approx (p1,w1) (p2,w2) in
                (p,w,x1)::(merge_aux as1 as2)
    in
    merge_aux as1 as2


(* collapse all the constructors from a contructorn pattern with approximations *)
let rec collapse0 p = match get_head p,get_args p with
    | Var(x,_),[] -> [ (Some 0, Num 0, x) ]
    | Angel _,[] -> assert false (* FIXME *)
    | Special (ApproxConst [],_),_ -> assert false
    | Special (ApproxConst ap,_),[] -> ap
    | Const(_,prio,_),[] -> [ (prio, Num 1, "()") ]
    | Const(_,prio,_),ps ->
        begin
            let approx_s = List.map collapse0 ps in
            let approx = List.fold_left (fun as1 as2 -> merge_approx as1 (simplify_approx as2)) [] approx_s in  (* NOTE: not necessary to simplify as1: it is the recursive call and is simplified *)
            List.map (function (p,w,x) -> let p,w = add_approx (prio,Num 1) (p,w) in (p,w,x)) approx
        end
    | Proj _,_ | Special (ApproxProj _,_),[] -> debug "OOPS: %s" (string_of_approx_term p); assert false
    | _,_ -> assert false

let collapse_pattern (depth:int) (pattern:sct_pattern) : sct_pattern
  =
    (* collapse the constructors at given depth from a constructor pattern with approximations *)
    let rec collapse_const d p =
        match get_head p,get_args p with
            | Special (ApproxConst [],_),_ -> assert false
            | Var _,[] | Angel _,[] | Special (ApproxConst _,_),[] -> p
            | Const(c,prio,_),ps ->
                if d=0
                then Special (ApproxConst (collapse0 p),())
                else app (Const(c,prio,())) (List.map (collapse_const (d-1)) ps)
            | _,_ -> assert false

    in

    (* collapse the pattern of a definition at a given depth *)
    let rec collapse_aux dp ps
      = match ps with
        | [] -> []
        | (Proj _ as d)::ps when dp>0 ->
            d::(collapse_aux (dp-1) ps)
        | (Proj(_,prio,t))::ps (*when dp=0*) ->
            let p,w = collapse_apps_proj ((Special(ApproxProj(prio,Num 1),t))::ps) in
            [Special(ApproxProj(p,w),t)]
        | [Special(ApproxProj _,_)] as ps -> ps
        | (Special(ApproxProj _,_))::_ -> assert false
        | p::ps -> (collapse_const depth p)::(collapse_aux dp ps)
    in

    let collapse dp (f,ps:sct_pattern) : sct_pattern
      = f,collapse_aux dp ps
    in

    collapse depth pattern



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

let rec subst_approx_term_aux sigma acc apps
  = match apps with
        | [] -> acc
        | ((prio,weight,x) as a)::apps ->
            try
                let apps2 = collapse0 (List.assoc x sigma) in
                let apps2 = List.map (function p,w,y -> let p,w = add_approx (p,w) (prio,weight) in (p,w,y)) apps2 in
                subst_approx_term_aux sigma (merge_approx apps2 acc) apps
            with Not_found -> subst_approx_term_aux sigma (a::acc) apps

let rec subst_approx_term sigma v
  = match v with
        | Var(x,t) -> (try List.assoc x sigma with Not_found -> Var(x,t))
        | (Angel _|Const _|Proj _|Special(ApproxProj _,_)) as v -> v
        | App(v1,v2) -> App(subst_approx_term sigma v1, subst_approx_term sigma v2)
        | Special(ApproxConst [],_) -> assert false
        | Special(ApproxConst apps,t) -> Special(ApproxConst (subst_approx_term_aux sigma [] apps),t)
(* let subst_approx_term sigma v = *)
(*     debug "sigma = %s" (string_of_list " , " (function x,v -> fmt "%s:=%s" x (string_of_approx_term v)) sigma); *)
(*     debug "before %s" (string_of_approx_term v); *)
(*     let v = subst_approx_term sigma v in *)
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

            | Special(ApproxConst [],_),_ -> assert false
            | Special(ApproxConst apps,_),[] ->
                let x = new_var() in
                (Var(x,()), List.map (function (p,w,y) -> (y,Special(ApproxConst [p, op_weight w,x],()))) apps)

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

            | [(Special(ApproxProj(p,w),t))] ->
                    [], [] , Some (Special(ApproxProj(p,op_weight w),t))
            | (Special(ApproxProj(p,w),_))::_ -> assert false

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

    let patterns_r = List.map (subst_approx_term sigma) patterns_r in

    let cl_r = match app_res with None -> (f_r,patterns_r)
                                | Some app -> app_all (f_r,patterns_r) [app]
    in

    (*   (1* debug "obtained %s" (string_of_sct_clause (lhs,rhs)) *1) *)

    (f_l,patterns_l) , cl_r


let rec rename_var x v
    = match v with
        | Var("()",_) -> v
        | Var(y,t) -> Var(y^x,t)
        | App(v1,v2) -> App(rename_var x v1, rename_var x v2)
        | Const _ | Proj _ | Angel _ -> v
        | Special(ApproxConst [],_) -> assert false
        | Special(ApproxConst apps,t) -> Special(ApproxConst (List.map (function p,w,y -> if y="()" then p,w,y else p,w,y^x) apps),t)
        | Special(ApproxProj _,_) -> v
        (* | _ -> assert false *)


(* unify the rhs of a clause with the lhs of another *)
let unify ?(allow_approx=false) (f_r,patterns_r:sct_pattern) (f_l,patterns_l:sct_pattern)
  :   (var_name * approx_term) list     (* the substitution *)
    * approx_term list                  (* the arguments that were in lhs but not in rhs *)
    * approx_term list                  (* the arguments that were in rhs but not in lhs *)  (* NOTE: at most one of those lists is non-empty *)
  =

    assert (f_r = f_l);

    (* TODO: rewrite to have a list of equations as argument *)
    let rec unify_aux (ps_r:approx_term list) (ps_l:approx_term list)
                      (sigma:(var_name*approx_term) list)
      : (var_name*approx_term) list * approx_term list * approx_term list
      = match ps_r,ps_l with
            | [],[] -> sigma,[],[]

            | u_r::ps_r,u_l::ps_l when u_r=u_l -> unify_aux ps_r ps_l sigma

            | App(u_r,v_r)::ps_r,App(u_l,v_l)::ps_l -> unify_aux (u_r::v_r::ps_r) (u_l::v_l::ps_l) sigma

            | Special(ApproxConst [],_)::_,_ -> assert false

            | Special(ApproxConst apps_r,_)::ps_r,u_l::ps_l ->
                if allow_approx
                then
                    let apps_l = collapse0 u_l in
                    let tau = List.map (function p,w,x -> (x,Special(ApproxConst(List.map (function _p,_w,_x -> let p,w = add_approx (_p,_w) (p, op_weight w) in p,w,_x) apps_r),())) ) apps_l in
                    unify_aux ps_r ps_l (tau @ (List.map (second (subst_approx_term sigma)) sigma))
                else
                    assert false

            | u_r::ps_r,Special(ApproxConst apps_l,_)::ps_l ->
                    assert false (*raise (UnificationError "approximation on the right not allowed during unification")*)

            | [Special(ApproxProj(p,w),_)],ps_l ->
                if allow_approx
                then
                    let tmp = List.filter (function Proj _ | Special(ApproxProj _,_) -> true | _ -> false) ps_l in
                    let tmp = List.map (function Proj(_,p,_) -> (p,Num 1) | Special(ApproxProj(p,w),_) -> (p,w) | _ -> assert false) tmp in
                    let p,w = List.fold_left (fun ap1 ap2 -> add_approx ap1 (fst ap2, op_weight (snd ap2))) (p,w) tmp in
                    (* sigma,[],[Special(ApproxProj(p,w))] *)
                    sigma,[Special(ApproxProj(p,w),())],[]
                else
                    assert false

            | ps_r,[Special(ApproxProj(p,w),_)] ->
                    assert false (*raise (UnificationError "approximation on the right not allowed during unification")*)

            | Var(x_r,_)::ps_r,u_l::ps_l -> unify_aux (List.map (subst_approx_term [x_r,u_l]) ps_r) ps_l ((x_r,u_l)::(List.map (second (subst_approx_term [x_r,u_l])) sigma))
            | u_r::ps_r,Var(x_l,_)::ps_l -> unify_aux ps_r (List.map (subst_approx_term [x_l,u_r]) ps_l) ((x_l,u_r)::(List.map (second (subst_approx_term [x_l,u_r])) sigma))

            | ps_r,[] -> sigma,ps_r,[]
            | [],ps_l -> sigma,[],ps_l


            | Special(ApproxProj(p,w),_)::_,_
            | _,Special(ApproxProj(p,w),_)::_ ->
                    debug "OOPS";
                    debug "ps_l = %s" (string_of_list " " string_of_approx_term ps_l);
                    debug "ps_r = %s" (string_of_list " " string_of_approx_term ps_r);
                    assert false

            | _,_ -> raise (UnificationError ("cannot unify " ^ (string_of_list " " string_of_approx_term ps_r) ^ " and " ^ (string_of_list " " string_of_approx_term ps_l)))

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
        let subst (f,pats) = (f,List.map (subst_approx_term sigma) pats) in
        let l = subst l1 in
        let r = subst r2 in
(* debug "obtained %s" (string_of_sct_clause (l,r)); *)
        let r = normalize_sct_clause (app_all l context2 , app_all r context1) in
(* debug "after renormalization %s" (string_of_sct_clause r); *)
        r
    with
        UnificationError err -> raise Impossible_case


let collapse_clause b d (l,r:sct_clause) : sct_clause
  =
    let l = collapse_pattern d l in
    let r = collapse_pattern d r in
    let l,r = normalize_sct_clause (l,r) in
    let r = collapse_weight_in_pattern b r in
    l,r


let collapsed_compose (b:int) (d:int) (c1:sct_clause) (c2:sct_clause) : sct_clause
  =
    (* debug "composing:  %s   and   %s" (string_of_sct_clause c1) (string_of_sct_clause c2); *)
    let l,r = compose c1 c2
    in
    (* debug "   l,r:  %s " (string_of_sct_clause (l,r)); *)
    let result = collapse_clause b d (l,r)
    in
    (* debug "   result:  %s " (string_of_sct_clause result); *)
    result



(* order *)
let approx_approx (p1,w1) (p2,w2) =
    match p1,p2 with
        | None,_ -> true
        | Some p1,Some p2 when p1 > p2 -> true
        | _,None -> false
        | Some p1,Some p2 when p1 < p2 -> false
        | Some p1,Some p2 (*when p1=p2*) ->
            begin
                match w1,w2 with
                    | Infty,_ -> true
                    | _,Infty -> false
                    | Num w1,Num w2 -> w1 >= w2
            end

(* check if p1 approximates p2 *)
let approximates p1 p2 =

    let rec approximates_aux pats1 pats2 =
        (* debug "pats1 = %s" (string_of_list " , " string_of_approx_term pats1); *)
        (* debug "pats2 = %s" (string_of_list " , " string_of_approx_term pats2); *)
        match pats1,pats2 with
            | [],[] -> true
            | Proj(d1,_,_)::pats1,Proj(d2,_,_)::pats2 -> d1=d2 && approximates_aux pats1 pats2
            | Var(x1,_)::pats1,Var(x2,_)::pats2 -> x1=x2 && approximates_aux pats1 pats2
            | Const(c1,_,_)::pats1,Const(c2,_,_)::pats2 -> c1=c2 && approximates_aux pats1 pats2
            | ((App _) as u1)::_pats1,((App _) as u2)::_pats2 ->
                    approximates_aux ((get_head u1)::(get_args u1)@_pats1) ((get_head u2)::(get_args u2)@_pats2)
            | Special(ApproxConst [],_)::_,_
            | _,Special(ApproxConst [],_)::_ -> assert false
            | Special(ApproxConst apps1,t1)::pats1,Special(ApproxConst apps2,t2)::pats2 ->
                    (* debug "left: %s, right: %s" *)
                    (*     (string_of_approx_term (Special(ApproxConst apps1,t1))) *)
                    (*     (string_of_approx_term (Special(ApproxConst apps2,t2))); *)
                let b = List.for_all (function p2,w2,x2 ->
                        List.exists  (function p1,w1,x1 ->
                            (* debug "x1=%s, x2=%s, p1=%s, p2=%s, w1=%s, w2=%s" x1 x2 (string_of_priority p1) (string_of_priority p2) (string_of_weight w1) (string_of_weight w2); *)
                                x1=x2 && (compare_approx (p1,w1) (p2,w2))
                            )
                            apps1)
                            apps2
                in b && approximates_aux pats1 pats2
            | Special(ApproxConst _,_)::_,u2::_pats2 ->
                    let aps2 = collapse0 u2 in
                    approximates_aux pats1 (Special(ApproxConst aps2,())::_pats2)
            | [Special(ApproxProj(p,w),_)],pats2 ->
                    begin
                        let projs = List.filter (function Special(ApproxProj _,_) -> true | _ -> false) pats2 in
                        let p2,w2 = List.fold_left (fun r a2 ->
                                        match a2 with Special(ApproxProj(_p,_w),_) -> add_approx r (_p,_w)
                                                    | _ -> assert false
                                    )
                                    (Some 0, Num 0)
                                    projs
                        in
                        approx_approx (p,w) (p2,w2)
                    end
            | _,_ -> false
    in

    try
        let l1,r1 = p1 in
        let l2,r2 = p2 in
        let rename s (f,pats) = (f,List.map (rename_var s) pats) in
        let l1,r1 = rename "₁" l1, rename "₁" r1 in
        let l2,r2 = rename "₂" l2, rename "₂" r2 in
        let sigma,context1,context2 = unify l1 l2 in

        let subst (f,pats) = (f,List.map (subst_approx_term sigma) pats) in

        let r1 = subst r1 in
        let f1,pats1 = app_all r1 context2 in
        let r2 = subst r2 in
        let f2,pats2 = app_all r2 context1 in
        (* debug "r1=%s  and  r2=%s" (string_of_sct_pattern (f1,pats1)) (string_of_sct_pattern (f2,pats2)); *)

        f1 = f2 && approximates_aux pats1 pats2

    with UnificationError _ -> false


let rec repeat x n =
    if n = 0
    then []
    else x::(repeat x (n-1))

(* compatibility *)
(* similar to approximates *)
let compatible (p1:sct_clause) (p2:sct_clause) : bool =

    let rec compatible_aux pats1 pats2 =
        (* debug "pats1 = %s" (string_of_list " , " string_of_approx_term pats1); *)
        (* debug "pats2 = %s" (string_of_list " , " string_of_approx_term pats2); *)
        match pats1,pats2 with
            | [],[] -> true
            | Proj(d1,_,_)::pats1,Proj(d2,_,_)::pats2 -> d1=d2 && compatible_aux pats1 pats2
            | Var(x1,_)::pats1,Var(x2,_)::pats2 when x1=x2 -> compatible_aux pats1 pats2
            | Var(x1,_)::_,_ -> approximates p2 p1
            | _,Var(x2,_)::_-> approximates p1 p2
            | Const(c1,_,_)::pats1,Const(c2,_,_)::pats2 -> c1=c2 && compatible_aux pats1 pats2
            | ((App _) as u1)::_pats1,((App _) as u2)::_pats2 ->
                    compatible_aux ((get_head u1)::(get_args u1)@_pats1) ((get_head u2)::(get_args u2)@_pats2)
            | Special(ApproxConst [],_)::_,_
            | _,Special(ApproxConst [],_)::_ -> assert false
            | Special(ApproxConst apps1,_)::pats1,Special(ApproxConst apps2,_)::pats2 ->
                    List.exists (function _,_,x2 ->
                    List.exists (function _,_,x1 ->
                            x1=x2
                        ) apps1
                        ) apps2
                    (* FIXME: or simply "true" because both are approximations of the empty approximation?
                     * Note that the empty approximation doesn't have any decreasing argument... *)

            (* FIXME: too lax:
            *     f x => f x
            * isn't compatible with
            *     f x => f <-1>x
            * note that this is sound: it may add some loops to check that aren't necessary... *)
            | (Special(ApproxConst _,_) as a)::pats1,u2::pats2 ->
                begin
                    (* let aps2 = collapse0 u2 in *)
                    (* compatible_aux pats1 (Special(ApproxConst aps2)::_pats2) *)
                    match get_head u2,get_args u2 with
                        | Const(_,p,_),args -> compatible_aux ((repeat a (List.length args))@pats1) (args@pats2)

                        | _ -> assert false
                end
            | u1::_pats1,Special(ApproxConst _,_)::_ ->
                    let aps1 = collapse0 u1 in
                    compatible_aux (Special(ApproxConst aps1,())::_pats1) pats2

            (* FIXME: is that right? *)
            | [Special(ApproxProj _,_)],_
            | _,[Special(ApproxProj _,_)] ->
                    true

            | _,_ -> false
    in

    try
        let l1,r1 = p1 in
        let l2,r2 = p2 in
        (* debug "          check if %s\nis compatible with %s" (string_of_sct_clause p1) (string_of_sct_clause p2); *)
        let sigma,context1,context2 = unify l1 l2 in

        let subst (f,pats) = (f,List.map (subst_approx_term sigma) pats) in

        let r1 = subst r1 in
        let f1,pats1 = app_all r1 context2 in
        let r2 = subst r2 in
        let f2,pats2 = app_all r2 context1 in

        (* debug "  got %s and %s" (string_of_sct_pattern (f1,pats1))(string_of_sct_pattern (f2,pats2)); *)

        let r = f1 = f2 && compatible_aux pats1 pats2 in
        (* debug "%s" (string_of_bool r); *)
        r


    with UnificationError _ -> false

(* decreasing arguments *)
let decreasing (l,r : sct_clause)
  : bool
  =
    (* TODO check outside ApproxProj *)
    let rec decreasing_aux pats1 pats2 acc
      = match pats1,pats2 with
            | [],[] -> (match acc with (Some p, Num w) when even p && w<0 -> true | _ -> false)

            | _,[] -> assert false 

            | pats1, (Special(ApproxProj(prio2,w2),_))::pats2 ->
                begin
                    assert (pats2 = []);
                    let app = add_approx
                                acc
                                (collapse_apps_proj (List.map snd pats1)) in
                    match app with
                        | _,Infty -> assert false
                        | p,w ->
                            match add_approx (prio2,w2) (p,op_weight w) with
                                | (None,Num w) -> w<0
                                | (Some p, Num w) when even p -> w<0
                                | _ -> false
                end
            | [],pats2 -> assert false

            | (app1,u1)::pats1, u2::pats2 ->
                begin
                    match get_head u1, get_args u1, get_head u2, get_args u2 with

                        | Proj(d1,p1,_),[],Proj(d2,p2,_),[] ->
                            assert (d1=d2);
                            assert (p1=p2);
                            decreasing_aux pats1 pats2 (add_approx (p1,Num 0) acc)

                        | Proj _,_,Proj _,_ -> assert false

                        | Var(x1,_),[],_,_ ->
                            begin
                                match collapse0 u2 with
                                    | [(p,w,x)] when x1=x ->
                                            (match add_approx (p,w) acc with (Some p, Num w) when odd p && w<0 -> true
                                                                            | _ -> decreasing_aux pats1 pats2 acc)
                                    | _ -> decreasing_aux pats1 pats2 acc
                            end
                        | _,_,Var(x2,_),[] ->
                            begin
                                match collapse0 u1 with
                                    | [(p,w,x)] when x2=x ->
                                            (match add_approx (p,w) acc with (Some p, Num w) when odd p && w>0 -> true
                                                                            | _ -> decreasing_aux pats1 pats2 acc)
                                    | _ -> decreasing_aux pats1 pats2 acc
                            end

                        | Const(c1,p1,_),args1,Const(c2,p2,_),args2 ->
                            assert (c1=c2);
                            assert (p1=p2);
                            let app = add_approx app1 (p1,Num 0) in
                            let args1 = List.map (fun x -> app,x) args1 in
                            decreasing_aux (args1@pats1) (args2@pats2) acc


                        | _,_,Special(ApproxConst [],_),_ -> assert false

                        | Const(_,p,_),args1,((Special(ApproxConst apps,_)) as u2),[] ->
                            let app = add_approx app1 (p,Num (-1)) in
                            let args1 = List.map (fun x -> app,x) args1 in
                            let args2 = repeat u2 (List.length args1) in
                            decreasing_aux (args1@pats1) (args2@pats2) acc

                        (* | Proj(_,p,_),[],Special(ApproxProj(prio2,w2),_),_ ->       (1* do this also when pats1 is empty *1) *)
                        (*     begin *)
                        (*         assert (pats2 = []); *)
                        (*         let app = add_approx *)
                        (*                     acc *)
                        (*                     (collapse_apps_proj (List.map snd ((app1,u1)::pats1))) in *)
                        (*         match app with *)
                        (*             | _,Infty -> assert false *)
                        (*             | p,w -> *)
                        (*                 begin *)
                        (*                     match add_approx (prio2,w2) (p,op_weight w) with *)
                        (*                         | (None,Num w) -> w<0 *)
                        (*                         | (Some p, Num w) when even p -> w<0 *)
                        (*                         | _ -> false *)
                        (*                 end *)
                        (*     end *)

                        | _,_,Special(ApproxConst _,_),_ -> assert false

                        | _,_,Angel _,_ -> true   (* FIXME: if the Angel isn't in a data, it should be "false" *)

                        | Angel _,_,_,_ -> assert false
                        | App _,_,_,_ | _,_,App _,_ -> assert false
                        | Special _,_,_,_ -> assert false

                        | _,_,_,_ -> debug "OOPS, u1=%s and u2=%s" (string_of_approx_term u1) (string_of_approx_term u2); assert false
                end
    in

    (* debug "check in %s and %s" (string_of_approx_term l) (string_of_approx_term (remove_result_constants r)); *)
    let f1,pats1 = l in
    let f2,pats2 = r in
    assert (f1=f2);
    decreasing_aux (List.map (fun p -> (Some 0,Num 0),p) pats1) pats2 (Some 0, Num 0)


let decreasing cl =
    try decreasing cl
    with _ -> debug "OOPS %s" (string_of_sct_clause cl); assert false
