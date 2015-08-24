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


let explode_pattern pattern
  =
    let rec explode_aux pattern acc
      = match pattern with
            | (Var(f,_)) -> f,acc
            | App((Special (ApproxProj _,_) | Proj _) as proj,u,_) -> explode_aux u (proj::acc)
            | App(u1,u2,_) -> explode_aux u1 (u2::acc)
            | _ -> assert false
    in
    explode_aux pattern []


(* collapsing the weights inside a term *)
let rec collapse_weight_in_term b u
  = match u with
        | Var _ | Const _ | Proj _ | Angel _ -> u
        | App(u1,u2,t) -> App(collapse_weight_in_term b u1, collapse_weight_in_term b u2,t)
        | Special(ApproxProj(p,w),t) -> Special(ApproxProj(p, collapse_weight b w),t)
        | Special(ApproxConst [],_) -> assert false
        | Special(ApproxConst apps,t) -> Special(ApproxConst(List.map (function p,w,x -> p, collapse_weight b w,x) apps),t)


(* misc operations on approximations *)
let add_approx a1 a2
  = match a1,a2 with
        | (None,w1) , (None,w2) -> (None, add_weight w1 w2)
        | (Some p1, w1) , (Some p2, w2) when p1<p2 -> (Some p2, w2)
        | (Some p1, w1) , (Some p2, w2) when p1>p2 -> (Some p1, w1)
        | (Some p1, w1) , (Some p2, w2) (*when p1=p2*) -> (Some p1, add_weight w1 w2)
        | (None,w) , (Some _,_) | (Some _,_),(None,w) -> (None, w)

let rec collapse_apps_proj args
  = match args with
        | Special(ApproxProj(p1,w1),t1)::Special(ApproxProj(p2,w2),t2)::args ->
            let p,w = add_approx (p1,w1) (p2,w2) in
            assert (t1=t2);
            collapse_apps_proj (Special(ApproxProj(p,w),t1)::args)
        | _ -> List.rev args

let rec app_all u args =
    match args with
        | [] -> u
        | Proj(d,p,t)::args -> app_all (App( Proj(d,p,t) , u , ())) args
        | [Special(ApproxProj(p,w),t)] -> App( Special(ApproxProj(p,w),t) , u , () )
        | Special(ApproxProj _,_)::_ -> assert false
        | arg::args -> app_all (App(u,arg,())) args
let app_all u args =
    (* FIXME: ugly hack to make sure the approximations on the result are collapsed together *)
    let u,args1 = explode_pattern u in
    let args = collapse_apps_proj (List.rev (args1 @ args)) in
    let u = Var(u,()) in
    (* debug "app_all %s with %s" (string_of_approx_term u) (string_of_list "," string_of_approx_term args); *)
    app_all u args


let simplify_approx aps =
    let aps = List.sort (fun t1 t2 -> let _,_,x1 = t1 and _,_,x2 = t2 in compare x1 x2) aps in
    let rec simplify_aux = function
        | [] -> []
        | [x] -> [x]
        | (p1,w1,x1)::(((_,_,x2)::_) as aps) when x1<x2 -> (p1,w1,x1)::(simplify_aux aps)
        | (p1,w1,x1)::(p2,w2,x2)::aps (*when x1<x2*) ->
                assert (x1=x2);
                let p,w = add_approx (p1,w1) (p2,w2) in
                simplify_aux ((p,w,x1)::aps)
    in
    simplify_aux aps

let merge_approx as1 as2 =
    let as1 = List.sort (fun t1 t2 -> let _,_,x1 = t1 and _,_,x2 = t2 in compare x1 x2) as1 in
    let as2 = List.sort (fun t1 t2 -> let _,_,x1 = t1 and _,_,x2 = t2 in compare x1 x2) as2 in
    let rec merge_aux as1 as2 = match as1,as2 with
        | as1 , [] | [] , as1 -> as1
        | (p1,w1,x1)::as1 , (_,_,x2)::_ when x1<x2 -> (p1,w1,x1)::(merge_aux as1 as2)
        | (_,_,x1)::_ , (p2,w2,x2)::as2 when x1>x2 -> (p2,w2,x2)::(merge_aux as1 as2)
        | (p1,w1,x1)::as1 , (p2,w2,x2)::as2 (*when x1=x2*) ->
                let (p,w) = add_approx (p1,w1) (p2,w2) in
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
    | Proj _,_ | Special (ApproxProj _,_),[] -> assert false
    | _,_ -> assert false

let collapse_pattern (depth:int) (pattern:approx_term) : approx_term
  =
    (* count the number of destructors in a definition pattern *)
    let rec count_proj p = match get_head p, get_args p with
        | Var _,_ -> 0
        | Proj _,p::_ -> 1 + (count_proj p)
        | Special (ApproxProj _,t),p::_ -> 1 + (count_proj p)
        | _,_ -> assert false
    in

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
    let rec collapse dp p = match get_head p, get_args p with
        | Proj _,[] -> assert false
        | Proj(_,prio,_), p::_ when dp>0->
            begin
                let p = collapse (dp-1) p in
                match get_head p, get_args p with
                    | Special(ApproxProj(_prio,_w),_),ps ->
                        let prio,w = add_approx (_prio,_w) (prio,Num 1) in
                        app (Special(ApproxProj(prio, w),())) ps
                    | h,ps -> App(Special(ApproxProj(prio,Num 1),()), app h ps,())
            end
        | Proj(d,prio,_),p::ps (*when pd=0*) ->
                app (Proj(d,prio,())) ((collapse dp p)::List.map (collapse_const depth) ps)
        | Special(ApproxProj(prio,w),_),[p] -> App( Special(ApproxProj(prio,w),()) , collapse dp p,())
        | Special(ApproxProj _,_),_ -> assert false
        | Var(f,_),ps -> app (Var(f,())) (List.map (collapse_const depth) ps)
        | (Angel _ | Const _ | App _ | Special(ApproxConst _,_)),ps -> assert false
    in

    collapse ((count_proj pattern)-depth) pattern



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
        | App(v1,v2,t) -> App(subst_approx_term sigma v1, subst_approx_term sigma v2,t)
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
    (* debug "normalize with %s" (string_of_sct_clause (lhs,rhs)); *)

    (* TODO: rename dangling variables on the RHS to "!x" *)

    (* debug "normalizing %s" (string_of_sct_clause (lhs,rhs)); *)
    let n = ref 0
    in

    let new_var () = incr n; "x"^sub_of_int !n
    in

    let add_approx_res app res =
        match app, res with
            | Some(prio,w), App (Special(ApproxProj(_prio,_w),()), res, ()) ->
                let prio,w = add_approx (_prio,_w) (prio,w) in
                App (Special(ApproxProj(prio,w),()),res,())
            | Some(prio,w), res ->
                App (Special(ApproxProj(prio,w),()),res,())
            | None, res -> res
    in

    let rec process_pattern p =
        match get_head p, get_args p with
            | Var(x,t),[] -> let y = new_var() in (Var(y,t), [x,Var(y,t)])
            | Const(c,p,t), args ->
                let tmp = List.map process_pattern args in
                let sigma = List.concat (List.map snd tmp) in
                let args = List.map fst tmp in
                (app (Const(c,p,t)) args , sigma)
            | Special(ApproxConst [],_),_ -> assert false
            | Special(ApproxConst apps,_),[] ->
                let x = new_var() in
                (Var(x,()), List.map (function (p,w,y) -> (y,Special(ApproxConst [p, op_weight w,x],()))) apps)
            | _ -> assert false
    in

    let rec process_lhs lhs =
        match get_head lhs, get_args lhs with
            | Var(f,t),args ->
                let tmp = List.map process_pattern args in
                let sigma = List.concat (List.map snd tmp) in
                let args = List.map fst tmp in
                (None, app (Var(f,t)) args, sigma)
            | Proj(d,p,t),lhs::args ->
                begin
                    match process_lhs lhs with
                        | None, lhs, tau ->
                            let tmp = List.map process_pattern args in
                            let sigma = List.concat (List.map snd tmp) in
                            let args = List.map fst tmp in
                            (None, app (Proj(d,p,t)) (lhs::args), tau@sigma)
                        | _ -> assert false
                end
            | Special(ApproxProj(p,w),t),[lhs] ->
                begin
                    match process_lhs lhs with
                        | None, lhs, sigma -> Some (p, op_weight w) , lhs, sigma
                        | _ -> assert false
                end
            | _,_ -> assert false
    in
    let process_lhs lhs =
        (* debug "process_lhs with %s" (string_of_approx_term lhs); *)
        process_lhs lhs
    in

    let app_res, lhs, sigma = process_lhs lhs
    in

    let rhs = add_approx_res app_res (subst_approx_term sigma rhs)
    in

      (* debug "obtained %s" (string_of_sct_clause (lhs,rhs)) *)
    lhs,rhs


let rec rename_var_aux x v
    = match v with
        | Var("()",_) -> v
        | Var(y,t) -> Var(y^x,t)
        | App(v1,v2,t) -> App(rename_var_aux x v1, rename_var_aux x v2,t)
        | Const _ | Proj _ | Angel _ -> v
        | Special(ApproxConst [],_) -> assert false
        | Special(ApproxConst apps,t) -> Special(ApproxConst (List.map (function p,w,y -> if y="()" then p,w,y else p,w,y^x) apps),t)
        | _ -> assert false

let rec rename_var x v
  = match get_head v,get_args v with
        | Var(f,t),args -> app (Var(f,t)) (List.map (rename_var_aux x) args)
        | Proj(d,p,t),v::args -> app (Proj(d,p,t)) ((rename_var x v)::(List.map (rename_var_aux x) args))
        | Special(ApproxProj(p,w),t),[v] -> App(Special(ApproxProj(p,w),t), rename_var x v,())
        | _ -> assert false




(* unify the rhs of a clause with the lhs of another *)
let unify ?(allow_right_approx=false) (rhs:approx_term) (lhs:approx_term)
  :   (var_name * approx_term) list     (* the substitution *)
    * approx_term list                  (* the arguments that were in lhs but not in rhs *)
    * approx_term list                  (* the arguments that were in rhs but not in lhs *)  (* NOTE: at most one of those lists is non-empty *)
  =

    let f_r,patterns_r = explode_pattern rhs in
    let f_l,patterns_l = explode_pattern lhs in
    assert (f_r = f_l);

    let rec unify_aux (ps_r:approx_term list) (ps_l:approx_term list)
                      (sigma:(var_name*approx_term) list)
      : (var_name*approx_term) list * approx_term list * approx_term list
      = match ps_r,ps_l with
            | [],[] -> sigma,[],[]

            | u_r::ps_r,u_l::ps_l when u_r=u_l -> unify_aux ps_r ps_l sigma

            | App(u_r,v_r,_)::ps_r,App(u_l,v_l,_)::ps_l -> unify_aux (u_r::v_r::ps_r) (u_l::v_l::ps_l) sigma

            | Special(ApproxConst [],_)::_,_ -> assert false

            | Special(ApproxConst apps_r,_)::ps_r,u_l::ps_l ->
                let apps_l = collapse0 u_l in
                let tau = List.map (function p,w,x -> (x,Special(ApproxConst(List.map (function _p,_w,_x -> let p,w = add_approx (_p,_w) (p, op_weight w) in p,w,_x) apps_r),())) ) apps_l in
                unify_aux ps_r ps_l (tau @ (List.map (second (subst_approx_term sigma)) sigma))

            | u_r::ps_r,Special(ApproxConst apps_l,_)::ps_l ->
                    (* if allow_right_approx *)
                    (* then *)
                    (*     let apps_r = collapse0 u_r in *)
                    (*     let tau = List.map (function p,w,x -> (x,Special(ApproxConst(List.map (function _p,_w,_x -> let p,w = add_approx (_p,_w) (p, op_weight w) in p,w,_x) apps_l))) ) apps_r in *)
                    (*     unify_aux ps_r ps_l (tau @ (List.map (second (subst_approx_term sigma)) sigma)) *)
                    (* else raise (UnificationError "approximation on the right not allowed during unification") *)
                    raise (UnificationError "approximation on the right not allowed during unification")

            | [Special(ApproxProj(p,w),_)],ps_l ->
                let tmp = List.filter (function Proj _ | Special(ApproxProj _,_) -> true | _ -> false) ps_l in
                let tmp = List.map (function Proj(_,p,_) -> (p,Num 1) | Special(ApproxProj(p,w),_) -> (p,w) | _ -> assert false) tmp in
                let p,w = List.fold_left (fun ap1 ap2 -> add_approx ap1 (fst ap2, op_weight (snd ap2))) (p,w) tmp in
                (* sigma,[],[Special(ApproxProj(p,w))] *)
                sigma,[Special(ApproxProj(p,w),())],[]

            | ps_r,[Special(ApproxProj(p,w),_)] ->
                    (* if allow_right_approx *)
                    (* then *)
                    (*     let tmp = List.filter (function Proj _ | Special(ApproxProj _) -> true | _ -> false) ps_r in *)
                    (*     let tmp = List.map (function Proj(_,p) -> (p,Num 1) | Special(ApproxProj(p,w)) -> (p,w) | _ -> assert false) tmp in *)
                    (*     let p,w = List.fold_left (fun ap1 ap2 -> add_approx ap1 ap2) (p,op_weight w) tmp in *)
                    (*     sigma,[Special(ApproxProj(p,w))],[] *)
                    (* else raise (UnificationError "approximation on the right not allowed during unification") *)
                    raise (UnificationError "approximation on the right not allowed during unification")

            | Var(x_r,_)::ps_r,u_l::ps_l -> unify_aux (List.map (subst_approx_term [x_r,u_l]) ps_r) ps_l ((x_r,u_l)::(List.map (second (subst_approx_term [x_r,u_l])) sigma))
            | u_r::ps_r,Var(x_l,_)::ps_l -> unify_aux ps_r (List.map (subst_approx_term [x_l,u_r]) ps_l) ((x_l,u_r)::(List.map (second (subst_approx_term [x_l,u_r])) sigma))

            | ps_r,[] -> sigma,ps_r,[]
            | [],ps_l -> sigma,[],ps_l


            | Special(ApproxProj(p,w),_)::_,_
            | _,Special(ApproxProj(p,w),_)::_ -> assert false

            | _,_ -> raise (UnificationError ("cannot unify " ^ (string_of_list " " string_of_approx_term ps_r) ^ " and " ^ (string_of_list " " string_of_approx_term ps_l)))

    in

    unify_aux patterns_r patterns_l []


let compose (l1,r1:sct_clause) (l2,r2:sct_clause)
  : sct_clause
  =
    let l1,r1 = rename_var "₁" l1, rename_var "₁" r1 in
    let l2,r2 = rename_var "₂" l2, rename_var "₂" r2 in
    (* debug "  %s  o    %s" (string_of_sct_clause (l1,r1)) (string_of_sct_clause (l2,r2)); *)

    try
        let sigma,context1,context2 = unify r1 l2 in
(* debug "sigma: %s" (string_of_list " , " (function x,t -> x ^ ":=" ^ (string_of_approx_term t)) sigma); *)
(* debug "context1: %s" (string_of_list " , " string_of_approx_term context1); *)
(* debug "context2: %s" (string_of_list " , " string_of_approx_term context2); *)
        let l = subst_approx_term sigma l1 in
        let r = subst_approx_term sigma r2 in
(* debug "obtained %s" (string_of_sct_clause (l,r)); *)
        normalize_sct_clause (app_all l context2 , app_all r context1)
    with
        UnificationError err -> raise Impossible_case


let collapse_clause b d (l,r)
  = let l = collapse_pattern d l in
    let r = collapse_pattern d r in
    let l,r = normalize_sct_clause (l,r) in
    let r = collapse_weight_in_term b r in
    l,r


let collapsed_compose b d c1 c2
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
            | Special(ApproxConst apps1,_)::pats1,Special(ApproxConst apps2,_)::pats2 ->
                    List.for_all (function p2,w2,x2 ->
                    List.exists  (function p1,w1,x1 ->
                        (* debug "x1=%s, x2=%s, p1=%s, p2=%s, w1=%s, w2=%s" x1 x2 (string_of_priority p1) (string_of_priority p2) (string_of_weight w1) (string_of_weight w2); *)
                            x1=x2 && (p1 < p2 || (p1 = p2 && w1 >= w2))
                        )
                        apps1)
                        apps2
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
        let l1,r1 = rename_var "₁" l1, rename_var "₁" r1 in
        let l2,r2 = rename_var "₂" l2, rename_var "₂" r2 in
        let sigma,context1,context2 = unify l1 l2 in
        let r1 = subst_approx_term sigma r1 in
        let r1 = app_all r1 context1 in
        let r2 = subst_approx_term sigma r2 in
        let r2 = app_all r2 context2 in
        (* debug "r1=%s  and  r2=%s" (string_of_approx_term r1) (string_of_approx_term r2); *)

        let f1,pats1 = explode_pattern r1 in
        let f2,pats2 = explode_pattern r2 in
        f1 = f2 && approximates_aux pats1 pats2


    with UnificationError _ -> false


let rec repeat x n =
    if n = 0
    then []
    else x::(repeat x (n-1))

(* compatibility *)
(* similar to approximates *)
let compatible p1 p2 =

    let rec compatible_aux pats1 pats2 =
        (* debug "pats1 = %s" (string_of_list " , " string_of_approx_term pats1); *)
        (* debug "pats2 = %s" (string_of_list " , " string_of_approx_term pats2); *)
        match pats1,pats2 with
            | [],[] -> true
            | Proj(d1,_,_)::pats1,Proj(d2,_,_)::pats2 -> d1=d2 && compatible_aux pats1 pats2
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
        (* debug "check if %s is compatible with %s" (string_of_sct_clause p1) (string_of_sct_clause p2); *)
        let sigma,context1,context2 = unify (fst p1) (fst p2) in
        let r1 = subst_approx_term sigma (snd p1) in
        let r1 = app_all r1 context1 in
        let r2 = subst_approx_term sigma (snd p2) in
        let r2 = app_all r2 context2 in

        let f1,pats1 = explode_pattern r1 in
        let f2,pats2 = explode_pattern r2 in
        f1 = f2 && compatible_aux pats1 pats2


    with UnificationError _ -> false

(* decreasing arguments *)
let decreasing (l,r : sct_clause)
  : bool
  =
    let rec decreasing_aux pats1 pats2 acc
      = match pats1,pats2 with
            | [],[] -> (match acc with (Some p, Num w) when even p && w<0 -> true | _ -> false)

            | [],_ | _,[] -> raise (Invalid_argument "decreasing should only be called on idempotent rules")
                                (* FIXME: cannot it happen that we get f x => f x .D y *)

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

                        | Proj(d,p,_),[],Special(ApproxConst _,_),_ ->
                            begin
                                assert (pats2 = []);
                                let acc = add_approx acc (p,Num 1) in
                                let pats1 = List.filter (function (_,Proj _) -> true | _ -> false) pats1 in
                                let app = List.fold_left (fun r p -> match p with _,Proj(_,p,_) -> add_approx r (p,Num 1) | _ -> assert false) acc pats1 in
                                match app with
                                    | Some p, Num w when even p && w<0 -> true
                                    | _ -> false
                            end

                        | _,_,Special(ApproxConst _,_),_ -> assert false

                        | _,_,Angel _,_ -> true   (* FIXME: if the Angel isn't in a data, it should be "false" *)

                        | Angel _,_,_,_ -> assert false
                        | App _,_,_,_ | _,_,App _,_ -> assert false
                        | Special _,_,_,_ -> assert false

                        | _,_,_,_ -> debug "OOPS, u1=%s and u2=%s" (string_of_approx_term u1) (string_of_approx_term u2); assert false
                end
    in
    let rec remove_result_constants u =
        match get_head u, get_args u with
            | Special(ApproxProj _,_),[u]
            | Const _, [u] -> remove_result_constants u
            | _,_ -> u
    in
    match r with
        | App(Special(ApproxProj(Some p,Num w),_),_,_) when even p && w<0 -> true
        | r ->
                (* debug "check in %s and %s" (string_of_approx_term l) (string_of_approx_term (remove_result_constants r)); *)
                let f1,pats1 = explode_pattern l in
                let f2,pats2 = explode_pattern (remove_result_constants r) in
                assert (f1=f2);
                decreasing_aux (List.map (fun p -> (Some 0,Num 0),p) pats1) pats2 (Some 0, Num 0)


