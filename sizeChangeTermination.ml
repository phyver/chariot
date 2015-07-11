open Misc
open Base



(* let is_clause (lhs,rhs : sct_clause) : bool = *)

(*     let rec is_constructor_pattern angel approx p = *)
(*         match get_head p, get_args p with *)
(*         | Var _,[] -> true *)
(*         | Angel,[] -> angel *)
(*         | Const(_,_),ps -> List.for_all (is_constructor_pattern angel approx) ps *)
(*         | Special s,_ -> approx s *)
(*         | _,_ ->  false *)
(*     in *)

(*     let is_destructor approx p = match p with *)
(*         | Proj _ -> true *)
(*         | Special s -> approx s *)
(*         | _ -> false *)
(*     in *)

(*     let check_lhs = List.for_all *)
(*                         (fun p -> is_constructor_pattern false (fun _ -> false) p *)
(*                                || is_destructor (fun _ -> false) p) *)
(*                         lhs *)
(*     in *)
(*     let check_rhs = List.for_all *)
(*                         (fun p -> is_constructor_pattern true (function ApproxProj _ -> false | ApproxConst _ -> true) p *)
(*                                || is_destructor (function ApproxProj _ -> true | ApproxConst _ -> false) p) *)
(*                         rhs *)
(*     in *)
(*     check_lhs && check_rhs *)


let add_approx a1 a2 = match a1,a2 with
    | (None,w1) , (None,w2) -> (None, add_weight w1 w2)
    | (None,w) , _ | _,(None,w) -> (None, w)
    | (Some p1, w1) , (Some p2, w2) when p1<p2 -> (Some p2, w2)
    | (Some p1, w1) , (Some p2, w2) when p1>p2 -> (Some p1, w1)
    | (Some p1, w1) , (Some p2, w2) (*when p1=p2*) -> (Some p1, add_weight w1 w2)

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


let collapse_rhs depth (rhs:sct_rhs) : sct_rhs =

    let rec collapse0 p = match get_head p,get_args p with
        | Var x,[] -> [ (Some 0, Num 0, x) ]
        | Angel,[] -> assert false (* FIXME *)
        | Special (ApproxConst ap),[] -> ap
        | Const(_,prio),ps ->
            begin
                let approx_s = List.map collapse0 ps in
                let approx = List.fold_left (fun as1 as2 -> merge_approx as1 (simplify_approx as2)) [] approx_s in  (* NOTE: not necessary to simplify as1: it is the recursive call and is simplified *)
                List.map (function (p,w,x) -> let p,w = add_approx (prio,Num 1) (p,w) in (p,w,x)) approx
            end
        | Proj _,_ | Special (ApproxProj _),[] -> assert false
        | _,_ -> assert false
    in

    let rec collapse_const d p =
        match get_head p,get_args p with
            | Var _,[] | Angel,[] | Special (ApproxConst _),[] -> p
            | Proj _,_ | Special (ApproxProj _),_ -> assert false
            | Const(c,prio),ps ->
                if d=0
                then Special (ApproxConst (collapse0 p))
                else app (Const(c,prio)) (List.map (collapse_const (d-1)) ps)
            | _,_ -> assert false

    in

    let rec count_proj p = match get_head p, get_args p with
        | Var _,_ -> 0
        | Proj _,p::_ -> 1 + (count_proj p)
        | Special (ApproxProj _),p::_ -> 1 + (count_proj p)
        | _,_ -> assert false
    in

    let rec collapse_rhs_aux dp p = match get_head p, get_args p with
        | Proj _,[] -> assert false
        | Proj(_,prio), p::_ when dp>0->
            begin
                let p = collapse_rhs_aux (dp-1) p in
                match get_head p, get_args p with
                    | Special(ApproxProj(_prio,_w)),ps ->
                        let prio,w = add_approx (_prio,_w) (prio,Num 1) in
                        app (Special(ApproxProj(prio, w))) ps
                    | h,ps -> App(Special(ApproxProj(prio,Num 1)), app h ps)
            end
        | Proj(d,prio),p::ps (*when pd=0*) ->
                app (Proj(d,prio)) ((collapse_rhs_aux dp p)::List.map (collapse_const depth) ps)
        | Special (ApproxProj _),[] -> p
        | Special (ApproxProj _),_::_ -> assert false
        | Var f,ps -> app (Var f) (List.map (collapse_const depth) ps)
        | (Angel | Const _ | App _ | Special (ApproxConst _)),ps -> assert false
    in

    collapse_rhs_aux ((count_proj rhs)-depth) rhs


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


let collapse_arg (v:term)
 (* : (var_name * approx_term) list *)
 =
    let add priority = function
        | Special l -> Special (List.map (function w,p,x -> add_weight_int w 1, max p priority, x) l)
        | _ -> assert false
    in

    let rec collapse_arg_aux v = match get_head v,get_args v with
        | Const(c,Some p),args | Proj(c,Some p),args ->
            let sigma = List.concat (List.map collapse_arg_aux args) in
            List.map (second (add p)) sigma
        | Const(c,None),_ | Proj(c,None),_ -> error "missing priority from constant"
        | Var(x),[] -> [(x, Special [Num 0,0,x])]
        | Var(x),_ -> error "applications of variables shouldn't appear in SCT patterns"
        | Angel,_ -> error "⊤ shouldn't appear in pattern"
        | Special v,_ -> v.bot
        | App _,_ -> assert false
    in

    collapse_arg_aux v


(* let unify (pattern:term) (def:approx_term) *)
(*  : (var_name * approx_term) list * (var_name * term) list *)
(*  = *)
(*     let rec unify_aux (eqs:(term*approx_term) list) acc = *)
(*         match eqs with *)
(*             | [] -> acc *)
(*             | (s,t)::eqs when s=t -> unify_aux eqs acc *)
(*             | (App(u1,v1),App(u2,v2))::eqs -> unify_aux ((u1,u2)::(v1,v2)::eqs) acc *)
(*             | (Var _f, _)::_ when _f = f -> unificationError "cannot unify the function name" *)
(*             | (Var x, v)::eqs -> *)
(*                     let eqs = List.map (function u1,u2 -> (subst_term [x,v] u1, subst_term [x,v] u2)) eqs in *)
(*                     let acc = List.map (function _x,_u -> (_x, subst_term [x,v] _u)) acc in *)
(*                     unify_aux eqs ((x,v)::acc) *)
(*             | (Special v,_)::_ | (_,Special v)::_ -> v.bot *)
(*             | _ -> unificationError "cannot unify" *)

(*     in *)
(*     let sigma = unify_aux [pattern,v] [] in *)
(*     subst_term sigma def *)
