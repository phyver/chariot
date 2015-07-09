open Misc
open Base

type z_infty = Num of int | Infty

let add_infty w1 w2 = match w1,w2 with
    | Infty,_ | _,Infty -> Infty
    | Num a,Num b -> Num (a+b)

let add_infty_int w n = add_infty w (Num n)

type sct_pattern =
    | SCTVar of var_name
    | SCTAngel

    | SCTConst of const_name * priority * sct_pattern list
    | SCTConstApprox of (priority * z_infty * var_name) list

    | SCTProj of const_name * priority
    | SCTProjApprox of priority * z_infty

(* a call from f to g is represented by a rewriting rule
 *   param_1 param_2 ... param_m  =>  arg_1 arg_2 ... arg_n
 * where m is the arity of f and n is the arity of g.
 *  - each param_i is either a constructor pattern or a destructor
 *  - each arg_i i either a constructor pattern (with possible approximations) or a destructor
 *)
type sct_lhs = sct_pattern list
type sct_rhs = sct_pattern list
type sct_clause = sct_lhs * sct_rhs


let is_clause (lhs,rhs : sct_clause) : bool =
    let rec is_constructor_pattern a s = function
        | SCTVar _ -> true
        | SCTAngel -> a
        | SCTConst(_,_,ps) -> List.for_all (is_constructor_pattern a s) ps
        | SCTConstApprox _ -> s
        | SCTProj _ -> false
        | SCTProjApprox _ -> false
    in
    let is_destructor = function
        | SCTProj _ -> true
        | SCTProjApprox _ -> true
        | _ -> false
    in
    let check_lhs = List.for_all (fun p -> is_constructor_pattern false false p || is_destructor p)
    in
    let check_rhs = List.for_all (fun p -> is_constructor_pattern true true p || is_destructor p)
    in
    check_lhs lhs && check_rhs rhs


let add_approx a1 a2 = match a1,a2 with
    | (None,w1) , (None,w2) -> (None, add_infty w1 w2)
    | (None,w) , _ | _,(None,w) -> (None, w)
    | (Some p1, w1) , (Some p2, w2) when p1<p2 -> (Some p2, w2)
    | (Some p1, w1) , (Some p2, w2) when p1>p2 -> (Some p1, w1)
    | (Some p1, w1) , (Some p2, w2) (*when p1=p2*) -> (Some p1, add_infty w1 w2)

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
    let rec collapse0 p = match p with
        | SCTVar x -> [ (Some 0, Num 0, x) ]
        | SCTAngel -> assert false (* FIXME *)
        | SCTConstApprox ap -> ap
        | SCTProj _ | SCTProjApprox _ -> assert false
        | SCTConst(_,prio,ps) ->
            begin
                let approx_s = List.map collapse0 ps in
                let approx = List.fold_left (fun as1 as2 -> merge_approx as1 (simplify_approx as2)) [] approx_s in  (* NOTE: not necessary to simplify as1: it is the recursive call and is simplified *)
                List.map (function (p,w,x) -> let p,w = add_approx (prio,Num 1) (p,w) in (p,w,x)) approx
            end
    in
    let rec collapse_const d p =
        if d=0
        then SCTConstApprox (collapse0 p)
        else
            match p with
        | SCTVar _ | SCTAngel | SCTConstApprox _ -> p
        | SCTProj _ | SCTProjApprox _ -> assert false
        | SCTConst(c,p,ps) -> SCTConst(c,p,List.map (collapse_const (d-1)) ps)
    in
    let rec collapse_rhs_aux depth ps = match ps with
        | [] -> []
        | SCTProj(p,d)::ps ->
            if depth = 0
            then assert false (* TODO...*)
            else
                SCTProj(p,d)::(collapse_rhs_aux (depth-1) ps)
        | [SCTProjApprox _ ] -> ps
        | (SCTProjApprox _)::_ -> assert false
        | (SCTVar _ | SCTAngel | SCTConst _ | SCTConstApprox _) as p::ps -> (collapse_const depth p)::(collapse_rhs_aux depth ps)
    in
    collapse_rhs_aux depth rhs


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
        | Special l -> Special (List.map (function w,p,x -> add_infty_int w 1, max p priority, x) l)
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
