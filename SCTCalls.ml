open Misc
open State
open Base
open Pretty


let explode_pattern pattern
  =
    let rec explode_aux pattern acc
      = match pattern with
            | (Var f) -> f,acc
            | App((Special (ApproxProj _) | Proj _) as proj ,u) -> explode_aux u (proj::acc)
            | App(u1,u2) -> explode_aux u1 (u2::acc)
            | _ -> assert false
    in
    explode_aux pattern []

let rec app_all u args =
    match args with
        | [] -> u
        | Proj(d,p)::args -> app_all (App( Proj(d,p) , u)) args
        | [Special(ApproxProj(p,w))] -> App( Special(ApproxProj(p,w)) , u )
        | Special(ApproxProj _)::_ -> assert false
        | arg::args -> app_all (App(u,arg)) args


(* collapsing the weights inside a term *)
let rec collapse_weight_in_term b u
  = match u with
        | Var _ | Const _ | Proj _ | Angel -> u
        | App(u1,u2) -> App(collapse_weight_in_term b u1, collapse_weight_in_term b u2)
        | Special(ApproxProj(p,w)) -> Special(ApproxProj(p, collapse_weight b w))
        | Special(ApproxConst apps) -> Special(ApproxConst(List.map (function p,w,x -> p, collapse_weight b w,x) apps))

(* misc operations on approximations *)
let add_approx a1 a2
  = match a1,a2 with
        | (None,w1) , (None,w2) -> (None, add_weight w1 w2)
        | (Some p1, w1) , (Some p2, w2) when p1<p2 -> (Some p2, w2)
        | (Some p1, w1) , (Some p2, w2) when p1>p2 -> (Some p1, w1)
        | (Some p1, w1) , (Some p2, w2) (*when p1=p2*) -> (Some p1, add_weight w1 w2)
        | (None,w1) , (Some _,w2) | (Some _,w1),(None,w2) -> if option "use_priorities" then warning "cannot add priorities and non-priorities, ignoring them"; (None, add_weight w1 w2)

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

let collapse_pattern (depth:int) (pattern:approx_term) : approx_term
  =
    (* count the number of destructors in a definition pattern *)
    let rec count_proj p = match get_head p, get_args p with
        | Var _,_ -> 0
        | Proj _,p::_ -> 1 + (count_proj p)
        | Special (ApproxProj _),p::_ -> 1 + (count_proj p)
        | _,_ -> assert false
    in

    (* collapse the constructors at given depth from a constructor pattern with approximations *)
    let rec collapse_const d p =
        match get_head p,get_args p with
            | Var _,[] | Angel,[] | Special (ApproxConst _),[] -> p
            | Const(c,prio),ps ->
                if d=0
                then Special (ApproxConst (collapse0 p))
                else app (Const(c,prio)) (List.map (collapse_const (d-1)) ps)
            | _,_ -> assert false

    in

    (* collapse the pattern of a definition at a given depth *)
    let rec collapse dp p = match get_head p, get_args p with
        | Proj _,[] -> assert false
        | Proj(_,prio), p::_ when dp>0->
            begin
                let p = collapse (dp-1) p in
                match get_head p, get_args p with
                    | Special(ApproxProj(_prio,_w)),ps ->
                        let prio,w = add_approx (_prio,_w) (prio,Num 1) in
                        app (Special(ApproxProj(prio, w))) ps
                    | h,ps -> App(Special(ApproxProj(prio,Num 1)), app h ps)
            end
        | Proj(d,prio),p::ps (*when pd=0*) ->
                app (Proj(d,prio)) ((collapse dp p)::List.map (collapse_const depth) ps)
        | Special (ApproxProj(prio,w)),[p] -> App( Special(ApproxProj(prio,w)) , collapse dp p)
        | Special (ApproxProj _),_ -> assert false
        | Var f,ps -> app (Var f) (List.map (collapse_const depth) ps)
        | (Angel | Const _ | App _ | Special (ApproxConst _)),ps -> assert false
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
                merge_approx apps2 (apps@acc)
            with Not_found -> subst_approx_term_aux sigma (a::acc) apps

let rec subst_approx_term sigma v
  = match v with
        | Var x -> (try List.assoc x sigma with Not_found -> Var x)
        | (Angel|Const _|Proj _|Special(ApproxProj _)) as v -> v
        | App(v1,v2) -> App(subst_approx_term sigma v1, subst_approx_term sigma v2)
        | Special(ApproxConst apps) -> Special(ApproxConst (subst_approx_term_aux sigma [] apps))


(* normalize a clause by moving all the approximations from the LHS to the RHS:
 *    A  (<1>x+<2>y) z  =>  B  x y z
 * is transformed into
 *    A  a  b  =>  B  <-1>a  <-2> a b
 *)

let normalize_sct_clause (lhs,rhs : sct_clause)
  : sct_clause
  =
    (* TODO: rename dangling variables on the RHS to "!x" *)

    (* debug "normalizing %s" (string_of_sct_clause (lhs,rhs)); *)
    let n = ref 0
    in

    let new_var () = incr n; "x"^sub_of_int !n
    in

    let add_approx_res app res =
        match app, res with
            | Some(prio,w), App (Special(ApproxProj(_prio,_w)), res) ->
                let prio,w = add_approx (_prio,_w) (prio,w) in
                App (Special(ApproxProj(prio,w)),res)
            | Some(prio,w), res ->
                App (Special(ApproxProj(prio,w)),res)
            | None, res -> res
    in

    let rec process_pattern p =
        match get_head p, get_args p with
            | Var x,[] -> let y = new_var() in (Var y, [x,Var y])
            | Const(c,p), args ->
                let tmp = List.map process_pattern args in
                let sigma = List.concat (List.map snd tmp) in
                let args = List.map fst tmp in
                (app (Const(c,p)) args , sigma)
            | Special(ApproxConst apps),[] ->
                let x = new_var() in
                (Var x, List.map (function (p,w,y) -> (y,Special(ApproxConst [p, op_weight w,x]))) apps)
            | _ -> assert false
    in

    let rec process_lhs lhs =
        match get_head lhs, get_args lhs with
            | Var f,args ->
                let tmp = List.map process_pattern args in
                let sigma = List.concat (List.map snd tmp) in
                let args = List.map fst tmp in
                (None, app (Var f) args, sigma)
            | Proj(d,p),lhs::args ->
                begin
                    match process_lhs lhs with
                        | None, lhs, tau ->
                            let tmp = List.map process_pattern args in
                            let sigma = List.concat (List.map snd tmp) in
                            let args = List.map fst tmp in
                            (None, app (Proj(d,p)) (lhs::args), tau@sigma)
                        | _ -> assert false
                end
            | Special(ApproxProj(p,w)),[lhs] ->
                begin
                    match process_lhs lhs with
                        | None, lhs, sigma -> Some (p, op_weight w) , lhs, sigma
                        | _ -> assert false

                end
            | _,_ -> assert false
    in

    let app_res, lhs, sigma = process_lhs lhs
    in

    let rhs = add_approx_res app_res (subst_approx_term sigma rhs)
    in

      (* debug "obtained %s" (string_of_sct_clause (lhs,rhs)) *)
    lhs,rhs


let rec rename_var_aux x v
    = match v with
        | Var y -> Var (y^x)
        | App(v1,v2) -> App(rename_var_aux x v1, rename_var_aux x v2)
        | Const _ | Proj _ | Angel -> v
        | Special(ApproxConst apps) -> Special(ApproxConst (List.map (function p,w,y -> p,w,y^x) apps))
        | _ -> assert false

let rec rename_var x v
  = match get_head v,get_args v with
        | Var f,args -> app (Var f) (List.map (rename_var_aux x) args)
        | Proj(d,p),v::args -> app (Proj(d,p)) ((rename_var x v)::(List.map (rename_var_aux x) args))
        | Special(ApproxProj(p,w)),[v] -> App(Special(ApproxProj(p,w)), rename_var x v)
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

            | App(u_r,v_r)::ps_r,App(u_l,v_l)::ps_l -> unify_aux (u_r::v_r::ps_r) (u_l::v_l::ps_l) sigma

            | Special(ApproxConst apps_r)::ps_r,u_l::ps_l ->
                let apps_l = collapse0 u_l in
                let tau = List.map (function p,w,x -> (x,Special(ApproxConst(List.map (function _p,_w,_x -> let p,w = add_approx (_p,_w) (p, op_weight w) in p,w,_x) apps_r))) ) apps_l in
                unify_aux ps_r ps_l (tau @ (List.map (second (subst_approx_term sigma)) sigma))

            | u_r::ps_r,Special(ApproxConst apps_l)::ps_l ->
                    if allow_right_approx
                    then
                        let apps_r = collapse0 u_r in
                        let tau = List.map (function p,w,x -> (x,Special(ApproxConst(List.map (function _p,_w,_x -> let p,w = add_approx (_p,_w) (p, op_weight w) in p,w,_x) apps_l))) ) apps_r in
                        unify_aux ps_r ps_l (tau @ (List.map (second (subst_approx_term sigma)) sigma))
                    else raise (UnificationError "approximation on the right not allowed during unification")

            | [Special(ApproxProj(p,w))],ps_l ->
                let tmp = List.filter (function Proj _ | Special(ApproxProj _) -> true | _ -> false) ps_l in
                let tmp = List.map (function Proj(_,p) -> (p,Num 1) | Special(ApproxProj(p,w)) -> (p,w) | _ -> assert false) tmp in
                let p,w = List.fold_left (fun ap1 ap2 -> add_approx ap1 ap2) (p,op_weight w) tmp in
                sigma,[],[Special(ApproxProj(p,w))]

            | ps_r,[Special(ApproxProj(p,w))] ->
                    if allow_right_approx
                    then
                        let tmp = List.filter (function Proj _ | Special(ApproxProj _) -> true | _ -> false) ps_r in
                        let tmp = List.map (function Proj(_,p) -> (p,Num 1) | Special(ApproxProj(p,w)) -> (p,w) | _ -> assert false) tmp in
                        let p,w = List.fold_left (fun ap1 ap2 -> add_approx ap1 ap2) (p,op_weight w) tmp in
                        sigma,[Special(ApproxProj(p,w))],[]
                    else raise (UnificationError "approximation on the right not allowed during unification")

            | Var(x_r)::ps_r,u_l::ps_l -> unify_aux (List.map (subst_approx_term [x_r,u_l]) ps_r) ps_l ((x_r,u_l)::(List.map (second (subst_approx_term [x_r,u_l])) sigma))
            | u_r::ps_r,Var(x_l)::ps_l -> unify_aux ps_r (List.map (subst_approx_term [x_l,u_r]) ps_l) ((x_l,u_r)::(List.map (second (subst_approx_term [x_l,u_r])) sigma))

            | ps_r,[] -> sigma,ps_r,[]
            | [],ps_l -> sigma,[],ps_l


            | Special(ApproxProj(p,w))::_,_
            | _,Special(ApproxProj(p,w))::_ -> assert false

            | _,_ -> raise (UnificationError ("cannot unify " ^ (string_of_list " " string_of_approx_term ps_r) ^ " and " ^ (string_of_list " " string_of_approx_term ps_l)))

    in

    unify_aux patterns_r patterns_l []


let compose (l1,r1:sct_clause) (l2,r2:sct_clause)
  : sct_clause
  =
    let l1,r1 = rename_var "₁" l1, rename_var "₁" r1 in
    let l2,r2 = rename_var "₂" l2, rename_var "₂" r2 in
(* debug "  %s  o    %s" (string_of_sct_clause (l1,r1)) (string_of_sct_clause (l2,r2)) *)

    try
        let sigma,context1,context2 = unify r1 l2 in
(* debug "sigma: %s" (string_of_list " , " (function x,t -> x ^ ":=" ^ (string_of_approx_term t)) sigma); *)
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
  = let l,r = compose c1 c2 in
    let result = collapse_clause b d (l,r)
    in
    (* debug "composing:  %s   and   %s" (string_of_sct_clause c1) (string_of_sct_clause c2); *)
    (* debug "   result:  %s " (string_of_sct_clause result); *)
    result



(* order *)
let approximates p1 p2 =

    let rec approximates_aux pats1 pats2 =
        (* debug "pats1 = %s" (string_of_list " , " string_of_approx_term pats1); *)
        (* debug "pats2 = %s" (string_of_list " , " string_of_approx_term pats2); *)
        match pats1,pats2 with
            | [],[] -> true
            | Proj(d1,_)::pats1,Proj(d2,_)::pats2 -> d1=d2 && approximates_aux pats1 pats2
            | Var x1::pats1,Var x2::pats2 -> x1=x2 && approximates_aux pats1 pats2
            | Const(c1,_)::pats1,Const(c2,_)::pats2 -> c1=c2 && approximates_aux pats1 pats2
            | ((App _) as u1)::_pats1,((App _) as u2)::_pats2 ->
                    approximates_aux ((get_head u1)::(get_args u1)@_pats1) ((get_head u2)::(get_args u2)@_pats2)
            | Special(ApproxConst apps1)::pats1,Special(ApproxConst apps2)::pats2 ->
                    List.for_all (function p2,w2,x2 ->
                    List.exists  (function p1,w1,x1 ->
                        (* debug "x1=%s, x2=%s, p1=%s, p2=%s, w1=%s, w2=%s" x1 x2 (string_of_priority p1) (string_of_priority p2) (string_of_weight w1) (string_of_weight w2); *)
                            x1=x2 && (p1 < p2 || (p1 = p2 && w1 >= w2))
                        )
                        apps1)
                        apps2
            | Special(ApproxConst _)::_,u2::_pats2 ->
                    let aps2 = collapse0 u2 in
                    approximates_aux pats1 (Special(ApproxConst aps2)::_pats2)
            | [Special(ApproxProj(p,w))],pats2 ->
                    begin
                        let projs = List.filter (function Special(ApproxProj _) -> true | _ -> false) pats2 in
                        let _,w = List.fold_left (fun r a2 ->
                                        match a2 with Special(ApproxProj(_p,_w)) -> add_approx r (_p,_w)
                                                    | _ -> assert false
                                    )
                                    (p,op_weight w)
                                    projs
                        in
                        match w with Infty -> false
                                   | Num w -> w <= 0
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
        (* msg "r1=%s  and  r2=%s" (string_of_approx_term r1) (string_of_approx_term r2); *)

        let f1,pats1 = explode_pattern r1 in
        let f2,pats2 = explode_pattern r2 in
        f1 = f2 && approximates_aux pats1 pats2


    with UnificationError _ -> false


(* compatibility *)
(* similar to approximates *)
let compatible p1 p2 =

    let rec compatible_aux pats1 pats2 =
        (* debug "pats1 = %s" (string_of_list " , " string_of_approx_term pats1); *)
        (* debug "pats2 = %s" (string_of_list " , " string_of_approx_term pats2); *)
        match pats1,pats2 with
            | [],[] -> true
            | Proj(d1,_)::pats1,Proj(d2,_)::pats2 -> d1=d2 && compatible_aux pats1 pats2
            | Var x1::pats1,Var x2::pats2 -> x1=x2 && compatible_aux pats1 pats2
            | Const(c1,_)::pats1,Const(c2,_)::pats2 -> c1=c2 && compatible_aux pats1 pats2
            | ((App _) as u1)::_pats1,((App _) as u2)::_pats2 ->
                    compatible_aux ((get_head u1)::(get_args u1)@_pats1) ((get_head u2)::(get_args u2)@_pats2)
            | Special(ApproxConst apps1)::pats1,Special(ApproxConst apps2)::pats2 ->
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
            | Special(ApproxConst _)::_,u2::_pats2 ->
                    let aps2 = collapse0 u2 in
                    compatible_aux pats1 (Special(ApproxConst aps2)::_pats2)
            | u1::_pats1,Special(ApproxConst _)::_ ->
                    let aps1 = collapse0 u1 in
                    compatible_aux (Special(ApproxConst aps1)::_pats1) pats2

            (* FIXME: is that right? *)
            | [Special(ApproxProj _)],_
            | _,[Special(ApproxProj _)] ->
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
    let rec repeat x n =
        if n = 0
        then []
        else x::(repeat x (n-1))
    in

    let rec decreasing_aux pats1 pats2 acc
      = match pats1,pats2 with
            | [],[] -> (match acc with (Some p, Num w) when even p && w<0 -> true | _ -> false)

            | [],_ | _,[] -> raise (Invalid_argument "decreasing should only be called on idempotent rules")
            | (app1,u1)::pats1, u2::pats2 ->
                begin
                    match get_head u1, get_args u1, get_head u2, get_args u2 with

                        | Proj(d1,p1),[],Proj(d2,p2),[] ->
                            assert (d1=d2);
                            assert (p1=p2);
                            decreasing_aux pats1 pats2 (add_approx (p1,Num 0) acc)

                        | Proj _,_,Proj _,_ -> assert false

                        | Var x1,[],Var x2,[] ->
                            decreasing_aux pats1 pats2 acc

                        | Var _,_,Var _,_ -> assert false

                        | Const(c1,p1),args1,Const(c2,p2),args2 ->
                            assert (c1=c2);
                            assert (p1=p2);
                            let app = add_approx app1 (p1,Num 0) in
                            let args1 = List.map (fun x -> app,x) args1 in
                            decreasing_aux (args1@pats1) (args2@pats2) acc

                        | Var x,[],Special(ApproxConst apps),[] ->
                            begin
                                match apps with
                                    | [(p,w,y)] when y=x ->
                                        (match add_approx app1 (p,w) with
                                            | Some p,Num w when odd p && w<0 -> true
                                            | _, _ -> decreasing_aux pats1 pats2 acc)
                                    | _ -> decreasing_aux pats1 pats2 acc
                            end

                        | Const(c1,p),args1,((Special(ApproxConst apps)) as u2),[] ->
                            let app = add_approx app1 (p,Num 1) in
                            let args1 = List.map (fun x -> app,x) args1 in
                            let args2 = repeat u2 (List.length args1) in
                            decreasing_aux (args1@pats1) (args2@pats2) acc

                        | Proj(d,p),[],Special(ApproxConst _),_ ->
                            begin
                                assert (pats2 = []);
                                let acc = add_approx acc (p,Num 1) in
                                let pats1 = List.filter (function (_,Proj _) -> true | _ -> false) pats1 in
                                let app = List.fold_left (fun r p -> match p with _,Proj(_,p) -> add_approx r (p,Num 1) | _ -> assert false) acc pats1 in
                                match app with
                                    | Some p, Num w when even p && w<0 -> true
                                    | _ -> false
                            end

                        | _,_,Special(ApproxConst _),_ -> assert false

                        | _,_,Angel,_ -> true   (* FIXME: if the Angel isn't in a data, it should be "false" *)

                        | Angel,_,_,_ -> assert false
                        | App _,_,_,_ | _,_,App _,_ -> assert false
                        | Special _,_,_,_ -> assert false

                        | _,_,_,_ -> assert false
                end
    in decreasing_aux [(Some 0,Num 0),l] [r] (Some 0, Num 0)


