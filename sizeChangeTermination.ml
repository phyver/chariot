open Misc
open Base
open Pretty

(* collapsing the weights inside a term *)
let rec collapse_weight_in_term b u
  = match u with
        | Var _ | Const _ | Proj _ | Angel -> u
        | App(u1,u2) -> App(collapse_weight_in_term b u1, collapse_weight_in_term b u2)
        | Special(ApproxProj(p,w)) -> Special(ApproxProj(p, collapse_weight b w))
        | Special(ApproxConst apps) -> Special(ApproxConst(List.map (function p,w,x -> p, collapse_weight b w,x) apps))

(* misc operations on approximations *)
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
        | Special (ApproxProj _),[] -> p
        | Special (ApproxProj _),_::_ -> assert false
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
      (* debug "normalizing %s => %s" (string_of_approx_term lhs) (string_of_approx_term rhs); *)
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

      (* debug "obtained %s => %s" (string_of_approx_term lhs) (string_of_approx_term rhs); *)
    lhs,rhs


let rec rename_var_aux x v
    = match v with
        | Var y -> Var (y^x)
        | App(v1,v2) -> App(rename_var_aux x v1, rename_var_aux x v2)
        | Const _ | Proj _ | Angel -> v
        | Special(ApproxConst apps) -> Special(ApproxConst (List.map (function p,w,y -> p,w,x^y) apps))
        | _ -> assert false

let rec rename_var x v
  = match get_head v,get_args v with
        | Var f,args -> app (Var f) (List.map (rename_var_aux x) args)
        | Proj(d,p),v::args -> app (Proj(d,p)) ((rename_var x v)::(List.map (rename_var_aux x) args))
        | Special(ApproxProj(p,w)),[v] -> App(Special(ApproxProj(p,w)), rename_var x v)
        | _ -> assert false




(* unify the rhs of a clause with the lhs of another *)
let unify (rhs:approx_term) (lhs:approx_term)
  :   (var_name * approx_term) list     (* the substitution concerning variables in rhs *)
    * (var_name * approx_term) list     (* the substitution concerning variables in lhs *)
    * approx_term list                  (* the arguments that were in lhs but not in rhs *)
    * approx_term list                  (* the arguments that were in rhs but not in lhs *)  (* NOTE: at most one of those lists is non-empty *)
  =

    let rec explode_pattern pattern acc
      = match pattern with
            | (Var f) -> f,acc
            | App((Special (ApproxProj _) | Proj _) as proj ,u) -> explode_pattern u (proj::acc)
            | App(u1,u2) -> explode_pattern u1 (u2::acc)
            | _ -> assert false
    in

    let f_r,patterns_r = explode_pattern rhs [] in
    let f_l,patterns_l = explode_pattern lhs [] in
    assert (f_r = f_l);

    let rec unify_aux (ps_r:approx_term list) (ps_l:approx_term list)
                      (sigma_r:(var_name*approx_term) list) (sigma_l:(var_name*approx_term) list)
      : (var_name*approx_term) list *  (var_name*approx_term) list * approx_term list * approx_term list
      = match ps_r,ps_l with
            | [],[] -> sigma_r,sigma_l,[],[]

            | u_r::ps_r,u_l::ps_l when u_r=u_l -> unify_aux ps_r ps_l sigma_r sigma_l

            | App(u_r,v_r)::ps_r,App(u_l,v_l)::ps_l -> unify_aux (u_r::v_r::ps_r) (u_l::v_l::ps_l) sigma_r sigma_l

            | u_r::ps_r,Var(x_l)::ps_l -> unify_aux ps_r (List.map (subst_approx_term [x_l,u_r]) ps_l) sigma_r ((x_l,u_r)::(List.map (second (subst_approx_term [x_l,u_r])) sigma_l))
            | Var(x_r)::ps_r,u_l::ps_l -> unify_aux (List.map (subst_approx_term [x_r,u_l]) ps_r) ps_l ((x_r,u_l)::(List.map (second (subst_approx_term [x_r,u_l])) sigma_r)) sigma_l

            | Special(ApproxConst apps_r)::ps_r,u_l::ps_l ->
                let apps_l = collapse0 u_l in
                let sigma = List.map (function p,w,x -> (x,Special(ApproxConst(List.map (function _p,_w,_x -> let p,w = add_approx (_p,_w) (p, op_weight w) in p,w,_x) apps_r))) ) apps_l in
                unify_aux ps_r ps_l sigma_r (sigma @ (List.map (second (subst_approx_term sigma)) sigma_l))

            | [Special(ApproxProj(p,w))],ps_l ->
                let tmp = List.filter (function Proj _ | Special(ApproxProj _) -> true | _ -> false) ps_l in
                let tmp = List.map (function Proj(_,p) -> (p,Num 1) | Special(ApproxProj(p,w)) -> (p,w) | _ -> assert false) tmp in
                let p,w = List.fold_left (fun ap1 ap2 -> add_approx ap1 ap2) (p,op_weight w) tmp in
                sigma_r,sigma_l,[],[Special(ApproxProj(p,w))]

            | ps_r,[] -> sigma_r,sigma_l,ps_r,[]
            | [],ps_l -> sigma_r,sigma_l,[],ps_l

            | ps_r,[Special(ApproxProj(p,w))] -> assert false
            | u_r::ps_r,Special(ApproxConst apps_l)::ps_l -> assert false

            | Special(ApproxProj(p,w))::_,_
            | _,Special(ApproxProj(p,w))::_ -> assert false

            | _,_ -> raise (UnificationError ("cannot unify " ^ (string_of_list " " string_of_approx_term ps_r) ^ " and " ^ (string_of_list " " string_of_approx_term ps_l)))

    in

    unify_aux patterns_r patterns_l [] []

let compose (l1,r1:sct_clause) (l2,r2:sct_clause)
  : sct_clause
  =
    let rec app_all u args =
        match args with
            | [] -> u
            | Proj(d,p)::args -> app_all (App( Proj(d,p) , u)) args
            | [Special(ApproxProj(p,w))] -> App( Special(ApproxProj(p,w)) , u )
            | Special(ApproxProj _)::_ -> assert false
            | arg::args -> app_all (App(u,arg)) args
    in

    let l1,r1 = rename_var "₁" l1, rename_var "₁" r1 in
    let l2,r2 = rename_var "₂" l2, rename_var "₂" r2 in

    try
        let sigma1,sigma2,context1,context2 = unify r1 l2 in
debug "sigma1: %s" (string_of_list " , " (function x,t -> x ^ ":=" ^ (string_of_approx_term t)) sigma1);
debug "sigma2: %s" (string_of_list " , " (function x,t -> x ^ ":=" ^ (string_of_approx_term t)) sigma2);
        let l = subst_approx_term sigma1 l1 in
        let r = subst_approx_term sigma2 r2 in
(* debug "obtained %s => %s" (string_of_approx_term l) (string_of_approx_term r); *)
        normalize_sct_clause (app_all l context2 , app_all r context1)
    with
        UnificationError err -> error ("impossible composition: " ^ err)

let collapsed_compose b d c1 c2
  = let l,r = compose c1 c2 in
    let l = collapse_pattern d l in
    let r = collapse_pattern d r in
    let l,r = normalize_sct_clause (l,r) in
    let l = collapse_weight_in_term b l in
    let r = collapse_weight_in_term b r in
    l,r
    







