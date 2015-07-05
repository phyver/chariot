open Misc
open Base

type z_infty = Num of int | Infty

let add_infty w1 w2 = match w1,w2 with
    | Infty,_ | _,Infty -> Infty
    | Num a,Num b -> Num (a+b)

let add_infty_int w n = add_infty w (Num n)

type approx_term = (z_infty * priority * var_name) list special_term

type sct_clause = term * approx_term



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
