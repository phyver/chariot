open Misc
open Base
open Pretty
open Compute
open Typing

type explore_struct = Folded of int * term * type_expression | Unfolded of (const_name * explore_term) list
 and explore_term = explore_struct special_term

let rec
   print_explore_struct = function
       | Folded(n,v,t) -> print_string "…"; print_int n; print_string "…:"; print_type t
       | Unfolded fields -> print_list "{}" "{" "; " "}" (function d,v -> print_string (d ^ "="); print_explore_term v) fields
and
  print_explore_term v = print_special_term print_explore_struct v

let rec term_to_explore (v:term) : explore_term = match v with
    | Angel -> Angel
    | Var x -> Var x
    | Proj(d,p) -> Proj(d,p)
    | Const(c,p) -> Const(c,p)
    | App(v1,v2) -> App(term_to_explore v1,term_to_explore v2)
    | Special v -> v.bot

let unfold (env:environment) (v:term) (depth:int) : explore_term
 =
    let rec unfold_aux depth (v:term) : explore_term =
        let hd, args = get_head v, get_args v in
        match infer_type env v [] [] with
            | Arrow _,_,_ | TVar _,_,_ -> app (term_to_explore hd) (List.map (unfold_aux depth) args)
            | Data(tname,_) as t,_,_ ->
                let p = get_type_priority env tname in
                if p mod 2 = 1
                then app (term_to_explore hd) (List.map (unfold_aux depth) args)
                else
                    if depth = 0
                    then Special (Folded (0,app hd args,t))
                    else
                        let consts = get_type_constants env tname in
                        let fields = List.map (fun d ->
                            let t = App(Proj(d,Some p),v) in
                            let nf = unfold_aux (depth-1) (reduce_all env t) in
                            (d, nf)) consts
                        in
                        Special (Unfolded fields)

    in unfold_aux depth (reduce_all env v)


let explore_term_depth (env:environment) (v:term) (depth:int) : unit
  = print_explore_term (unfold env v depth)

