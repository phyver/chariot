open Misc
open Base
open Pretty
open Compute
open Typing

type explore_struct = Folded of int * term * type_expression | Unfolded of (const_name * explore_term) list
 and explore_term = explore_struct special_term

let rec
   print_explore_struct = function
       | Folded(n,v,t) -> print_string "…"; print_int n; print_string "…:"
       | Unfolded fields -> print_list "{}" "{" "; " "}" (function d,v -> print_string (d ^ "="); print_explore_term v) fields
and
  print_explore_term v = print_special_term print_explore_struct v

let rec head_to_explore (v:term) : explore_term = match v with
    | Angel -> Angel
    | Var x -> Var x
    | Proj(d,p) -> Proj(d,p)
    | Const(c,p) -> Const(c,p)
    | Special v -> v.bot
    | App(v1,v2) -> assert false

let struct_nb = ref 0

let rec term_to_explore (env:environment) (v:term) : explore_term
 =  let hd, args = get_head v, get_args v in
    match infer_type env v [] [] with
        | Data(tname,_) as t,_,_ ->
            if (is_inductive env tname)
            then
                app (head_to_explore hd) (List.map (term_to_explore env) args)
            else
                (incr struct_nb; Special (Folded (!struct_nb,v,t)))
        | Arrow _,_,_ | TVar _,_,_ ->
            app (head_to_explore hd) (List.map (term_to_explore env) args)
let term_to_explore env v = struct_nb:=0; term_to_explore env v


let rec unfold (env:environment) (p:int->bool) (v:explore_term) : explore_term
 =  match v with
        | Angel | Var _ | Proj _ | Const _ -> v
        | App(v1,v2) -> App(unfold env p v1, unfold env p v2)
        | Special(Unfolded fields) -> Special (Unfolded (List.map (second (unfold env p)) fields))
        | Special(Folded(n,v,t)) when not (p n) -> incr struct_nb; Special(Folded(!struct_nb,v,t))
        | Special(Folded(n,v,Data(tname,_))) when (p n) ->
                let p = get_type_priority env tname in
                let consts = get_type_constants env tname in
                let fields = List.map (fun d ->
                    let v = App(Proj(d,Some p),v) in
                    let v = reduce_all env v in
                    (d, term_to_explore env v)) consts
                in
                Special (Unfolded fields)
        | Special _ -> assert false

let unfold env p v = struct_nb:=0; unfold env p v

let rec unfold_to_depth env v depth
 =  if depth = 0
    then term_to_explore env v
    else
        let v = unfold_to_depth env v (depth-1) in
        unfold env (fun _ -> true) v

let explore_term_depth (env:environment) (v:term) (depth:int) : unit
  = print_explore_term (unfold_to_depth env v depth)

