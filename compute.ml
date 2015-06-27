open Base
open Pretty
open Misc

let rec subst_term sigma (v:term) = match v with
    | Var(x) -> (try List.assoc x sigma with Not_found -> Var(x))
    | Angel | Const _ | Proj _ -> v
    | App(v1,v2) -> App(subst_term sigma v1, subst_term sigma v2)
    | Special v -> v.bot

let rec equal_term v1 v2 = match v1,v2 with
    | Var(x),Var(y) -> x=y
    | Angel,Angel -> true
    | App(v11,v12),App(v21,v22) -> (equal_term v11 v21) && (equal_term v12 v22)
    | Proj(d1,_),Proj(d2,_) -> d1=d2
    | Const(c1,_),Const(c2,_) -> c1=c2
    | _,_ -> false

let unify_pattern (pattern,def:term*term) (v:term) : term
  = (* the function defined by the pattern: this variable cannot be instantiated! *)
    let f = get_function_name pattern in

    let rec unify_aux (eqs:(term*term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when equal_term s t -> unify_aux eqs acc
            | (App(u1,v1),App(u2,v2))::eqs -> unify_aux ((u1,u2)::(v1,v2)::eqs) acc
            | (Var _f, _)::_ when _f = f -> unificationError "cannot unify the function name"
            | (Var x, v)::eqs ->
                    let eqs = List.map (function u1,u2 -> (subst_term [x,v] u1, subst_term [x,v] u2)) eqs in
                    let acc = List.map (function _x,_u -> (_x, subst_term [x,v] _u)) acc in
                    unify_aux eqs ((x,v)::acc)
            | (Special v,_)::_ | (_,Special v)::_ -> v.bot
            | _ -> unificationError "cannot unify"

    in
    let sigma = unify_aux [pattern,v] [] in
    subst_term sigma def

(* NOTE: very inefficient *)
let reduce_all (env:environment) (v:term) : term
  =
    (* look for the first clause that can be used to reduce u
     * the boolean in the result indicates if a reduction was made *)
    let rec reduce_first_clause (v:term) clauses : term*bool =
        match clauses with
            | [] -> v,false
            | clause::clauses ->
                begin
                    try
                        let new_term = unify_pattern clause v in
                        new_term,true
                    with UnificationError _ -> reduce_first_clause v clauses
                end
    and
      reduce v = match v with
          | Var(f) -> (try reduce_first_clause v (get_function_clauses env f) with Not_found -> v,false)
          | Const _ | Angel | Proj _ -> v,false
          | App(v1,v2) -> 
                let v1,b1 = reduce v1 in
                let v2,b2 = reduce v2 in
                let v3,b3 = (try reduce_first_clause (App(v1,v2)) (get_function_clauses env (get_function_name v))
                             with Invalid_argument "no head function" | Not_found -> App(v1,v2),b1||b2) in
                v3, b1||b2||b3
          | Special v -> v.bot
    in

    let rec aux v =
      let v,b = reduce v in
      if b then aux v else v
    in

    aux v
