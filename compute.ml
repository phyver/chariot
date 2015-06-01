open Base
open Pretty

let rec subst_term (u:term) (sigma:(var_name*term) list) : term
  = match u with
        | Var(x) -> (try List.assoc x sigma with Not_found -> u)
        | Constant _ -> u
        | Daimon -> u
        | Apply(u1,u2) -> Apply(subst_term u1 sigma, subst_term u2 sigma)


(* the argument f represents the function defined by the pattern: this variable cannot be instantiated! *)
let unify_pattern (pattern:term) (u:term) (f:var_name): (var_name*term) list
  = let rec unify_aux (eqs:(term*term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> unify_aux eqs acc
            | (Constant(c1),Constant(c2))::eqs when c1=c2 -> acc
            | (Constant(c1), Constant(c2))::_ -> error ("cannot unify constants " ^ c1 ^ " and " ^ c2)
            | (Constant _, _)::_ -> error "cannot unify constant and non-constant"
            | (Apply(u1,u2),Apply(v1,v2))::eqs -> unify_aux ((u1,v1)::(u2,v2)::eqs) acc
            | (Apply _, _)::_ -> error "cannot unify application with non-application"
            | (Var x, _)::_ when x = f -> error "cannot unify the function name"
            | (Var x, u)::eqs ->
                    let eqs = List.map (function u1,u2 -> (subst_term u1 [x,u], subst_term u2 [x,u])) eqs in
                    let acc = List.map (function _x,_u -> (_x, subst_term _u [x,u])) acc in
                    unify_aux eqs ((x,u)::acc)
            | (Daimon,_)::_ -> error "cannot unify daimon"
    in unify_aux [pattern,u] []


let reduce_all (env:environment) (u:term) : term
  = let clauses = List.concat (List.map (function (f,_,_,clauses) -> List.map (function x,y -> f,x,y)clauses) env.functions)
    in

    (* look for the first clause that can be used to reduce u
     * the boolean in the result indicates if a reduction was made *)
    let rec reduce_first_clause (u:term) clauses : term*bool =
        match clauses with
            | [] -> u,false
            | (f, pattern, def)::clauses ->
                begin
                    try
                        let sigma = unify_pattern pattern u f in
                        let new_term = subst_term def sigma in
                        new_term,true
                    with Error _ -> reduce_first_clause u clauses
            end
    in

    (* reduce the leftmost redex
     * the boolean in the result ndicates if a reduction was made *)
    let rec reduce_leftmost (u:term) : term*bool =
        match u with
            | Daimon -> Daimon,false
            | Constant(c) -> Constant(c),false
            | Var(x) -> reduce_first_clause u clauses
            | Apply(u1,u2) ->
                begin
                    let v,b = reduce_first_clause u clauses in
                    if b
                    then v,b
                    else
                        let v,b = reduce_leftmost u1 in
                        if b
                        then Apply(v, u2),b
                        else
                        let v,b = reduce_leftmost u2 in
                        Apply(u1,v),b
                end
    in

    let rec aux u =
      let v,b = reduce_leftmost u in
      if b then aux v else v

    in aux u


