open Base
open Pretty

let rec subst_term (u:term) (sigma:(var_name*term) list) : term
  = match u with
        | Var(x) -> (try List.assoc x sigma with Not_found -> u)
        | Daimon | Const _ | Proj _-> u
        | Apply(u1,u2) -> Apply(subst_term u1 sigma, subst_term u2 sigma)


let unify_pattern (pattern:term) (u:term) : (var_name*term) list
  = (* the function defined by the pattern: this variable cannot be instantiated! *)
    let f = get_function_name pattern in

    let rec unify_aux (eqs:(term*term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> unify_aux eqs acc
            | (Const(c1),Const(c2))::eqs when c1=c2 -> acc
            | (Proj(c1),Proj(c2))::eqs when c1=c2 -> acc
            | (Const(c1), Const(c2))::_ -> error ("cannot unify constructors " ^ c1 ^ " and " ^ c2)
            | (Proj(c1), Proj(c2))::_ -> error ("cannot unify projections " ^ c1 ^ " and " ^ c2)
            | (Const _, Proj _)::_ | (Proj _, Const _)::_ -> error "cannot unify constant and projection"
            | (Proj _,_)::_ | (_,Proj _)::_ ->  error "cannot unify projection and non-projection"
            | (Apply(u1,u2),Apply(v1,v2))::eqs -> unify_aux ((u1,v1)::(u2,v2)::eqs) acc
            | (Apply _, _)::_ -> error "cannot unify application with non-application"
            | (Var x, _)::_ when x = f -> error "cannot unify the function name"
            | (Var x, u)::eqs ->
                    let eqs = List.map (function u1,u2 -> (subst_term u1 [x,u], subst_term u2 [x,u])) eqs in
                    let acc = List.map (function _x,_u -> (_x, subst_term _u [x,u])) acc in
                    unify_aux eqs ((x,u)::acc)
            | (Const _,_)::_ | (_,Const _)::_ ->  error "cannot unify constructor and non-constructor"
            | (Daimon,_)::_ -> error "cannot unify daimon"
    in unify_aux [pattern,u] []


let reduce_all (env:environment) (u:term) : term
  =
    let rec get_clauses (f:var_name) = function
        | [] -> error ("function " ^ f ^ " doesn't exist")
        | (_f,_,_,clauses)::_ when f=_f -> clauses
        | _::defs -> get_clauses f defs
    in

    (* look for the first clause that can be used to reduce u
     * the boolean in the result indicates if a reduction was made *)
    let rec reduce_first_clause (u:term) f clauses : term*bool =
        match clauses with
            | [] -> u,false
            | (pattern, def)::clauses ->
                begin
                    try
                        let sigma = unify_pattern pattern u in
                        let new_term = subst_term def sigma in
                        new_term,true
                    with Error _ -> reduce_first_clause u f clauses
            end
    in

    (* reduce the leftmost redex
     * the boolean in the result ndicates if a reduction was made *)
    let rec reduce_leftmost (u:term) : term*bool =
        match u with
            | Daimon -> Daimon,false
            | Const _ | Proj _ -> u,false
            | Var(x) -> reduce_first_clause u x (get_clauses x env.functions)
            | Apply(u1,u2) ->
                begin
                    try
                        (* FIXME: rewrite... *)
                        let f = get_function_name u in
                        let v,b = reduce_first_clause u f (get_clauses f env.functions) in
                        if b
                        then v,true
                        else error "nothing"
                    with Error _ ->         (* either nothing as above, or because of "get_function_name" when u doesn't start with a function *)
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


