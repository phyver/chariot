open Base
open Pretty


let rec subst_term (App(u,args):term) (sigma:(var_name*term) list) : term
  = let args = List.map (fun u -> subst_term u sigma) args in
      match u with
        | Var(x) -> app (try List.assoc x sigma with Not_found -> App(Var x,[])) args
        | Daimon | Const _ -> App(u, args)
        | Proj(u,d) -> App(Proj(subst_term u sigma, d), args)


let unify_pattern (pattern:term) (u:term) : (var_name*term) list
  = (* the function defined by the pattern: this variable cannot be instantiated! *)
    let f = get_function_name pattern in

    let rec unify_aux (eqs:(term*term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> unify_aux eqs acc
            | (App(u1,args1),(App(u2,args2) as v2))::eqs ->
                begin
                    match u1,u2 with
                        | (Const(c1),Const(c2)) when c1=c2 -> unify_aux ((List.combine args1 args2)@eqs) acc
                        | (Const(c1), Const(c2)) -> error ("cannot unify constructors " ^ c1 ^ " and " ^ c2)

                        | (Proj(v1,d1),Proj(v2,d2)) when d1=d2 -> unify_aux ((v1,v2)::(List.combine args1 args2)@eqs) acc
                        | (Proj(_,d1), Proj(_,d2)) -> error ("cannot unify projections " ^ d1 ^ " and " ^ d2)

                        | (Const _, Proj _) | (Proj _, Const _) -> error "cannot unify constant and projection"
                        | (Proj _,_) | (_,Proj _) ->  error "cannot unify projection and non-projection"

                        | (Var x, _) when x = f -> error "cannot unify the function name"
                        | (Var x, _) ->
                                let eqs = List.map (function u1,u2 -> (subst_term u1 [x,v2], subst_term u2 [x,v2])) eqs in
                                let acc = List.map (function _x,_u -> (_x, subst_term _u [x,v2])) acc in
                                assert (args1 = []);
                                unify_aux eqs ((x,u)::acc)

                        | (Const _,_) | (_,Const _) ->  error "cannot unify constructor and non-constructor"
                        | (Daimon,_) -> error "cannot unify daimon"
                end
    in unify_aux [pattern,u] []


let reduce_all (env:environment) (v:term) : term
  =
    let rec get_clauses (f:var_name) = function
        | [] -> error ("function " ^ f ^ " doesn't exist")
        | (_f,_,_,clauses)::_ when f=_f -> clauses
        | _::defs -> get_clauses f defs
    in

    (* look for the first clause that can be used to reduce u
     * the boolean in the result indicates if a reduction was made *)
    let rec reduce_first_clause (u:term) clauses : term*bool =
        match clauses with
            | [] -> u,false
            | (pattern, def)::clauses ->
                begin
                    try
                        let sigma = unify_pattern pattern u in
                        let new_term = subst_term def sigma in
                        new_term,true
                    with Error _ -> reduce_first_clause u clauses
                end
    in
    let rec
      reduce_all_atomic u = match u with
          | Var _ | Const _ | Daimon -> App(u,[]),false
          | Proj(v,d) -> let v,b = reduce v in App(Proj(v,d),[]),b
    and
      reduce (v:term) : term*bool =
        let App(u,args) = v in
        let args,bs = List.split (List.map reduce args) in
        let b1 = List.exists (fun b -> b) bs in
        let u,b2 = reduce_all_atomic u in
        let v,b3 = try reduce_first_clause (app u args) (get_clauses (get_function_name v) env.functions)
                   with Error _ -> v,false
        in v, b1&&b2&&b3
    in

    let rec aux v =
      let v,b = reduce v in
      if b then aux v else v
    in

    aux v
