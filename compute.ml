open Base
open Pretty
open Misc


let rec subst_term (App(u,args):'a term) (sigma:(var_name*'a term) list) : 'a term
  = let args = List.map (fun u -> subst_term u sigma) args in
      match u with
        | Var(x) -> app (try List.assoc x sigma with Not_found -> App(Var x,[])) args
        | Angel | Const _ -> App(u, args)
        | Proj(u,d,p) -> App(Proj(subst_term u sigma, d,p), args)


let unify_pattern (pattern,def:'a term*'a term) (v:'a term) : 'a term
  = (* the function defined by the pattern: this variable cannot be instantiated! *)
    let f = get_function_name pattern in

    let rec unify_aux (eqs:('a term*'a term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> unify_aux eqs acc
            | (App(u1,args1),(App(u2,args2) as v2))::eqs ->
                begin
                    match u1,u2 with
                        | (Const(c1,p1),Const(c2,p2)) when c1=c2 -> assert (p1=p2); unify_aux ((List.combine args1 args2)@eqs) acc
                        | (Const(c1,_), Const(c2,_)) -> error ("cannot unify constructors " ^ c1 ^ " and " ^ c2)

                        | (Proj(v1,d1,p1),Proj(v2,d2,p2)) when d1=d2 -> assert (p1=p2); unify_aux ((v1,v2)::(List.combine args1 args2)@eqs) acc
                        | (Proj(_,d1,_), Proj(_,d2,_)) -> error ("cannot unify projections " ^ d1 ^ " and " ^ d2)

                        | (Const _, Proj _) | (Proj _, Const _) -> error "cannot unify constant and projection"
                        | (Proj _,_) | (_,Proj _) ->  error "cannot unify projection and non-projection"

                        (* | (Var x, _) when x = f -> error "cannot unify the function name" *)
                        | (Var _f1, Var _f2) when _f1=f && _f2=f ->
                        unify_aux ((List.combine args1 args2)@eqs) acc
                        | (Var x, _) ->
                                let eqs = List.map (function u1,u2 -> (subst_term u1 [x,v2], subst_term u2 [x,v2])) eqs in
                                let acc = List.map (function _x,_u -> (_x, subst_term _u [x,v2])) acc in
                                assert (args1 = []);
                                unify_aux eqs ((x,v2)::acc)

                        | (Const _,_) | (_,Const _) ->  error "cannot unify constructor and non-constructor"
                        | (Angel,_) -> error "cannot unify angel"
                end
    in
    let App(pu,pargs) = pattern in
    let App(u,args) = v in

    try
        let eqs,rest = combine_suffix pargs args in
        let sigma = unify_aux ((App(pu,[]),App(u,[]))::eqs) [] in
        app (subst_term def sigma) rest
    with Invalid_argument "combine_suffix" -> error "cannot unify: not enough arguments"


let reduce_all (env:environment) (v:'a term) : 'a term
  =
    let rec get_clauses (f:var_name) = function
        | [] -> error ("function " ^ f ^ " doesn't exist")
        | (_f,_,_,clauses)::_ when f=_f -> clauses
        | _::defs -> get_clauses f defs
    in

    (* look for the first clause that can be used to reduce u
     * the boolean in the result indicates if a reduction was made *)
    let rec reduce_first_clause (v:'a term) clauses : 'a term*bool =
        match clauses with
            | [] -> v,false
            | (pattern, def)::clauses ->
                begin
                    try
                        let new_term = unify_pattern (pattern,def) v in
                        new_term,true
                    with Error _ -> reduce_first_clause v clauses (* FIXME *)
                end
    in
    let rec
      reduce_all_atomic u = match u with
          | Var _ | Const _ | Angel -> App(u,[]),false
          | Proj(v,d,p) -> let v,b = reduce v in App(Proj(v,d,p),[]),b
    and
      reduce (v:'a term) : 'a term*bool =
        let App(u,args) = v in
        let args,bs = List.split (List.map reduce args) in
        let b1 = List.exists (fun b -> b) bs in
        let u,b2 = reduce_all_atomic u in
        let v = app u args in
        let v,b3 = try reduce_first_clause v (get_clauses (get_function_name v) env.functions)
                   with Error _ -> v,false
        in
        v, b1||b2||b3
    in

    let rec aux v =
      let v,b = reduce v in
      if b then aux v else v
    in

    aux v
