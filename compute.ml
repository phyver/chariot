open Base
open Pretty
open Misc


let rec subst_term (App(u,args):term) (sigma:(var_name*term) list) : term
  = let args = List.map (fun u -> subst_term u sigma) args in
      match u with
        | Var(x) -> app (try List.assoc x sigma with Not_found -> App(Var x,[])) args
        | Angel | Const _ -> App(u, args)
        | Proj(u,d,p) -> App(Proj(subst_term u sigma, d,p), args)


let unify_pattern (pattern,def:term*term) (v:term) : term
  = (* the function defined by the pattern: this variable cannot be instantiated! *)
    let f = get_function_name pattern in

    let rec unify_aux (eqs:(term*term) list) acc =
        match eqs with
            | [] -> acc
            | (s,t)::eqs when s=t -> unify_aux eqs acc
            | (App(u1,args1),(App(u2,args2) as v2))::eqs ->
                begin
                    match u1,u2 with
                        | (Const(c1,p1),Const(c2,p2)) when c1=c2 ->
                            begin
                                assert (p1=p2);
                                try unify_aux ((List.combine args1 args2)@eqs) acc
                                with Invalid_argument "List.combine" -> unificationError "combine"
                            end
                        | (Const(c1,_), Const(c2,_)) -> unificationError ("cannot unify constructors " ^ c1 ^ " and " ^ c2)

                        | (Proj(v1,d1,p1),Proj(v2,d2,p2)) when d1=d2 ->
                            begin
                                assert (p1=p2);
                                try unify_aux ((v1,v2)::((List.combine args1 args2)@eqs)) acc
                                with Invalid_argument "List.combine" -> unificationError "combine"
                            end
                        | (Proj(_,d1,_), Proj(_,d2,_)) -> unificationError ("cannot unify projections " ^ d1 ^ " and " ^ d2)

                        | (Var _f1, Var _f2) when _f1=f && _f2=f ->
                            begin
                                try unify_aux ((List.combine args1 args2)@eqs) acc
                                with Invalid_argument "List.combine" -> unificationError "combine"
                            end
                        | (Var x, _) when x = f -> unificationError "cannot unify the function name"
                        | (Var x, _) ->
                                let eqs = List.map (function u1,u2 -> (subst_term u1 [x,v2], subst_term u2 [x,v2])) eqs in
                                let acc = List.map (function _x,_u -> (_x, subst_term _u [x,v2])) acc in
                                (* assert (args1 = []); *)
                                unify_aux eqs ((x,v2)::acc)

                        | (Const _, Proj _) | (Proj _, Const _) -> unificationError "cannot unify constant and projection"
                        | (Const _,_) | (_,Const _) ->  unificationError "cannot unify constructor and non-constructor"
                        | (Proj _,_) | (_,Proj _) ->  unificationError "cannot unify projection and non-projection"
                        | (Angel,_) -> unificationError "cannot unify angel"
                end
    in
    try
        let sigma = unify_aux [pattern,v] [] in
        subst_term def sigma
    with Invalid_argument "combine_suffix" -> error "cannot unify: not enough arguments"

(* NOTE: very inefficient *)
let reduce_all (env:environment) (v:term) : term
  =
    let rec get_clauses (f:var_name) = function
        | [] -> error ("function " ^ f ^ " doesn't exist")
        | (_f,_,_,clauses)::_ when f=_f -> clauses
        | _::defs -> get_clauses f defs
    in

    (* return a pair of the list without its last element, and its last element *)
    let rec remove_last (l:'a list) : 'a list*'a = match l with
        | [] -> raise (Invalid_argument "remove_last")
        | [z] -> [],z
        | a::l -> let l,z = remove_last l in (a::l,z)
    in

    (* try to apply one clause, and it it doesn't work, remove the last
     * argument and try again
     * If nothing work, return the original term together with false *)
    let rec try_clause (App(u,args) as v) (rest_args) clause : term*bool =
        try
            let new_term = unify_pattern clause v in
            app new_term rest_args,true
        with UnificationError _ ->
            begin
            match args with
                | [] -> app v rest_args, false
                | args ->
                    let args,last = remove_last args in
                    try_clause (App(u,args)) (last::rest_args) clause
            end
    in

    (* look for the first clause that can be used to reduce u
     * the boolean in the result indicates if a reduction was made *)
    let rec reduce_first_clause (App(u,args) as v:term) clauses : term*bool =
        match clauses with
            | [] -> v,false
            | clause::clauses ->
                let new_term,b = try_clause v [] clause in
                if b
                then (new_term,b)
                else (reduce_first_clause v clauses)
    in
    let rec
      reduce_all_atomic u = match u with
          | Var _ | Const _ | Angel -> App(u,[]),false
          | Proj(v,d,p) -> let v,b = reduce v in App(Proj(v,d,p),[]),b
    and
      reduce (v:term) : term*bool =
        let App(u,args) = v in
        let args,bs = List.split (List.map reduce args) in
        let b1 = List.exists (fun b -> b) bs in
        let u,b2 = reduce_all_atomic u in
        let v = app u args in
        let v,b3 = try reduce_first_clause v (get_clauses (get_function_name v) env.functions)
                   with Error _ -> v,false  (* if v doesn't start with a function *)
        in
        v, b1||b2||b3
    in

    let rec aux v =
      let v,b = reduce v in
      if b then aux v else v
    in

    aux v
