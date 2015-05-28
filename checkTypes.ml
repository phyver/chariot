open Base


let process_type_defs (env:environment) (priority:priority) (defs:(type_name * arity * (const_name * type_expression) list) list) =
    (* all the types that were mutually defined by this definition *)
    let new_types = List.map (function (t,_,_) -> t) defs in

    let rec process_type_defs_aux env defs =
        match defs with

        | [] -> env

        | (t,arity,consts)::defs ->
                if List.exists (function _t,_,_,_ -> _t=t) env.types
                then raise (Error ("there is a type named " ^ t))
                else begin
                    (* 2/ no constructor / destructor already exists *)
                    (* TODO *)

                    (* arity should be the same as the one from the environment *)
                    let rec aux = function
                        | Arrow(t1,t2) -> Arrow(aux t1, aux t2)
                        | TVar(true,x) as t -> t
                        | TVar(false,_) -> assert false
                        | Data(_t, _params) as t ->
                                if List.mem _t new_types
                                then t
                                else
                                    try
                                        if List.length _params = get_arity _t env
                                        then t
                                        else raise (Error ("*** type " ^ _t ^ " is used with inapropriate arity"))
                                    with Not_found -> raise (Error ("*** type " ^ _t ^ " doesn't exist"))

                    in

                    assert false
                    (* let consts = List.map (function c,t -> c.name, second aux) consts in *)

                    (* let env = process_type_defs_aux env defs in *)

                    (* { env with types = (t,arity,priority,consts)::env.types ; constants = consts @ env.constants } *)
                end

    in process_type_defs_aux env defs


