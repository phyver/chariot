open Tools

type term_constant = { name:        string  ;
                       priority:    int     }   (* should be odd for constructors and even for destructors *)


type tname = string
type type_expression =
    | PVar of string     (* polymorphic type variable *)
    | SVar of string     (* non polymorphic type variable *)
    | Atom of tname * (type_expression list)
    | Arrow of type_expression * type_expression

type term =
    | Var of string
    | Constant of term_constant
    | Apply of term*term

type type_substitution = (string * type_expression) list

let rec occur_type x (t:type_expression) = match t with
    | PVar y | SVar y -> x=y
    | Arrow(t1,t2) -> occur_type x t1 || occur_type x t2
    | Atom(_, args) -> List.exists (occur_type x) args

let rec subst_type (sigma:type_substitution) (t:type_expression) : type_expression = match t with
    | PVar y -> (try List.assoc y sigma with Not_found -> PVar y)
    | SVar y -> SVar y
    | Arrow(t1,t2) -> Arrow(subst_type sigma t1, subst_type sigma t1)
    | Atom(a, args) -> Atom(a, List.map (subst_type sigma) args)

let unify_type (t1:type_expression) (t2:type_expression) : type_substitution =
    let rec aux (eqs:(type_expression*type_expression) list ) = match eqs with
            | [] -> []
            | (s,t)::eqs when s=t -> aux eqs
            | (Atom(t1, args1),Atom(t2, args2))::eqs when t1=t2 ->
                begin
                    try aux ((List.combine args1 args2)@eqs)
                    with Invalid_argument _ -> raise Exit
                end
            | (t, PVar x)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    (x,t)::(aux eqs)
            | (PVar x, t)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    (x,t)::(aux eqs)
            | _ -> raise Exit
    in aux [ (t1,t2) ]

type environment = { types :  type_expression list              ;
                     consts : (term_constant * type_expression) list  ;
                     vars :   (string * type_expression) list }

let get_type (c:term) env =
    match c with
        | Var s -> List.assoc s env.vars
        | Constant c -> List.assoc c env.consts
        | _ -> assert false

let rec infer_type (u:term) (env:environment) : type_expression =
    match u with
        | Apply(u1,u2) ->
            begin
                let t1 = infer_type u1 env in
                let t2 = infer_type u2 env in
                match t1 with
                    | Arrow(t11,t12) ->
                            let sigma = unify_type t11 t2
                            in subst_type sigma t12
                    | _ -> raise Exit
            end
        | u -> try get_type u env with Not_found -> raise Exit








(* commands *)
type cmd =
    | Eof
    | Nothing
    | TypeDef of (type_expression * (term_constant * type_expression) list) list
             (*  -defined type-        -constructors/destructors-          -mutual types- *)

let process_type env defs =
    (* all the types that were mutually defined by this definition *)
    let new_types = List.map (function (t,_) -> t) defs
    in

    match defs with
    | [] -> env
    | (Atom(t,params), consts)::defs ->
            if List.exists (function Atom(_t,_) -> _t=t | _ -> assert false) env.types
            then raise (Error ("there is a type named " ^ t))
            else begin
                assert (List.for_all (function PVar _ -> true | _ -> false) params);
                (* 2/ no constructor / destructor already exists *)
                (* TODO *)

                (* get defined type with given name *)
                let get_new_type t params =
                    let rec get_new_type_aux = function
                        | [] -> raise (Error ("type " ^ t ^ " doesn't exist"))
                        | Atom(_t,_params)::ts when _t = t && _params = params -> _t
                        | Atom(_t,_params)::ts when _t = t -> raise (Error ("cannot change parameter for defined type " ^ t))
                        | Atom(_,_)::ts -> get_new_type_aux ts
                        | _ -> assert false
                    in
                    get_new_type_aux new_types
                in

                (* get type with given name *)
                let get_type t params =
                    let rec get_type_aux = function
                        | [] -> get_new_type t params
                        | Atom(_t,_params)::ts when _t = t && List.length _params = List.length params -> _t
                        | Atom(_t,_)::ts when _t = t -> raise (Error ("type " ^ t ^ " used with wrong number of parameters"))
                        | Atom(_,_)::ts -> get_type_aux ts
                        | _::ts -> assert false
                    in
                    get_type_aux env.types
                in



                (* priority / arity should be the same as the one from the environment *)
                let rec aux = function
                    | Arrow(t1,t2) -> Arrow(aux t1, aux t2)
                    | PVar x when List.mem (PVar x) params -> PVar x
                    | PVar x -> raise (Error ("parameter " ^ x ^ " doesn't exist"))     (* FIXME: to do in parser.mly? *)
                    | Atom(_t, _params) when _t = t && params = _params -> Atom(t,params)   (* FIXME: to do in parser.mly? *)
                    | Atom(_t, _params) when _t = t -> raise (Error ("cannot use type " ^ t ^ " with different type arguments"))   (* FIXME: to do in parser.mly? *)
                    | Atom(_t, _params) -> let _t = get_type _t _params in Atom (_t, List.map aux _params)
                    | SVar s -> assert false
                in

                let consts = List.map (fun (c,t) -> (c, aux t)) consts in

                { types = Atom(t,params)::env.types ; consts = consts @ env.consts ; vars = env.vars }
            end
    | _::defs -> assert false

