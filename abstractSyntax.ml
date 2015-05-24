open Tools

type term_constant = { name:        string  ;
                       priority:    int     }   (* should be odd for constructors and even for destructors *)

type type_constant = { name:        string  ;
                       arity:       int     ;
                       priority:    int     }   (* should be odd for inductive and even for coinductive *)

type type_expression =
    | PVar of string     (* polymorphic type variable *)
    | SVar of string     (* non polymorphic type variable *)
    | Atom of type_constant * (type_expression list)
    | Arrow of type_expression * type_expression

let rec check_type_arity = function
    | PVar _ | SVar _ -> ()
    | Atom(t,args) ->
            if t.arity <> List.length args
            then raise (Error ("wrong number of type arguments for " ^ t.name));
            List.iter check_type_arity args
    | Arrow(t1,t2) -> check_type_arity t1 ; check_type_arity t2

let rec doesnt_contain (t:type_expression) (x:type_constant) = match t with
    | SVar _ -> assert false
    | PVar _ -> true
    | Atom(c,_) -> x.name <> c.name
    | Arrow(t1,t2) -> doesnt_contain t1 x && doesnt_contain t2 x

let rec is_strictly_positive (t:type_expression) (x:type_expression)
  = match t,x with
    | PVar _, Atom _ -> true
    | Atom _, Atom _ -> t = x
    | Arrow(t1,t2), Atom(a,_) -> is_strictly_positive t2 x && doesnt_contain t1 a
    | _,_ -> assert false


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

let unify_type (t1:type_expression) (t2:type_expression) : type_substitution * type_substitution =
    let rec aux (eqs:(type_expression*type_expression) list ) = match eqs with
            | [] -> [],[]
            | (s,t)::eqs when s=t -> aux eqs
            | (Atom(t1, args1),Atom(t2, args2))::eqs when t1.name=t2.name ->
                begin
                    try aux ((List.combine args1 args2)@eqs)
                    with Invalid_argument _ -> raise Exit
                end
            | (t, PVar x)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let sigma1,sigma2 = aux eqs in
                    (sigma1, (x,t)::sigma2)
            | (PVar x, t)::eqs when not (occur_type x t) ->
                    let eqs = List.map (function (t1,t2) -> (subst_type [x,t] t1, subst_type [x,t] t2)) eqs in
                    let sigma1,sigma2 = aux eqs in
                    ((x,t)::sigma1, sigma2)
            | _ -> raise Exit
    in aux [ (t1,t2) ]

type environment = { types :  type_constant list              ;
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
                            let sigma1,sigma2 = unify_type t11 t2
                            in subst_type (sigma1 @ sigma2) t12
                    | _ -> raise Exit
            end
        | u -> try get_type u env with Not_found -> raise Exit








(* commands *)
type cmd =
    | Eof
    | Nothing
    | TypeDef of (type_constant * type_expression list * (term_constant * type_expression) list) list
             (*  -defined type-    -PVar arguments-        -constructors/destructors-          -mutual types- *)

let process_type env defs =
    (* all the types that were mutually defined by this definition *)
    let new_types = List.map (function (t,args,_) -> (t,args)) defs
    in

    match defs with
    | [] -> env
    | ((t:type_constant), (args:type_expression list), (consts:(term_constant * type_expression) list))::defs ->
            if List.exists (fun _t -> _t.name = t.name) env.types
            then raise (Error ("there is a type named " ^ t.name))
            else if List.exists (fun _c -> ((fst _c):term_constant).name = t.name) env.consts
            then raise (Error ("there is a constructor named " ^ t.name))
            else if List.exists (fun _x -> fst _x = t.name) env.vars
            then raise (Error ("there is a constant named " ^ t.name))
            else begin
                assert (t.arity = List.length args);
                assert (List.for_all (function PVar _ -> true | _ -> false) args);
                (* 1/ replace priority -1 in constant types, or remove priority from constant type records *)
                (* 2/ no constructor / destructor already exists *)
                (* TODO *)

                (* get defined type with given name *)
                let get_new_type t args =
                    let rec get_new_type_aux = function
                        | [] -> raise (Error ("type " ^ t.name ^ " doesn't exist"))
                        | (_t,_args)::ts when _t.name = t.name && _args = args -> _t
                        | (_t,_args)::ts when _t.name = t.name -> raise (Error ("cannot change parameter for defined type " ^ t.name))
                        | _::ts -> get_new_type_aux ts
                    in
                    get_new_type_aux new_types
                in

                (* get type with given name *)
                let get_type t args =
                    let rec get_type_aux = function
                        | [] -> get_new_type t args
                        | _t::ts when _t.name = t.name && _t.arity = List.length args -> _t
                        | _t::ts when _t.name = t.name -> raise (Error ("type " ^ t.name ^ " used with wrong number of parameters"))
                        | _::ts -> get_type_aux ts
                    in
                    get_type_aux env.types
                in



                (* instances of defined types have the same parameters
                 * priority / arity should be the same as the one from the environment *)
                let rec aux = function
                    | Arrow(t1,t2) -> Arrow(aux t1, aux t2)
                    | PVar x when List.mem (PVar x) args -> PVar x
                    | PVar x -> raise (Error ("parameter " ^ x ^ " doesn't exist"))
                    | Atom(_t, _args) when _t.name = t.name && args = _args -> Atom(t,args)
                    | Atom(_t, _args) when _t.name = t.name -> raise (Error ("cannot use type " ^ t.name ^ " with different type arguments"))
                    | Atom(_t, _args) -> let _t = get_type _t _args in Atom (_t, List.map aux _args)
                    | SVar s -> assert false
                in

                let consts = List.map (fun (c,t) -> (c, aux t)) consts in

                let rec get_result_type = function
                    | Atom(t,args) -> Atom(t,args)
                    | PVar x -> PVar x
                    | SVar _ -> assert false
                    | Arrow(_, t) -> get_result_type t
                in

                (* 3/ check types of constructors / destructors:
                 *       if inductive, RHS of constructor types is t /
                 *       if coinductive, LHS of destructor is t, and the destructor is unary *)

                { types = t::env.types ; consts = consts @ env.consts ; vars = env.vars }
            end

