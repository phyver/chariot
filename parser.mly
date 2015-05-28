%{
open Base
open Misc


let priority = ref 0

(* check that all the type parameters of a definition are different *)
let check_type_parameters l =
    let l = List.sort compare l in
    let rec uniq = function
        | [] -> ()
        | [a] -> ()
        | a::b::l when a=b -> raise (Error ("Type parameters should be all different."))
        | a::b::l -> uniq (b::l)
    in
    uniq (List.sort compare l)

(* While parsing, we don't know if nullary types correspond to type parameters or other type constants.
 * The Parser uses the "SVar" constructor for those...
 * We can later replace them by a type parameter (if it is one), or a nullary type constant.
 * (Checking that the nullary type constant actually exists is done later. *)
let rec replace_unknown_SVar type_args = function
    | Arrow(t1,t2) -> Arrow(replace_unknown_SVar type_args t1, replace_unknown_SVar type_args t2)
    | TVar(true,x) -> TVar(true,x)
    | Data(t, args) -> Data(t, List.map (replace_unknown_SVar type_args) args)
    | TVar(false,x) -> if List.mem (TVar(true,x)) type_args
                then TVar(true,x)
                else Data(x, [])

(* check that a type doesn't contain an instance of some other type *)
let check_doesnt_contain (t:type_expression) (x:type_expression) =
    let xname, xparams = match x with Data(xname,xparams) -> xname,xparams | _ -> assert false in
    let rec aux = function
        | TVar(false,_) -> assert false
        | TVar(true,_) -> ()
        | Data(c,_) when xname = c -> raise @$ Error ("type " ^ xname ^ " appears in non strictly positive position")
        | Data(c,_) -> ()
        | Arrow(t1,t2) -> aux t1 ; aux t2
    in aux t

(* check that a type only appears strictly positively in another *)
let rec check_is_strictly_positive (t:type_expression) (x:type_expression) =
    let () = match x with Data _ -> () | _ -> assert false in
    let rec aux = function 
        | TVar(true,_) -> ()
        | Data _ -> ()
        | Arrow(t1,t2) -> check_doesnt_contain t1 x; aux t2
        | _ -> assert false
    in aux t

(* check that a type only appears strictly positively in all the arguments of a constant *)
let rec check_is_strictly_positive_constant (t:type_expression) (x:type_expression) =
    let () = match x with Data _ -> () | _ -> assert false in
    let rec aux t = match t with
        | TVar(true,_) -> check_is_strictly_positive t x
        | Data _ -> check_is_strictly_positive t x
        | Arrow(t1,t2) -> check_is_strictly_positive t1 x; aux t2
        | _ -> assert false
    in aux t

(* FIXME:clean *)
(* check the type of a destructor: it should be of the form T(...) -> ...
 * where "T(...)" is the type being defined *)
let check_destructor (t:type_expression) (d:term_constant*type_expression) = match t,d with
    | Data(t,args), (_,Arrow(Data(_t,_args), _)) when _t=t && _args=args -> ()
    | Data(t,args), (d,_) -> raise (Error ("Destructor " ^ d.name ^ " doesn't appropriate type"))
    | _,_ -> assert false

(* FIXME:clean *)
(* check the type of a constructor: it should be of the form ... -> T(...)
 * where "T(...)" is the type being defined *)
let rec check_constructor (t:type_expression) (c:term_constant*type_expression) = match t,c with
    | Data(t,args), (_,Data(_t,_args)) when _t=t && _args=args -> ()
    | Data _, (c,Arrow(_,_t)) -> check_constructor t (c,_t)
    | Data(t,args), (c,_) -> raise (Error ("Constructor " ^ c.name ^ " doesn't appropriate type"))
    | _,_ -> assert false

(* FIXME:clean *)
(* check that all the types being defined only appear with exactly the same parameters *)
let rec check_parameters_of_defined_types (types:type_expression list) (t:type_expression) = match types,t with
    | _,TVar(true,_) -> ()
    | [], Data(t,args) -> ()
    | Data(_t,_args)::types, Data(t,args) when _t=t && _args=args -> ()
    | Data(_t,_args)::types, Data(t,args) when _t=t -> raise @$ Error("type " ^ t ^ " should always use the same parameters in the definition")
    | Data _::types, Data _ -> check_parameters_of_defined_types types t
    | _::_, Data _ -> assert false
    | types,Arrow(t1,t2) -> check_parameters_of_defined_types types t1; check_parameters_of_defined_types types t2
    | _,TVar(false,_) -> assert false
%}

%token EQUAL COLON EMPTYLINE LPAR RPAR LBRAC RBRAC COMMA PIPE DOT
%token DATA CODATA WHERE AND ARROW VAL
%token EOF
%token <string> IDU IDL

%right ARROW
%left DOT

%start statement

%type <Base.cmd> statement
%type <(type_name * arity * (term_constant * type_expression) list) list> new_types

%%


statement:
    | EMPTYLINE                 { Nothing       }
    | new_types EMPTYLINE       { TypeDef(!priority, $1)   }
    | new_functions EMPTYLINE   { Nothing       }
    | COLON IDL EMPTYLINE       { Cmd $2        }
    | EOF                       { Eof           }

new_types:
    |   DATA type_defs
        {
            if !priority mod 2 = 0 then priority := !priority + 1 else priority := !priority + 2;

            let defs = $2 in
            List.iter (function t,consts -> List.iter (check_constructor t) consts) defs;

            (* TODO check_parameters_of_defined_types, for all types*)

            let (result:(type_name * arity * (term_constant * type_expression) list) list)
             = List.map
                    (function Data(t,params),consts -> t, List.length params, List.map (first (fun c -> {c with priority = !priority})) consts
                             | _ -> assert false)
                    defs
            in
            result
        }
    | CODATA type_defs
        {
            if !priority mod 2 = 1 then priority := !priority + 1 else priority := !priority + 2;
            let defs = $2 in
            List.iter (function t,consts -> List.iter (check_destructor t) consts) defs;

            let (result:(type_name * arity * (term_constant * type_expression) list) list)
             = List.map
                    (function Data(t,params),consts -> t, List.length params, List.map (first (fun c -> {c with priority = !priority})) consts
                             | _ -> assert false)
                    defs
            in
            result
        }

type_defs:
    | type_def                  { [$1] }
    | type_def AND type_defs    { $1::$3 }

type_def:
    | IDU type_parameters WHERE const_clauses
        /* check strict positivity */
        {
            let params = $2 in
            check_type_parameters params;

            let t = Data($1,params) in

            let consts = List.map (second @$ replace_unknown_SVar params) $4 in
            List.iter (function (_,_t) -> check_is_strictly_positive_constant _t t) consts;

            (t, consts)
        }

type_parameters:
    | /* nothing */                   { [] }
    | LPAR type_parameters_aux RPAR   { $2 }

type_parameters_aux:
    | IDU                                 { [TVar(true,$1)] }
    | IDU COMMA type_parameters_aux       { (TVar(true,$1))::$3 }

const_clauses:
    | /* nothing */                   { [] }
    | const_clause                    { [$1] }
    | const_clause const_clauses2     { $1::$2 }
    | const_clauses2                  { $1 }

const_clauses2:
    | PIPE const_clause                   { [$2] }
    | PIPE const_clause const_clauses2    { $2::$3 }

const_clause:
    | IDU COLON type_expression      { ({name = $1; priority = !priority}, $3) }

type_expression:
    | IDU                                           { TVar(false,$1) }  /* we don't know yet if this is a polymorphic variable or a type constant... */
    | IDU LPAR RPAR                                 { Data($1, []) }
    | IDU LPAR type_expression_args RPAR            { Data($1,$3) }
    | type_expression ARROW type_expression         { Arrow($1, $3) }
    | LPAR type_expression RPAR                     { $2 }

type_expression_args:
    | type_expression                               { [$1] }
    | type_expression COMMA type_expression_args    { $1::$3 }

new_functions:
    | VAL function_defs         { $2 }

function_defs:
    | function_def { [$1] }
    | function_def AND function_defs { $1::$3 }

function_def:
    | IDL COLON type_expression function_clauses    { () }

function_clauses:
    | /*nothing*/                               { [] }
    | PIPE function_clause function_clauses     { $2::$3 }

function_clause:
    | pattern EQUAL term { () }

term:
    | atomic_term { $1 }
    | term atomic_term { Apply($1, $2) }

atomic_term:
    | LPAR term RPAR { $2 }
    | atomic_term DOT IDU { Apply(Constant({name = $3; priority = -2}), $1) }
    | IDL { Var($1) }
    | IDU { Constant({name = $1; priority = -1}) }

pattern:
    | term { $1 }



