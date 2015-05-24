%{
open Tools
open AbstractSyntax


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
    | PVar x -> PVar x
    | Atom(t, args) -> Atom(t, List.map (replace_unknown_SVar type_args) args)
    | SVar s -> if List.mem (PVar s) type_args
                then PVar s
                else Atom({name = s; priority = -1; arity=0}, [])

(* check the type of a destructor: it should be of the form T(...) -> ...
 * where "T(...)" is the type being defined *)
let check_destructor types t args = function
    | (_,Arrow(Atom(_t,_args), _)) when _t.name=t.name && _args=args -> ()
    | (d,_) -> raise (Error ("Destructor " ^ d.name ^ "doesn't appropriate type"))

(* check the type of a constructor: it should be of the form ... -> T(...)
 * where "T(...)" is the type being defined *)
let rec check_constructor types t args = function
    | (c,Atom(_t,_args)) when _t.name=t.name && _args=args -> ()
    | (c,Arrow(_,_t)) -> check_constructor types t args (c,_t)
    | (c,_) -> raise (Error ("Constructor " ^ c.name ^ " doesn't appropriate type"))

%}

%token EQUAL COLON SEMICOLON LPAR RPAR LBRAC RBRAC COMMA PIPE
%token DATA CODATA WHERE AND ARROW
%token EOF
%token <string> IDU IDL

%right ARROW

%start statement

%type <AbstractSyntax.cmd> statement
%type <(type_constant * type_expression list * (term_constant * type_expression) list) list> type_defs

%%


statement:
  | SEMICOLON               { Nothing       }
  | type_defs SEMICOLON     { TypeDef $1    }
  | EOF                     { Eof           }

type_defs:
  |   DATA type_defs
        {
            if !priority mod 2 = 0 then incr priority;
            let defs = $2 in
            List.map (function t,args,consts ->(t,args,List.map (function (c:term_constant),ct -> (({name = c.name; priority = !priority}:term_constant),ct)) consts)) defs
        }
  | CODATA type_defs
        {
            if !priority mod 2 = 1 then incr priority;
            let defs = $2 in
            List.map (function t,args,consts ->(t,args,List.map (function (c:term_constant),ct -> (({name = c.name; priority = !priority}:term_constant),ct)) consts)) defs
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
            let consts = List.map (function (c,t) -> (c,replace_unknown_SVar params t)) $4 in
            let t:type_constant  =  { name = $1; arity = List.length params; priority = -1} in
            (t, params, consts)
        }

type_parameters:
  | /* nothing */                   { [] }
  | LPAR type_parameters_aux RPAR   { $2 }

type_parameters_aux:
  | IDU                                 { [PVar $1] }
  | IDU COMMA type_parameters_aux       { (PVar $1)::$3 }

const_clauses:
  | /* nothing */                   { [] }
  | const_clause                    { [$1] }
  | const_clause const_clauses2     { $1::$2 }
  | const_clauses2                  { $1 }

const_clauses2:
  | PIPE const_clause                   { [$2] }
  | PIPE const_clause const_clauses2    { $2::$3 }

const_clause:
    | IDU COLON const_type      { ({name = $1; priority = !priority}, $3) }

const_type:
  | IDU                                 { SVar $1 }  /* we don't know yet if this is a polymorphic variable or a type constant... */
  | IDU LPAR RPAR                       { Atom( {name = $1; arity = -1; priority = -1}, [] ) }
  | IDU LPAR const_type_args RPAR       { Atom( {name = $1; arity = -1; priority = -1}, $3 ) }
  | const_type ARROW const_type         { Arrow($1, $3) }

const_type_args:
    | const_type                            { [$1] }
    | const_type COMMA const_type_args      { $1::$3 }


