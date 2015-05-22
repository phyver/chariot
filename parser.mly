%{
open Tools
open AbstractSyntax

let priority = ref 0
let coind_priority () = if !priority mod 2 = 0 then !priority else (incr priority; !priority)
let ind_priority () = if !priority mod 2 = 1 then !priority else (incr priority; !priority)


let current_env = {types = []; consts = []; vars = []}

%}

%token EQUAL COLON SEMICOLON LPAR RPAR LBRAC RBRAC COMMA PIPE
%token DATA CODATA WHERE AND ARROW
%token EOF
%token <string> IDU IDL

%right ARROW

%start statement

%type <unit> statement
%type <unit> statements

%%

statements:
  | statement statements { $1 ; $2 }
  | EOF { () }

statement:
  | SEMICOLON { () }
  | type_def SEMICOLON { () }

type_def:
  | DATA IDU WHERE const_clauses
        {
            let t:type_constant = { name=$2; arity=0; priority=ind_priority () } in
            current_env.types <- t::current_env.types;
            ()
        }
  | DATA IDU LPAR type_args RPAR WHERE const_clauses
        { () }
  | CODATA IDU WHERE const_clauses
        { () }
  | CODATA IDU LPAR type_args RPAR WHERE const_clauses
        { () }

type_args:
  | IDU { [PVar $1] }
  | IDU COMMA type_args { (PVar $1)::$3 }

const_clauses:
  | { [] }
  | const_clause { [$1] }
  | const_clause const_clauses2 { $1::$2 }
  | const_clauses2 { $1 }

const_clauses2:
  | PIPE const_clause { [$2] }
  | PIPE const_clause const_clauses2 { $2::$3 }

const_clause:
    | IDU COLON const_type { ($1,$3) }

const_type:
  | IDU { SVar $1 }  /* we don't know yet if this is a polymorphic variable or a type constant... */
  | IDU LPAR RPAR { Atom( {name = $1; arity = -1; priority = -1}, [] ) }
  | IDU LPAR const_type_args RPAR { Atom( {name = $1; arity = -1; priority = -1}, $3 ) }
  | const_type ARROW const_type { Arrow($1, $3) }

const_type_args:
    | const_type { [$1] }
    | const_type COMMA const_type_args { $1::$3 }


