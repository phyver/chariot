%{
open Base
open Commands
%}

%token EQUAL COLON ENDSTATEMENT LPAR RPAR LBRAC RBRAC COMMA PIPE DOT
%token DATA CODATA WHERE AND ARROW VAL DUMMY
%token CMDQUIT CMDPROMPT CMDINFER CMDUNIFY CMDSHOW
%token EOF
%token <string> IDU IDL STR TVAR TSVAR

%right ARROW
%left DOT

%start single_statement
%start statements

%type <Commands.cmd list> statements
%type <Commands.cmd> single_statement

%type <priority * (type_name * (type_expression list) * (const_name * type_expression) list) list> new_types
%type <(type_name * (type_expression list) * (const_name * type_expression) list) list> type_defs
%type <type_name * (type_expression list) * (const_name * type_expression) list> type_def

%type <var_name * type_expression * (term * term) list> function_def
%type <(var_name * type_expression * (term * term) list ) list> function_defs

%%

statements:
    | statement statements      { $1::$2 }
    | /*nothing*/ {[]}

single_statement:
    | statement { $1 }
    | EOF { Eof }

statement:
    | ENDSTATEMENT                      { Nothing }
    | new_types ENDSTATEMENT            { let priority,defs = $1 in TypeDef(priority, defs) }
    | new_functions ENDSTATEMENT        { FunDef($1) }
    | command ENDSTATEMENT              { $1 }

command:
    | CMDQUIT                                       { CmdQuit }
    | CMDINFER term                                 { CmdInfer $2 }
    | CMDUNIFY type_expression type_expression      { CmdUnify($2,$3) }
    | CMDPROMPT string                              { CmdPrompt($2) }
    | CMDSHOW string                                { CmdShow($2) }

string:
    | IDL { $1 }
    | IDU { $1 }
    | STR { $1 }

new_types:
    |   DATA type_defs          { (-1,$2) }
    | CODATA type_defs          { (-2,$2) }

type_defs:
    | type_def                  { [$1] }
    | type_def AND type_defs    { $1::$3 }

type_def:
    | IDL type_parameters WHERE const_clauses       { ($1, $2, $4) }

type_parameters:
    | /* nothing */                         { [] }
    | LPAR type_parameters_aux RPAR         { $2 }

type_parameters_aux:
    | TVAR                                  { [TVar(true,$1)] }
    | TVAR COMMA type_parameters_aux        { (TVar(true,$1))::$3 }

const_clauses:
    | /* nothing */                         { [] }
    | const_clause                          { [$1] }
    | const_clause const_clauses2           { $1::$2 }
    | const_clauses2                        { $1 }

const_clauses2:
    | PIPE const_clause                     { [$2] }
    | PIPE const_clause const_clauses2      { $2::$3 }

const_clause:
    | IDU COLON type_expression             { ($1, $3) }

type_expression:
    /* TODO: add TSVAR for '_a --> TVar(false,"a") */
    | TVAR                                          { TVar(true,$1) }
    | TSVAR                                         { TVar(false,$1) }
    | IDL                                           { Data($1, []) }
    | IDL LPAR RPAR                                 { Data($1, []) }
    | IDL LPAR type_expression_args RPAR            { Data($1,$3) }
    | type_expression ARROW type_expression         { Arrow($1, $3) }
    | LPAR type_expression RPAR                     { $2 }

type_expression_args:
    | type_expression                               { [$1] }
    | type_expression COMMA type_expression_args    { $1::$3 }

new_functions:
    | VAL function_defs         { $2 }

function_defs:
    | function_def                      { [$1] }
    | function_def AND function_defs    { $1::$3 }

function_def:
    | IDL COLON type_expression function_clauses    { ($1,$3,$4) }

function_clauses:
    | /*nothing*/                               { [] }
    | PIPE function_clause function_clauses     { $2::$3 }

function_clause:
    | lhs_term EQUAL rhs_term        { ($1,$3) }

rhs_term:
    | term { $1 }

term:
    | atomic_term               { $1 }
    | term atomic_term          { Apply($1, $2) }

atomic_term:
    | LPAR term RPAR            { $2 }
    | atomic_term DOT IDU       { Apply(Constant($3), $1) }
    | IDL                       { Var($1) }
    | IDU                       { Constant($1) }

lhs_term:
    | IDL   { Var($1) }
    | LPAR lhs_term RPAR { $2 }
    | lhs_term DOT IDU { Apply(Constant($3), $1) }
    | lhs_term atomic_pattern { Apply($1,$2) }

atomic_pattern:
    | IDL { Var($1) }
    | IDU { Constant($1) }
    | LPAR pattern RPAR { $2 }

pattern:
    | atomic_pattern { $1 }
    | pattern atomic_pattern { Apply($1, $2) }

