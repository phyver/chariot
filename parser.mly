%{
open Misc
open Base
open State
open Commands

let rec int_to_term n u =
    if n=0
    then u
    else int_to_term (n-1) (App(Const("Succ",None),u))

let rec list_to_term l u =
    match l with
        | [] -> u
        | v::l -> list_to_term l (App(App(Const("Cons",None),v),u))

let dummy_nb = ref 0

let dummy () = incr dummy_nb; Var("_" ^ (sub_of_int !dummy_nb))

let mk_product l =
    let n = List.length l in
    Data("prod_" ^ (string_of_int n), l)

let mk_tuple l =
    let n = List.length l in
    app (Const("Tuple_" ^ (string_of_int n),None)) l

%}

%token EQUAL COLON SEMICOLON BLANKLINE LPAR RPAR COMMA PIPE DOT DUMMY ANGEL ARROW PLUS MINUS STAR
%token LSQBRAC RSQBRAC DOUBLECOLON DOUBLEARROW
%token DATA CODATA WHERE AND VAL
%token CMDHELP CMDQUIT CMDPROMPT CMDSHOW CMDTEST CMDVERBOSE CMDSET
%token CMDEXPLORE CMDREDUCE CMDUNFOLD CMDECHO CMDTESTCOMPOSE CMDTESTCOMPARE
%token EOF
%token <string> IDU IDL STR TVAR
%token <int> INT

%right ARROW DOUBLECOLON
%left DOT
%left PLUS


%start single_statement
%start statements
%start explore_command

%type <Commands.cmd list> statements
%type <Commands.cmd> single_statement
%type <Commands.explore_cmd> explore_command

%type <int * (type_name * (type_expression list) * (const_name * type_expression) list) list> new_types
%type <(type_name * (type_expression list) * (const_name * type_expression) list) list> type_defs
%type <type_name * (type_expression list) * (const_name * type_expression) list> type_def

%type <var_name * type_expression option * (term * term) list> function_def
%type <(var_name * type_expression option * (term * term) list ) list> function_defs

%%

statements:
    | statement statements      { $1::$2 }
    | eos statements            { $2 }
    | EOF                       { [] }

single_statement:
    | statement eos     { $1 }
    | eos               { Nothing }
    | EOF               { Eof }
    | term eos          { CmdReduce $1 }

statement:
    | new_types       { let n,defs = $1 in TypeDef(n, defs) }
    | new_functions   { FunDef($1) }
    | command         { $1 }

eos:
    | SEMICOLON     {}
    | BLANKLINE     {}

command:
    | CMDEXPLORE term                                   { CmdExplore $2 }
    | CMDREDUCE term                                    { CmdReduce $2 }
    | CMDUNFOLD term COMMA INT                          { CmdUnfold($2,$4) }
    | CMDQUIT                                           { CmdQuit }
    | CMDPROMPT string                                  { CmdPrompt($2) }
    | CMDSHOW string                                    { CmdShow($2) }
    | CMDVERBOSE INT                                    { CmdVerbose($2) }
    | CMDSET string string                              { CmdOption($2,$3) }
    | CMDSET string INT                                 { CmdOption($2,string_of_int $3) }
    | CMDSET                                            { CmdOption("","") }
    | CMDHELP                                           { CmdHelp }
    | CMDECHO string                                    { CmdEcho($2) }

    | CMDTESTCOMPOSE lhs_term DOUBLEARROW rhs_term AND lhs_term DOUBLEARROW rhs_term       { CmdCompose($2,$4,$6,$8) }
    | CMDTESTCOMPARE lhs_term DOUBLEARROW rhs_term AND lhs_term DOUBLEARROW rhs_term       { CmdCompare($2,$4,$6,$8) }

string:
    | IDL { $1 }
    | IDU { $1 }
    | STR { $1 }

explore_command:
    | int_range eos             { ExpUnfold $1 }
    | MINUS eos                 { ExpUnfoldAll }
    | /*nothing*/ eos           { ExpUnfoldAll }
    | CMDQUIT eos               { ExpEnd }
    | EOF                       { ExpEnd }

int_range:
    | INT                       { [$1] }
    | INT int_range             { $1::$2 }
    | INT MINUS INT int_range   { (range $1 $3) @ $4 }

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
    | TVAR                                  { [TVar($1)] }
    | TVAR COMMA type_parameters_aux        { (TVar($1))::$3 }

const_clauses:
    | /* nothing */                         { [] }
    | const_clause                          { $1 }
    | const_clause const_clauses2           { $1@$2 }
    | const_clauses2                        { $1 }

const_clauses2:
    | PIPE const_clause                     { $2 }
    | PIPE const_clause const_clauses2      { $2@$3 }

const_clause:
    | IDU consts_type COLON type_expression             { ($1, $4)::(List.map (fun c -> (c,$4)) $2) }

consts_type:
    | /* nothing */         { [] }
    | PIPE IDU consts_type  { $2::$3 }


atomic_type:
    | LPAR type_expression RPAR                     { $2 }
    | TVAR                                          { TVar($1) }
    | IDL                                           { Data($1, []) }
    | IDL LPAR RPAR                                 { Data($1, []) }
    | IDL LPAR type_expression_args RPAR            { Data($1,$3) }

type_expression:
    | atomic_type ARROW type_expression             { Arrow($1, $3) }
    | product_type ARROW type_expression            { Arrow($1, $3) }
    | atomic_type                                   { $1 }
    | product_type                                  { $1 }

product_type:
    | atomic_type product_type_aux                  { mk_product ($1::$2) }
product_type_aux:
    | STAR atomic_type                              { [$2] }
    | STAR atomic_type product_type_aux             { $2::$3 }

type_expression_args:
    | type_expression                               { [$1] }
    | type_expression COMMA type_expression_args    { $1::$3 }

new_functions:
    | VAL function_defs         { $2 }

function_defs:
    | function_def                      { [$1] }
    | function_def AND function_defs    { $1::$3 }

function_def:
    | IDL COLON type_expression function_clauses    { ($1,Some($3),$4) }
    | function_clause function_clauses              { (get_function_name (fst $1),None,$1::$2) }
    | function_clauses                              { (get_function_name (fst (List.hd $1)),None,$1) }

function_clauses:
    | /*nothing*/                               { [] }
    | PIPE function_clause function_clauses     { $2::$3 }

function_clause:
    | lhs_term EQUAL rhs_term        { ($1,$3) }

rhs_term:
    | term { $1 }

term:
    | atomic_term               { $1 }
    | term atomic_term          { App($1,$2) }

    | term PLUS atomic_term                { App(App(Var("add"),$1),$3) }

atomic_term:
    | LPAR term RPAR            { $2 }
    | atomic_term DOT IDU       { App(Proj($3,None), $1) }
    | IDL                       { Var($1) }
    | IDU                       { Const($1,None) }
    | ANGEL                     { Angel }

    | INT                       { int_to_term $1 (Const("Zero",None)) }
    | term_list                 { list_to_term (List.rev $1) (Const("Nil",None)) }
    | atomic_term DOUBLECOLON atomic_term       { App(App(Const("Cons",None),$1),$3) }
    | tuple                     { $1 }

tuple:
    | LPAR RPAR                         { mk_tuple [] }
    | LPAR term tuple_aux RPAR          { mk_tuple ($2::$3) }
tuple_aux:
    | COMMA term                        { [$2] }
    | COMMA term tuple_aux              { $2::$3 }


term_list:
    | LSQBRAC term_list_inside RSQBRAC  { $2 } /* FIXME: check priorities... */
    | LSQBRAC RSQBRAC                   { [] }

term_list_inside:
    | term                              { [$1] }
    | term SEMICOLON term_list_inside   { $1::$3 }

lhs_term:
    | IDL                           { Var($1) }
    | LPAR lhs_term RPAR            { $2 }
    | lhs_term DOT IDU              { App(Proj($3,None), $1) }
    | lhs_term atomic_pattern       { App($1,$2) }

atomic_pattern:
    | DUMMY                 { dummy() }
    | IDL                   { Var($1) }
    | IDU                   { Const($1,None) }
    | LPAR pattern RPAR     { $2 }

    | INT                   { int_to_term $1 (Const("Zero",None)) }
    | pattern_list          { list_to_term (List.rev $1) (Const("Nil",None)) }
    | atomic_pattern DOUBLECOLON atomic_pattern       { App(App(Const("Cons",None),$1),$3) }
    | atomic_pattern PLUS INT      { int_to_term $3 $1 }
    | pattern_tuple         { $1 }

pattern:
    | atomic_pattern            { $1 }
    | pattern atomic_pattern    { App($1,$2) }


pattern_list:
    | LSQBRAC pattern_list_inside RSQBRAC  { $2 } /* FIXME: check priorities... */
    | LSQBRAC RSQBRAC                   { [] }

pattern_list_inside:
    | pattern                              { [$1] }
    | pattern SEMICOLON pattern_list_inside   { $1::$3 }

pattern_tuple:
    | LPAR RPAR                         { mk_tuple [] }
    | LPAR pattern pattern_tuple_aux RPAR          { mk_tuple ($2::$3) }
pattern_tuple_aux:
    | COMMA pattern                        { [$2] }
    | COMMA pattern pattern_tuple_aux              { $2::$3 }

