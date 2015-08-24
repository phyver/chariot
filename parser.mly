/*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
adequacy checker for recursive definitions involving nested least and
greatest fixed points.

This software is governed by the CeCILL-B license under French law and
abiding by the rules of distribution of free software.  You can  use,
modify and/ or redistribute the software under the terms of the CeCILL-B
license as circulated by CEA, CNRS and INRIA at the following URL
"http://www.cecill.info".

As a counterpart to the access to the source code and  rights to copy,
modify and redistribute granted by the license, users are provided only
with a limited warranty  and the software's author,  the holder of the
economic rights,  and the successive licensors  have only  limited
liability.

In this respect, the user's attention is drawn to the risks associated
with loading,  using,  modifying and/or developing or reproducing the
software by the user in light of its specific status of free software,
that may mean  that it is complicated to manipulate,  and  that  also
therefore means  that it is reserved for developers  and  experienced
professionals having in-depth computer knowledge. Users are therefore
encouraged to load and test the software's suitability as regards their
requirements in conditions enabling the security of their systems and/or
data to be ensured and,  more generally, to use and operate it in the
same conditions as regards security.

The fact that you are presently reading this means that you have had
knowledge of the CeCILL-B license and that you accept its terms.
========================================================================*/


%{
open Misc
open Env
open Utils
open State
open Typing
open Pretty
open Compute
open Explore
open SCTCalls
open Coverage
open FunctionDefs
open TypeDefs

(* transform a list of types into the product *)
let list_to_product (l:type_expression list) : type_expression
  = let n = List.length l in
    Data("prod_" ^ (string_of_int n), l)

(* transforms an integer into a term by adding Succ constructors in front of u *)
let rec int_to_term (n:int) (u:unit term) : unit term
  = if n=0
    then u
    else int_to_term (n-1) (App(Const("Succ",None,()),u,()))

(* transform an addition u+v into either an application of the "add" function or, when v is an natural number, into Succ(... Succ (u) *)
let process_addition u v
  = let rec add_aux u v
      = match v with
            | Const("Zero", _,()) -> u
            | App(Const("Succ", p,()), v,()) -> add_aux (App(Const("Succ",p,()),u,())) v
            | _ -> raise Exit
    in
    try add_aux u v
    with Exit -> App(App(Var("add",()),u,()),v,())

(* tranform a list of terms into the corresponding list by adding Cons constructors in front of u *)
let rec list_to_term (l:unit term list) (u:unit term) : unit term
  = match l with
        | [] -> u
        | v::l -> list_to_term l (App(App(Const("Cons",None,()),v,()),u,()))

(* tranform a list of terms into the corresponding tuple *)
let tuple_term (l:unit term list) : unit term =
    let n = List.length l in
    app (Const("Tuple_" ^ (string_of_int n),None,())) l


(* a reference to number dummy arguments in terms *) (*FIXME: necessary??? *)
let dummy_nb = ref 0
(* generate a fresh dummy variable *)
let dummy () = incr dummy_nb; Var("_" ^ (sub_of_int !dummy_nb),())

(* execute a statement and catch appropriate errors *)
let exec_cmd (cmd:unit->unit) : unit
  = try cmd ()
    with
        | Error err ->
            if option "continue_on_error"
            then errmsg "%s" err
            else error err
        | TypeError err ->
            if option "continue_on_error"
            then errmsg "typing error: %s" err
            else error err

(* process some types definitions and add them to the environment *)
let cmd_process_type_defs n defs
  = (* the real bloc number of this bunch of mutual type definitions *)
    let n = if even current_state.current_bloc = even n
            then current_state.current_bloc+2
            else current_state.current_bloc+1
    in
    current_state.env <- process_type_defs current_state.env n defs;
    current_state.last_term <- None;
    current_state.last_explore <- None

(* process some functions definitions and add them to the environment *)
let cmd_process_function_defs defs
  = current_state.env <- process_function_defs current_state.env defs;
    current_state.last_term <- None;
    current_state.last_explore <- None

(* show (some part of) the environment *)
let cmd_show s =
    if s = "types" then show_types current_state.env
    else
    if s = "functions" then show_functions current_state.env
    else
    if s = "all" || s = "env" then show_environment current_state.env
    else

    (* FIXME: ugly *)
    let rec show_type_aux = function
        | [] -> raise Exit
        | (tname,params,n,consts)::_ when s=tname ->
            show_type_bloc current_state.env [(tname,params,n,consts)]
        | _::types -> show_type_aux types
    in
    let rec show_function_aux = function
        | [] -> raise Exit
        | (f,m,t,clauses)::_ when s=f ->
            show_function_bloc current_state.env [(f,m,t,clauses)]
        | _::defs -> show_function_aux defs
    in
    try show_type_aux current_state.env.types
    with Exit ->
        try show_function_aux current_state.env.functions
        with Exit -> errmsg "no type or function %s in environment" s


let cmd_show_help ()
  = print_list "| " "\n| " "\n\n" print_string [
        "";
        "chariot: a language with arbitrary nested inductive and coinductive types";
        "";
        "TODO";
        "";
    ]


(* reduce a term and show the result *)
let cmd_reduce (term:unit term) : unit
  = let t,term,context = infer_type_term current_state.env term in
    msg "term: %s" (string_of_term term);
    let term = reduce_all current_state.env term in
    current_state.last_term <- Some term;
    current_state.last_explore <- None;
    msg "result: %s" (string_of_term term);
    msg "of type: %s" (string_of_type t);
    if not (context = [])
    then msg "with free variables: %s" (string_of_list " , " (function x,t -> x^" : "^(string_of_type t)) context);
    print_newline()

let cmd_show_last ()
  = match current_state.last_term with
        | None -> ()
        | Some t ->
            msg "last result: %s" (string_of_term t)

(* unfold a term by expanding lazy subterms up-to a given depth, and show the result *)
let cmd_unfold_initial (term:unit term) (depth:int) : unit
  = let t,term,context = infer_type_term current_state.env term in
    let term = unfold_to_depth current_state.env term depth in
    msg "... %s" (string_of_explore_term term);
    msg "of type: %s" (string_of_type t);
    if not (context = [])
    then msg "with free variables: %s" (string_of_list " , " (function x,t -> x^" : "^(string_of_type t)) context);
    current_state.last_explore <- Some term;
    print_newline()

let cmd_unfold (l:int list) : unit
  = try
        let t = match current_state.last_explore with
                    | Some t -> t
                    | None ->
                        begin
                            match current_state.last_term with
                                | Some t ->
                                    let t =  unfold_to_depth current_state.env t 0 in
                                    t
                                | None -> raise Exit 
                        end
        in
        let t = match l with
                    | [] -> unfold current_state.env (fun _ -> true) t
                    | _ ->  unfold current_state.env (fun n -> List.mem n l) t
        in
        current_state.last_explore <- Some t;
        msg "... %s" (string_of_explore_term t)

    with Exit -> errmsg "There is no term to unfold..."




(***
 * various functions for testing functions
 *)
let test_unify_type t1 t2 =
    msg "unifying type   %s" (string_of_type t1);
    msg "          and   %s" (string_of_type t2);
    let sigma = unify_type_mgu t1 t2 in
    let t1s = subst_type sigma t1 in
    let t2s = subst_type sigma t2 in
    assert (t1s = t2s);
    msg "       result   %s" (string_of_type t1s);
    msg "          via   %s" (string_of_list "  ;  " (function x,t -> "'"^x^" := "^(string_of_type t)) sigma);
    print_newline()

let test_unify_term pattern term =
    let _,pattern,_ = infer_type_term current_state.env pattern in
    let _,term,_ = infer_type_term current_state.env term in
    msg "unifying pattern   %s" (string_of_term pattern);
    msg "        and term   %s" (string_of_term term);
    let new_term = unify_pattern (pattern,pattern) term in
    msg "          result   %s" (string_of_term new_term);
    print_newline()

let test_compose l1 r1 l2 r2 =
    msg "  %s => %s    o    %s => %s" (string_of_term l1) (string_of_term r1) (string_of_term l2) (string_of_term r2);
    let l1 = pattern_to_approx_term l1 in
    let r1 = pattern_to_approx_term r1 in
    let l2 = pattern_to_approx_term l2 in
    let r2 = pattern_to_approx_term r2 in
    let l,r = collapsed_compose current_state.bound current_state.depth (l1,r1) (l2,r2) in
    msg "          =  %s => %s" (string_of_approx_term l) (string_of_approx_term r);
    print_newline()

let test_compare l1 r1 l2 r2 =
    let l1 = pattern_to_approx_term l1 in
    let r1 = pattern_to_approx_term r1 in
    let l2 = pattern_to_approx_term l2 in
    let r2 = pattern_to_approx_term r2 in
    let l1,r1 = collapse_clause current_state.bound current_state.depth (l1,r1) in
    let l2,r2 = collapse_clause current_state.bound current_state.depth (l2,r2) in
    msg "  %s => %s    ≥    %s => %s" (string_of_approx_term l1) (string_of_approx_term r1) (string_of_approx_term l2) (string_of_approx_term r2); 
    if approximates (l1,r1) (l2,r2)
    then msg "        TRUE"
    else msg "        FALSE";
    print_newline()

let test_collapse p =
    let p = pattern_to_approx_term p in
    let q = collapse_pattern current_state.depth p in
    let q = collapse_weight_in_term current_state.bound q in
    msg "  collapse of   %s   is   %s" (string_of_approx_term p) (string_of_approx_term q);
    print_newline()

%}

%token EQUAL COLON SEMICOLON BLANKLINE LPAR RPAR COMMA PIPE DOT DUMMY ANGEL ARROW PLUS MINUS STAR GT
%token LSQBRAC RSQBRAC DOUBLECOLON DOUBLEARROW
%token DATA CODATA WHERE AND VAL
%token CMDHELP CMDQUIT CMDSHOW CMDSET
%token CMDUNFOLD CMDREDUCE CMDUNFOLD CMDECHO
%token TESTUNIFYTYPES TESTUNIFYTERMS TESTCOMPOSE TESTCOMPARE TESTCOLLAPSE
%token EOF
%token <string> IDU IDL STR TVAR
%token <int> INT

%right ARROW DOUBLECOLON
%left DOT
%left PLUS


%start single_statement
%start statements

%type <unit> statements
%type <unit> single_statement

%type <int * (type_name * (type_expression list) * (const_name * type_expression) list) list> new_types
%type <(type_name * (type_expression list) * (const_name * type_expression) list) list> type_defs
%type <type_name * (type_expression list) * (const_name * type_expression) list> type_def

%type <var_name * type_expression option * (unit pattern * unit term) list> function_def
%type <(var_name * type_expression option * (unit pattern * unit term) list ) list> function_defs

%%

statements:
    | done_statement statements      { $1;$2 }
    | eos statements                 { $2 }
    | EOF                            { () }

done_statement:
    | statement         { exec_cmd $1 }

single_statement:
    | statement eos     { exec_cmd $1}
    | eos               { exec_cmd cmd_show_last }
    | EOF               { raise Exit }
    | term eos          { exec_cmd (fun () -> cmd_reduce $1) }

statement:
    | new_types       { fun () -> let n,defs = $1 in cmd_process_type_defs n defs }
    | new_functions   { fun () -> cmd_process_function_defs $1 }
    | command         {$1 }

command:
    | CMDREDUCE term                                    { fun () -> cmd_reduce $2 }
    | CMDQUIT                                           { fun () -> raise Exit }
    | CMDSHOW string                                    { fun () -> cmd_show $2 }
    | CMDSET string string                              { fun () -> set_option $2 $3 }
    | CMDSET string INT                                 { fun () -> set_option $2 (string_of_int $3) }
    | CMDSET                                            { fun () -> show_options () }
    | CMDHELP                                           { fun () -> cmd_show_help () }
    | CMDECHO string                                    { fun () -> msg "%s" $2 }

    | CMDUNFOLD term                                    { fun () -> cmd_unfold_initial $2 0 }
    | CMDUNFOLD term COMMA INT                          { fun () -> cmd_unfold_initial $2 $4 }
    | GT int_range                                      { fun () -> cmd_unfold $2 }

    | TESTUNIFYTYPES type_expression AND type_expression                                 { fun () -> test_unify_type $2 $4 }
    | TESTUNIFYTERMS pattern AND term                                                    { fun () -> test_unify_term $2 $4 }
    | TESTCOLLAPSE lhs_term                                                              { fun () -> test_collapse $2 }
    | TESTCOMPOSE lhs_term DOUBLEARROW rhs_term AND lhs_term DOUBLEARROW rhs_term        { fun () -> test_compose $2 $4 $6 $8 }
    | TESTCOMPARE lhs_term DOUBLEARROW rhs_term AND lhs_term DOUBLEARROW rhs_term        { fun () -> test_compare $2 $4 $6 $8 }


new_types:
    /*(* The output of a type definition from the parser consists of
     *   - a bloc number odd/even to distinguish data / codada types
     *   - a list of (possibly) mutual type definitions:
     *        - a type name
     *        - a list of type parameters, all of the form TVar(true,x)
     *        - a list of constants (constructors for data, destructors for codata), with a type
     * No sanity checking is done by the parser, everything is done in the "process_type_defs" function in file "checkTypes.ml"...
     *)*/
    |   DATA type_defs          { (-1,$2) }     /* the "-1" and "-2" are replaced by the appropriate bloc number in the function cmd_process_type_defs */
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
    | atomic_type product_type_aux                  { list_to_product ($1::$2) }
product_type_aux:
    | STAR atomic_type                              { [$2] }
    | STAR atomic_type product_type_aux             { $2::$3 }

type_expression_args:
    | type_expression                               { [$1] }
    | type_expression COMMA type_expression_args    { $1::$3 }


new_functions:
    /*(* The output of a function definition from the parser consists of a list of
     *   - a function name
     *   - a function type
     *   - a list of clauses, each consisting of
     *       - a LHS given by a term (possibly with "_" variables
     *       - a RHS given by a term
     *)*/
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
    | lhs_term EQUAL rhs_term        { dummy_nb := 0; ($1,$3) }

rhs_term:
    | term { $1 }

term:
    | atomic_term               { $1 }
    | term atomic_term          { App($1,$2,()) }

    | term PLUS atomic_term     { process_addition $1 $3 }

atomic_term:
    | LPAR term RPAR                        { $2 }
    | atomic_term DOT IDU                   { App(Proj($3,None,()), $1,()) }
    | IDL                                   { Var($1,()) }
    | IDU                                   { Const($1,None,()) }
    | ANGEL                                 { Angel () }

    | INT                                   { int_to_term $1 (Const("Zero",None,())) }
    | term_list                             { list_to_term (List.rev $1) (Const("Nil",None,())) }
    | atomic_term DOUBLECOLON atomic_term   { App(App(Const("Cons",None,()),$1,()),$3,()) }
    | tuple                                 { $1 }

tuple:
    | LPAR RPAR                         { tuple_term [] }
    | LPAR term tuple_aux RPAR          { tuple_term ($2::$3) }
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
    | IDL                           { Var($1,()) }
    | LPAR lhs_term RPAR            { $2 }
    | lhs_term DOT IDU              { App(Proj($3,None,()), $1, ()) }
    | lhs_term atomic_pattern       { App($1,$2,()) }

atomic_pattern:
    | DUMMY                                         { dummy() }
    | IDL                                           { Var($1,()) }
    | IDU                                           { Const($1,None,()) }
    | LPAR pattern RPAR                             { $2 }

    | INT                                           { int_to_term $1 (Const("Zero",None,())) }
    | pattern_list                                  { list_to_term (List.rev $1) (Const("Nil",None,())) }
    | atomic_pattern DOUBLECOLON atomic_pattern     { App(App(Const("Cons",None,()),$1,()),$3,()) }
    | atomic_pattern PLUS INT                       { int_to_term $3 $1 }
    | pattern_tuple                                 { $1 }

pattern:
    | atomic_pattern            { $1 }
    | pattern atomic_pattern    { App($1,$2,()) }

pattern_list:
    | LSQBRAC pattern_list_inside RSQBRAC       { $2 } /* FIXME: check priorities... */
    | LSQBRAC RSQBRAC                           { [] }

pattern_list_inside:
    | pattern                                   { [$1] }
    | pattern SEMICOLON pattern_list_inside     { $1::$3 }

pattern_tuple:
    | LPAR RPAR                                 { tuple_term [] }
    | LPAR pattern pattern_tuple_aux RPAR       { tuple_term ($2::$3) }
pattern_tuple_aux:
    | COMMA pattern                         { [$2] }
    | COMMA pattern pattern_tuple_aux       { $2::$3 }


eos:
    | SEMICOLON     {}
    | BLANKLINE     {}

string:
    | IDL { $1 }
    | IDU { $1 }
    | STR { $1 }

int_range:
    | /* nothing */             { [] }
    | INT int_range             { $1::$2 }
    | INT MINUS INT int_range   { (range $1 $3) @ $4 }

