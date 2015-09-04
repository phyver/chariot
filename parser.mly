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
open Rewrite
open ComputeCaseStruct
open Explore
open SCTCalls
open Coverage
open FunctionDefs
open TypeDefs
open StructPattern

(* transform a struct_term without structs into a unit term *)
let parsed_to_plain v
  = map_raw_term (fun _ -> error "no structure allowed for this command") id id v
let parsed_to_sct v
  = let v = parsed_to_plain v in
    let v = map_raw_term (fun s->s.bot) (k None) id v in
    let v = pattern_to_approx_term v in
    term_to_sct_pattern v

(* transform a list of types into the product *)
let list_to_product (l:type_expression list) : type_expression
  = let n = List.length l in
    Data("prod_" ^ (string_of_int n), l)

(* transforms an integer into a term by adding Succ constructors in front of u *)
let rec int_to_term (n:int) (u:(unit,unit) struct_term) : (unit,unit) struct_term
  = if n=0
    then u
    else int_to_term (n-1) (App(Const("Succ",(),()),u))

(* transform an addition u+v into either an application of the "add" function or, when v is an natural number, into Succ(... Succ (u) *)
let process_addition u v
  = let rec add_aux u v
      = match v with
            | Const("Zero", _,()) -> u
            | App(Const("Succ", p,()), v) -> add_aux (App(Const("Succ",p,()),u)) v
            | _ -> raise Exit
    in
    try add_aux u v
    with Exit -> App(App(Var("add",()),u),v)

(* tranform a list of terms into the corresponding list by adding Cons constructors in front of u *)
let rec list_to_term (l:(unit,unit) struct_term list) (u:(unit,unit) struct_term) : (unit,unit) struct_term
  = match l with
        | [] -> u
        | v::l -> list_to_term l (App(App(Const("Cons",(),()),v),u))

(* tranform a list of terms into the corresponding tuple *)
let tuple_term (l:(unit,unit) struct_term list) : (unit,unit) struct_term =
    let n = List.length l in
    app (Const("Tuple_" ^ (string_of_int n),(),())) l


(* a reference to number dummy arguments in terms *)
let dummy_nb = ref 0
(* generate a fresh dummy variable *)
let dummy () = incr dummy_nb; Var("_" ^ (string_of_sub !dummy_nb),())

(* execute a statement and catch appropriate errors *)
let exec_cmd (cmd:unit->unit) : unit
  = try cmd ()
    with
        | Error err ->
            if option "continue_on_error"
            then errmsg "%s" err
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
    try
        let _,params,consts = env_type_assoc current_state.env s in
        show_data_type current_state.env s params consts;
        print_newline()
    with Not_found ->
        try
            let _,t,clauses,cst = env_fun_assoc current_state.env s in
            print_endline "val";
            show_function s t clauses cst;
            print_newline()
        with Not_found -> errmsg "no type or function %s in environment" s


let cmd_show_help ()
  = print_list "| " "\n| " "\n\n" print_string [
        "";
        "chariot: a language with arbitrary nested inductive and coinductive types";
        "";
        "TODO";
        "";
    ]

let cmd_show_type (term:(unit,unit) struct_term) : unit
  = let term = parsed_to_plain term in
    let t,term,context = infer_type_term current_state.env term in
    msg "%s" (string_of_typed_term term);
    if not (context = [])
    then msg "with free variables: %s" (string_of_list " , " (function x,t -> x^" : "^(string_of_type t)) context)

(* reduce a term and show the result *)
let cmd_reduce (term:(unit,unit) struct_term) : unit
  = let term = parsed_to_plain term in
    let t,term,context = infer_type_term current_state.env term in
    msg "term: %s" (string_of_plain_term term);
    (* let term = rewrite_all current_state.env term in *)
    let term = reduce current_state.env term in
    current_state.last_term <- Some term;
    current_state.last_explore <- None;
    msg "result: %s" (string_of_plain_term term);
    msg "of type: %s" (string_of_type t);
    if not (context = [])
    then msg "with free variables: %s" (string_of_list " , " (function x,t -> x^" : "^(string_of_type t)) context);
    print_newline()

let cmd_show_last ()
  = match current_state.last_term with
        | None -> ()
        | Some t ->
            msg "last result: %s" (string_of_plain_term t)

(* unfold a term by expanding lazy subterms up-to a given depth, and show the result *)
let cmd_unfold_initial (term:(unit,unit) struct_term) (depth:int) : unit
  = let term = parsed_to_plain term in
    let t,term,context = infer_type_term current_state.env term in
    let term = unfold_to_depth current_state.env term depth in
    msg "%s" (string_of_unfolded_term term);
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
        msg "%s" (string_of_unfolded_term t)
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

let test_unify_term (pattern:parsed_term) (term:parsed_term) =
    let term = parsed_to_plain term in
    let pattern = parsed_to_plain pattern in
    let _,pattern,_ = infer_type_term current_state.env pattern in
    let _,term,_ = infer_type_term current_state.env term in
    msg "unifying pattern   %s" (string_of_plain_term pattern);
    msg "        and term   %s" (string_of_plain_term term);
    let new_term = unify_pattern (pattern,pattern) term in
    msg "          result   %s" (string_of_plain_term new_term);
    print_newline()

let test_compose l1 r1 l2 r2 =
    let l1 = parsed_to_sct l1 in
    let r1 = parsed_to_sct r1 in
    let l2 = parsed_to_sct l2 in
    let r2 = parsed_to_sct r2 in
    msg "  %s    o    %s" (string_of_sct_clause (l1,r1)) (string_of_sct_clause (l2,r2));
    let l,r = collapsed_compose current_state.bound current_state.depth (l1,r1) (l2,r2) in
    msg "          =  %s" (string_of_sct_clause (l,r));
    print_newline()

let test_compare l1 r1 l2 r2 =
    let l1 = parsed_to_sct l1 in
    let r1 = parsed_to_sct r1 in
    let l2 = parsed_to_sct l2 in
    let r2 = parsed_to_sct r2 in
    let l1,r1 = collapse_clause current_state.bound current_state.depth (l1,r1) in
    let l2,r2 = collapse_clause current_state.bound current_state.depth (l2,r2) in
    msg "  %s    ≥    %s" (string_of_sct_clause (l1,r1)) (string_of_sct_clause (l2,r2));
    if approximates (l1,r1) (l2,r2)
    then msg "        TRUE"
    else msg "        FALSE";
    print_newline()

let test_collapse (p:parsed_term) =
    let p = parsed_to_sct p in
    let q = collapse_pattern current_state.depth p in
    let q = collapse_weight_in_pattern current_state.bound q in
    msg "  collapse of   %s   is   %s" (string_of_sct_pattern p) (string_of_sct_pattern q);
    print_newline()

%}

%token EQUAL COLON SEMICOLON BLANKLINE LPAR RPAR COMMA PIPE DOT DUMMY ANGEL DAIMON ARROW PLUS MINUS STAR GT
%token LSQBRAC RSQBRAC LCBRAC RCBRAC DOUBLECOLON DOUBLEARROW SHARP DOLLAR
%token DATA CODATA WHERE AND VAL
%token CMDHELP CMDQUIT CMDSHOW CMDSET
%token CMDUNFOLD CMDREDUCE CMDUNFOLD CMDECHO CMDSHOWTYPE
%token TESTUNIFYTYPES TESTUNIFYTERMS TESTCOMPOSE TESTCOMPARE TESTCOLLAPSE
%token EOF
%token <string> IDU IDL STR TVAR
%token <int> INT

%right ARROW DOUBLECOLON DOLLAR SHARP
%left DOT PLUS


%start single_statement
%start statements

%type <unit> statements
%type <unit> single_statement

%type <int * (type_name * (type_expression list) * (const_name * type_expression) list) list> new_types
%type <(type_name * (type_expression list) * (const_name * type_expression) list) list> type_defs
%type <type_name * (type_expression list) * (const_name * type_expression) list> type_def

%type <var_name * type_expression option * (parsed_term * parsed_term) list> function_def
%type <(var_name * type_expression option * (parsed_term * parsed_term) list ) list> function_defs

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
    | CMDSHOWTYPE term                                  { fun () -> cmd_show_type $2 }
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

    | TESTUNIFYTYPES type_expression AND type_expression                 { fun () -> test_unify_type $2 $4 }
    | TESTUNIFYTERMS term AND term                                       { fun () -> test_unify_term $2 $4 }
    | TESTCOLLAPSE term                                                  { fun () -> test_collapse $2 }
    | TESTCOMPOSE term DOUBLEARROW term AND term DOUBLEARROW term        { fun () -> test_compose $2 $4 $6 $8 }
    | TESTCOMPARE term DOUBLEARROW term AND term DOUBLEARROW term        { fun () -> test_compare $2 $4 $6 $8 }


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
    | term EQUAL term        { dummy_nb := 0; ($1,$3) }

term:
    | app_term                  { $1 }

    /* syntactic sugar */
    | term PLUS term            { process_addition $1 $3 }
    | IDU SHARP term            { Sp(Struct [$1,$3], ()) }
    | term DOLLAR term          { App($1,$3) }

app_term:
    | app_term atomic_term      { App($1,$2) }
    | atomic_term               { $1 }

atomic_term:
    | LPAR term RPAR                        { $2 }
    | atomic_term DOT IDU                   { App(Proj($3,(),()), $1) }
    | IDL                                   { Var($1,()) }
    | DUMMY                                 { dummy() }
    | IDU                                   { Const($1,(),()) }
    | ANGEL                                 { Angel() }
    | DAIMON                                { Daimon() }

    /* syntactic sugar */
    | INT                                   { int_to_term $1 (Const("Zero",(),())) }
    | term_list                             { list_to_term (List.rev $1) (Const("Nil",(),())) }
    | atomic_term DOUBLECOLON atomic_term   { App(App(Const("Cons",(),()),$1),$3) }
    | tuple                                 { $1 }
    | LCBRAC struct_term RCBRAC             { Sp(Struct $2, ()) }

struct_term:
    | /*nothing*/                               { [] }
    | IDU EQUAL term                            { [$1,$3] }
    | IDU EQUAL term SEMICOLON struct_term      { ($1,$3)::$5 }


tuple:
    | LPAR RPAR                         { tuple_term [] }
    | LPAR term tuple_aux RPAR          { tuple_term ($2::$3) }
tuple_aux:
    | COMMA term                        { [$2] }
    | COMMA term tuple_aux              { $2::$3 }


term_list:
    | LSQBRAC term_list_inside RSQBRAC  { $2 }
    | LSQBRAC RSQBRAC                   { [] }

term_list_inside:
    | term                              { [$1] }
    | term SEMICOLON term_list_inside   { $1::$3 }

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

