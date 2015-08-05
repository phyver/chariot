open Misc
open State
open Base
open Pretty
open Typing
open Compute
open CheckCoverage
open CheckFunctions
open Explore
open SCTCalls

(* TODO: put all of this in parser.mly *)
(* commands *)
type cmd =
    | CmdCompose of term*term*term*term
    | CmdCompare of term*term*term*term

    | Eof
    | Nothing
    | CmdQuit
    | CmdHelp

    | CmdPrompt of string
    | CmdVerbose of int
    | CmdOption of string*string
    | CmdShow of string
    | CmdEcho of string

    | CmdReduce of term
    | CmdUnfold of term*int
    | CmdExplore of term

    | TypeDef of int * (type_name * (type_expression list) * (const_name * type_expression) list) list
    (* The output of a type definition from the parser consists of
     *   - a bloc number odd/even to distinguish data / codada types
     *   - a list of (possibly) mutual type definitions:
     *        - a type name
     *        - a list of type parameters, all of the form TVar(true,x)
     *        - a list of constants (constructors for data, destructors for codata), with a type
     * No sanity checking is done by the parser, everything is done in the "process_type_defs" function in file "checkTypes.ml"...
     *)

    | FunDef of (var_name * type_expression option * (term * term) list) list
    (* The output of a function definition from the parser consists of a list of
     *   - a function name
     *   - a function type
     *   - a list of clauses, each consisting of
     *       - a LHS given by a term (possibly with "_" variables
     *       - a RHS given by a term
     *)

type explore_cmd =
    | ExpEnd
    | ExpUnfold of int list
    | ExpUnfoldAll

let cmd_reduce env term =
    let t,constraints = infer_type_term env term in
    msg "term: %s" (string_of_term term);
    let term = reduce_all env term in
    msg "result: %s" (string_of_term term);
    msg "of type: %s" (string_of_type t);
    if not (constraints = [])
    then msg "with free variables: %s" (string_of_list " , " (function x,t -> x^" : "^(string_of_type t)) constraints);
    print_newline()

let cmd_unfold env term depth =
    let t,constraints = infer_type_term env term in
    msg "term: %s" (string_of_term term);
    let term = unfold_to_depth env term depth in
    msg "result (at depth %i): %s" depth (string_of_explore_term term);
    msg "of type: %s" (string_of_type t);
    if not (constraints = [])
    then msg "with free variables: %s" (string_of_list " , " (function x,t -> x^" : "^(string_of_type t)) constraints);
    print_newline()

let cmd_show env s =
    if s = "types" then show_types env
    else
    if s = "functions" then show_functions env
    else
    let rec auxt = function
        | [] -> raise Exit
        | (tname,params,n,consts)::_ when s=tname ->
            begin
                if even n
                then print_string "codata\n"
                else print_string "data\n";
                show_data_type env tname params consts;
                print_newline()
            end
        | _::types -> auxt types
    in
    let rec auxf = function
        | [] -> raise Exit
        | (f,m,t,clauses)::_ when s=f ->
            begin
                print_string "val\n"; show_function f t clauses;
                print_newline()
            end
        | _::defs -> auxf defs
    in
    try auxt env.types
    with Exit -> try auxf env.functions with Exit -> print_endline ("*** no type or function " ^ s ^ " in environment\n")







let cmd_unify_type env t1 t2 =
    msg "=======================================================";
    msg "unifying type   %s" (string_of_type t1);
    msg "          and   %s" (string_of_type t2);
    let sigma = unify_type_mgu t1 t2 in
    let t1s = subst_type sigma t1 in
    let t2s = subst_type sigma t2 in
    assert (t1s = t2s);
    msg "       result   %s" (string_of_type t1s);
    msg "          via   %s" (string_of_list "  ;  " (function x,t -> "'"^x^" := "^(string_of_type t)) sigma);
    msg "=======================================================";
    print_newline()

let cmd_unify_term env pattern term =
    msg "=======================================================";
    msg "unifying pattern   %s" (string_of_term pattern);
    msg "        and term   %s" (string_of_term term);
    let new_term = unify_pattern (pattern,pattern) term in
    msg "          result   %s" (string_of_term new_term);
    msg "=======================================================";
    print_newline()

(* let cmd_test env pattern depth = *)
(*     msg "======================================================="; *)
(*     msg "collapsing pattern   %s" (string_of_term pattern); *)
(*     msg "          to depth   %d" depth; *)
(*     let pattern = pattern_to_approx_term pattern in *)
(*     let pattern = collapse_pattern depth pattern in *)
(*     msg "          result   %s" (string_of_approx_term pattern); *)
(*     msg "======================================================="; *)
(*     print_newline() *)

let cmd_compose env l1 r1 l2 r2 =
    msg "  %s => %s    o    %s => %s" (string_of_term l1) (string_of_term r1) (string_of_term l2) (string_of_term r2);
    let l1 = pattern_to_approx_term l1 in
    let r1 = pattern_to_approx_term r1 in
    let l2 = pattern_to_approx_term l2 in
    let r2 = pattern_to_approx_term r2 in
    let l,r = collapsed_compose current_state.bound current_state.depth (l1,r1) (l2,r2) in
    msg "          =  %s => %s" (string_of_approx_term l) (string_of_approx_term r);
    print_newline()


let cmd_compare env l1 r1 l2 r2 =
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

