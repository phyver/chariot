open Base
open Pretty
open Typing
open Compute
open CheckCoverage
open CheckFunctions
open Explore

(* commands *)
type cmd =
    | CmdTest of term*int

    | Eof
    | Nothing
    | CmdQuit
    | CmdHelp

    | CmdPrompt of string
    | CmdVerbose of int
    | CmdOption of string*bool
    | CmdShow of string

    | CmdReduce of term
    | CmdExplore of term

    | TypeDef of priority * (type_name * (type_expression list) * (const_name * type_expression) list) list
    (* The output of a type definition from the parser consists of
     *   - a priority odd/even to distinguish data / codada types
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
    (* let term = put_priority env term in *)
    let t,constraints = infer_type_term env term in
    print_string "\tresult: ";
    print_term (reduce_all env term);
    print_newline();
    print_string "\tof type: "; print_type t; print_newline();
    print_list "" "\twith free variables " "  ,  " "\n" (function x,t -> print_string (x ^ " : "); print_type t) constraints;
    print_newline()

let cmd_show env s =
    if s = "types" then show_types env
    else
    if s = "functions" then show_functions env
    else
    let rec auxt = function
        | [] -> raise Exit
        | (tname,params,priority,consts)::_ when s=tname ->
            begin
                if priority mod 2 = 0
                then print_string "codata\n"
                else print_string "data\n";
                show_data_type env tname params priority consts;
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
    print_string "=======================================================\n";
    print_string "unifying type   ";
    print_type t1;
    print_string "\n          and   ";
    print_type t2;
    print_newline();
    let sigma = unify_type_mgu t1 t2 in
    let t1s = subst_type sigma t1 in
    let t2s = subst_type sigma t2 in
    assert (t1s = t2s);
    print_string "       result   ";
    print_type t1s;
    print_newline();
    print_string "          via   ";
    print_list "''" "" "  ;  " "" (function x,t -> print_string ("'" ^ x ^ " := "); print_type t) sigma;
    print_newline();
    print_string "=======================================================\n";
    print_newline()

let cmd_unify_term env pattern term =
    print_string "=======================================================\n";
    (* let pattern = put_priority env pattern in *)
    (* let term = put_priority env term in *)
    print_string "unifying pattern   ";
    print_term pattern;
    print_string "\n        and term   ";
    print_term term;
    print_newline();
    let new_term = unify_pattern (pattern,pattern) term in
    print_string "          result   ";
    print_term new_term;
    print_newline();
    print_string "=======================================================\n";
    print_newline()

let cmd_exhaustive_function env f =
    print_string "=======================================================\n";
    print_string ("checking if definition " ^ f ^ " is exhaustive\n");
    if exhaustive env (get_function_clauses env f)
    then print_string "OK"
    else print_string "PROBLEM";
    print_newline();
    print_string "=======================================================\n";
    print_newline()

let cmd_print_depth env t depth =
    print_string "=======================================================\n";
    (* let t = put_priority env t in *)
    explore_term_depth env t depth;
    print_newline();
    print_string "=======================================================\n";
    print_newline()
