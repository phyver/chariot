open Base
open Pretty
open Typing
open Compute

(* commands *)
type cmd =
    | Eof
    | Nothing

    | CmdQuit
    | CmdPrompt of string
    | CmdUnifyType of type_expression*type_expression
    | CmdUnifyTerm of term*term
    | CmdInfer of term
    | CmdShow of string
    | CmdReduce of term

    | TypeDef of priority * (type_name * (type_expression list) * (const_name * type_expression) list) list
    (* The output of a type definition from the parser consists of
     *   - a priority odd/even to distinguish data / codada types
     *   - a list of (possibly) mutual type definitions:
     *        - a type name
     *        - a list of type parameters, all of the form TVar(true,x)
     *        - a list of constants (constructors for data, destructors for codata), with a type
     * No sanity checking is done by the parser, everything is done in the "process_type_defs" function in file "checkTypes.ml"...
     *)

    | FunDef of (var_name * type_expression * (term * term) list) list
    (* The output of a function definition from the parser consists of a list of
     *   - a function name
     *   - a function type
     *   - a list of clauses, each consisting of
     *       - a LHS given by a term (possibly with "_" variables
     *       - a RHS given by a term
     *)


let cmd_unify_type env t1 t2 =
    print_string "=======================================================\n";
    print_string "unifying type   ";
    print_type env t1;
    print_string "\n          and   ";
    print_type env t2;
    print_newline();
    let sigma = unify_type t1 t2 in
    let t1s = subst_type sigma t1 in
    let t2s = subst_type sigma t2 in
    assert (t1s = t2s);
    print_string "       result   ";
    print_type env t1s;
    print_newline();
    print_string "          via   ";
    print_list "''" "" "  ;  " "" (function x,t -> print_string ("'" ^ x ^ " := "); print_type env t) sigma;
    print_newline();
    print_string "=======================================================\n";
    print_newline()

let cmd_infer_type env u vars =
    print_string "=======================================================\n";
    print_string "     the term   ";
    print_term env u;
    print_newline();
    let t,sigma = infer_type u env vars in
    print_string "   is of type   ";
    print_type env t;
    print_newline();
    print_string "         when   ";
    print_list "''" "" "  ;  " "" (function x,t -> print_string (x ^ " : "); print_type env t) sigma;
    print_newline();
    print_string "=======================================================\n";
    print_newline ()

let cmd_unify_term env pattern term =
    print_string "=======================================================\n";
    print_string "unifying pattern   ";
    print_term env pattern;
    print_string "\n        and term   ";
    print_term env term;
    print_newline();
    let f = CheckFunctions.get_function_name pattern in
    let sigma = unify_pattern pattern term f in
    let new_term = subst_term pattern sigma in
    assert (new_term = term);
    print_string "          result   ";
    print_list "''" "" "  ;  " "" (function x,t -> print_string (x ^ " := "); print_term env t) sigma;
    print_newline();
    print_string "=======================================================\n";
    print_newline()

let cmd_reduce env term =
    print_string "reducing: ";
    print_term env term;
    print_newline();
    print_string "  result: ";
    print_term env (reduce_all env term);
    print_newline();
    print_newline()

