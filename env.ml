(*========================================================================
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
========================================================================*)


(*
 * the types for representing
 *   - types
 *   - terms
 *   - environments
 *)

exception Error of string
let error s = raise (Error s)

exception UnificationError of string
let unificationError s = raise (UnificationError s)


(* types for type expressions and substitutions *)
type type_name = string
type type_expression =
    | TVar of type_name
    | Data of type_name * (type_expression list)
    | Arrow of type_expression * type_expression
type type_substitution = (type_name * type_expression) list


(* type for expressions *)
type const_name = string
type var_name = string
type ('s,'p,'t) raw_term =      (* 's is used to add features to terms, 'p is used to add priorities and 't is used to put types on subterms *)
    | Angel of 't                       (* generic meta variable, living in all types *)
    | Daimon of 't                      (* generic "bad" (possibly looping) term, living in all types *)
    | Var of var_name*'t
    | Const of const_name * 'p *'t      (* constructor, with a priority *)
    | Proj of const_name * 'p *'t       (* destructor, with a priority *)
    | App of ('s,'p,'t) raw_term * ('s,'p,'t) raw_term
    | Sp of 's*'t                       (* special terms for additionnal structure on terms *)

(*************************************************************************
 * the main kinds of terms used are
 *   - parsed terms: 's is structure, 'p is unit, 't is unit
 *   - plain terms: 's is empty, 'p is unit, 't is unit
 *   - typed terms: 's is empty, 'p is unit, 't is type_expression
 *   - terms: 's is empty, 'p is int, 't is type_expression
 *   - unfolded terms: 's is explore_struct, 'p is int, 't is type_expression (TODO: or possibly 't is unit???)
 *   - case / struct trees: trees with leafs in typed terms
 *   - approximated term: 's is approximation, 'p is int, 't is unit
 *
 * TODO: define those types, and use them
 **********************************************************************)

type priority = int option      (* priority of types and constants: odd for data and even for codata *)
                                (* NOTE: I need an "infinity" priority to deal with unknown approximation on results *)
type empty = { bot: 'a .'a }

(* terms with structures *)
type ('p,'t) structure = Struct of (const_name * ('p,'t) struct_term) list
 and ('p,'t) struct_term = (('p,'t) structure,'p,'t) raw_term

(* term with possibly unfolded codata *)
(* FIXME: once I have typed terms, I should remove the type expression from the unfolded_struct type *)
type ('p,'t) fold_struct =
    | Folded of int * (empty,'p,'t) raw_term
    | Unfolded of (const_name * var_name list * ('p,'t) unfolded_term) list
 and ('p,'t) unfolded_term = (('p,'t) fold_struct,'p,'t) raw_term

(* term with case and structs *)
type 't case_struct_tree =
    | CSFail
    | CSLeaf of 't
    | CSCase of var_name * (const_name * (var_name list * 't case_struct_tree)) list
    | CSStruct of (const_name * ((var_name list) * 't case_struct_tree)) list
(* definitions of functions with cases and structs *)
type case_struct_def = var_name list * (empty,unit,type_expression) raw_term case_struct_tree


(* SCT terms *)
type weight = Num of int | Infty

(* a call from f to g is represented by a rewriting rule
 *   param_1 param_2 ... param_m  =>  arg_1 arg_2 ... arg_n
 * where m is the arity of f and n is the arity of g.
 *  - each param_i is either a constructor pattern or a destructor
 *  - each arg_i i either a constructor pattern (with possible approximations) or a destructor
 *)
type approximation = AppRes of priority * weight | AppArg of (priority * weight * var_name) list
type approx_term = (approximation,priority,unit) raw_term
(* type sct_clause = approx_term * approx_term *)
 type sct_pattern = (var_name * approx_term list)
 type sct_clause = sct_pattern * sct_pattern
(* TODO: use
 * type approx_term = (approximation,type_expression) raw_term
 * type sct_clause = (var_name * approx_term list) * (var_name * approx_term list)
 * ??? *)




(* terms from the parser *)
type parsed_term = (unit,unit) struct_term

(* terms after removal of structures *)
type plain_term = (empty,unit,unit) raw_term

(* terms after typing *)
type typed_term = (empty,unit,type_expression) raw_term

(* terms after priorities have been added *)
type priority_term = (empty,priority,type_expression) raw_term


(* type 't term = (empty,priority,'t) raw_term *)
(* type 't term_substitution = (var_name * 't term) list *)

type bloc_nb = int      (* number of the block of mutual function definitions *)

(* TODO: use type 't pattern = var_name * 't term list *)
type function_clause = priority_term * priority_term     (* clause of a function definition *)


(* type for the environment *)
type environment = {
    (* we keep the names of type arguments of a definition in the environment,
     * together with its bloc number and the list of its constants
     * (constructors/destrucors) *)
    types:     (type_name * bloc_nb * (type_name list) * const_name list) list         ;

    (* each constant (type constructor/destructor) has a type and a bloc number
     * the bloc number is odd for constructors and even for destructors *)
    (* TODO: use separate lists ? *)
    constants: (const_name * bloc_nb * type_expression) list                           ;

    (* each function is defined inside a bloc of definitions and has a type and
     * a list of defining clauses *)
    functions: (var_name *
                bloc_nb *
                type_expression *
                function_clause list *
                case_struct_def) list
    }

