(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
totality checker for recursive definitions involving nested least and
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
    | Struct of (const_name * ('s,'p,'t) raw_term) list * 'p * 't
    | App of ('s,'p,'t) raw_term * ('s,'p,'t) raw_term
    | Sp of 's*'t                       (* special terms for additionnal structure on terms *)

(*************************************************************************
 * the main kinds of terms used are
 *   - plain terms: 's is empty, 'p is unit, 't is unit
 *   - typed terms: 's is empty, 'p is unit, 't is type_expression
 *   - terms: 's is empty, 'p is priority, 't is type_expression
 *   - terms with frozen subterms, used for evaluation: 's is 'x frozen, 'p is unit, 't is unit
 *   - case / struct trees: trees with leafs in typed terms
 *   - approximated term: 's is approximation, 'p is priority, 't is unit
 **********************************************************************)

type priority = int option      (* priority of types and constants: odd for data and even for codata *)
                                (* NOTE: I need an "infinity" priority to deal with unknown approximation on results *)
type empty = { bot: 'a .'a }

(* term with possibly unfolded codata *)
(* TODO: use *)
(* type ('p,'t)frozen_term = int * ((empty,unit,unit) raw_term,unit,unit)raw_term *)
type 'x frozen = Frozen of 'x
type 'x frozen_term = ('x frozen,unit,unit) raw_term

(* term with case and structs *)
type 'v case_struct_tree =
    | CSFail
    | CSLeaf of 'v
    | CSCase of var_name * const_name list * (const_name * (var_name list * 'v case_struct_tree)) list
    | CSStruct of (const_name * 'v case_struct_tree) list
(* definitions of functions with cases and structs *)
type case_struct_def = var_name list * (empty,unit,type_expression) raw_term case_struct_tree

(* type 'v case_sp = *)
(*     | CFail *)
(*     | CLeaf of 'v *)
(*     | CCase of var_name * const_name list * (const_name * (var_name list * 'v case_term)) list *)
(* and 'v case_term = ('v case_sp,unit,type_expression) raw_term *)
(* type case_def = var_name list * (empty,unit,type_expression) raw_term case_term *)


(* SCP terms *)
type weight = Num of int | Infty

type coeff = (priority*weight) list

(* a call from f to g is represented by a rewriting rule
 *   param_1 param_2 ... param_m  =>  arg_1 arg_2 ... arg_n
 * where m is the arity of f and n is the arity of g.
 *  - each param_i is either a constructor pattern or a destructor
 *  - each arg_i i either a constructor pattern (with possible approximations) or a destructor
 *)
type approximation = AppRes of coeff | AppArg of (var_name*coeff) list
type approx_term = (approximation,priority,unit) raw_term
(* type scp_clause = approx_term * approx_term *)
 type scp_pattern = (var_name * approx_term list)
 type scp_clause = scp_pattern * scp_pattern


(* terms from the parser *)
type plain_term = (empty,unit,unit) raw_term

(* terms after typing *)
type typed_term = (empty,unit,type_expression) raw_term

(* terms after priorities have been added *)
type term = (empty,priority,type_expression) raw_term

type function_clause = term * term     (* clause of a function definition *)

(* terms after reduction *)
type computed_term = plain_term frozen_term

(* terms during exploration, frozen subterms are numbered *)
type explore_term = (int*plain_term) frozen_term


type bloc_nb = int      (* number of the block of mutual function definitions *)

(* type for the environment *)
type environment = {
    (* we keep the names of type arguments of a definition in the environment,
     * together with its bloc number and the list of its constants
     * (constructors/destructors)
     * The bloc number is odd for inductive types and even for coinductive types *)
    types:     (type_name * bloc_nb * (type_name list) * const_name list) list         ;

    (* each constant (type constructor/destructor) has a type and a bloc number
     * the bloc number is odd for constructors and even for destructors *)
    constants: (const_name * bloc_nb * type_expression) list                           ;

    (* each function is defined inside a bloc of definitions and has a type and
     * a list of defining clauses *)
    functions: (var_name *
                bloc_nb *
                type_expression *
                function_clause list *
                case_struct_def) list
    }

