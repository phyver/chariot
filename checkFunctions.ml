open Base
open Misc
open Pretty
open Typing

let var_counter = ref 0


(* check tha all the functions are different *)
let check_uniqueness_functions funs =
    match uniq funs with
        | None -> ()
        | Some(f) -> raise @$ Error ("*** function " ^ f ^ " is defined more than once")


let check_new_funs_different_from_old new_funs old_funs =
    match common new_funs old_funs with
        | None -> ()
        | Some f -> raise @$ Error ("*** function " ^ f ^ " already exists")

let rec get_function_name = function
    | Var(f) -> f
    | Constant c -> raise @$ Error ("*** " ^ c ^ " is not a function name")
    | Apply(Constant _, p) -> get_function_name p
    | Apply(p,_) -> get_function_name p

let rec get_variables_from_lhs = function
    | Var(x) -> [x]
    | Constant _ -> []
    | Apply(t1,t2) -> (get_variables_from_lhs t1) @ (get_variables_from_lhs t2)

let rec infer_type_of_variables env vars lhs_pattern
  =
      print_string "infer_type_of_variables: ";
      print_term lhs_pattern;
      print_newline();

    match lhs_pattern with
    | Apply(e1,e2) -> (* start with t1, then (infer_type t1), it should be T1 -> T2, unify (infer_type t2) and T1 *)
        begin
            let sigma = infer_type_of_variables env vars e1 in
    print_string "sigma = "; List.iter (function x,t -> print_string (x ^ ": "); print_type env t; print_newline()) sigma; print_newline();
            let vars = List.map (second (subst_type sigma)) vars in
            let t1,sigma1 = infer_type e1 env vars in
    print_string "   "; print_term e1; print_string " has type "; print_type env t1; print_newline ();
            let t2,sigma2 = infer_type e2 env vars in
    print_string "   "; print_term e2; print_string " has type "; print_type env t2; print_newline ();
            match t1 with
                | Arrow(tt1,tt2) ->
                    begin
    print_string "unify "; print_type env tt1; print_string " and "; print_type env t2; print_newline();
                        sigma @ sigma1 @ sigma2 @ (unify_type tt1 t2)
                    end
                | _ ->  raise (Error "not function type")
        end
    | Constant(c) -> []
    | Var(x) -> []


let process_function_defs (env:environment)
                          (defs:(var_name * type_expression * (term * term) list) list)
  =
    (* check that the functions are all different *)
    let new_functions = List.rev_map (function f,_,_ -> f) defs in
    check_uniqueness_functions new_functions;

    (* check that new function are different from old ones *)
    let old_functions = List.rev_map (function f,_,_,_ -> f) env.functions in
    check_new_funs_different_from_old new_functions old_functions;

    let process_single_clause (f:var_name) (t:type_expression) (lhs_pattern,rhs_term:term*term) =
        (* get function from LHS and check it is equal to f *)
        let _f = get_function_name lhs_pattern in
        if not (_f = f) then raise @$ Error ("*** function names " ^ f ^ " and " ^ _f ^ " do not match");

        (* get variables *)
        let vars = get_variables_from_lhs lhs_pattern in
        (match uniq vars with
            | None -> ()
            | Some(x) -> raise @$ Error ("*** variable " ^ x ^ " appears more than once"));

        (* add types *)
        let vars = List.map (fun x -> if x=f then (f,t) else (incr var_counter; (x,TVar("x"^(string_of_int !var_counter))))) vars in

        List.iter (function x,t -> Printf.printf "var %s: " x; print_type env t; print_newline()) vars;
        print_string "\n\n";

        (* unify with t *)
        let sigma = infer_type_of_variables env vars lhs_pattern in

        List.iter (function x,t -> print_string ("PARAM " ^ x ^ ": "); print_type env t; print_newline()) sigma;
        print_string "\n\n";

        let vars = List.map (second @$ subst_type sigma) vars in

        List.iter (function x,t -> print_string ("new var " ^ x ^ ": "); print_type env t; print_newline()) vars;
        print_string "----------\n\n";


        ()
    in


    let process_single_def (f:var_name) (t:type_expression) (clauses:(term*term) list) =

        (* make type parameters non unifiable *)
        List.iter (process_single_clause f t) clauses;

        ()
    in



    List.iter (function f,t,clauses -> process_single_def f t clauses) defs;

      env
