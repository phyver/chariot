open Misc
open Env
open Utils
open Pretty

type structure = Struct of (const_name * struct_term) list
and struct_term = (structure,unit) special_term


let aux_function_counter = ref 0
let new_aux () = incr aux_function_counter; Var("_aux"^(string_of_sub !aux_function_counter),())

let aux_functions = ref []

let remove_match_struct (clauses:(struct_term*struct_term) list)
  : (unit term*struct_term) list
  =

    let arg_counter = ref 0 in
    let new_var () = incr arg_counter; "x"^(string_of_sub !arg_counter) in

    let rec process_arg (pat:struct_term)
      :  unit term * (var_name*struct_term) list
      = match pat with
            | Var(x,()) -> let y=new_var() in Var(y,()),[y,Var(x,())]
            | Angel _ | Daimon _ -> assert false
            | Const(c,p,()) -> Const(c,p,()),[]
            | Proj(d,p,()) -> Proj(d,p,()),[]
            | App(u1,u2) ->
                let u1,sigma1=process_arg u1 in
                let u2,sigma2=process_arg u2 in
                App(u1,u2), sigma1@sigma2
            | Sp(Struct fields,()) -> let y=new_var() in Var(y,()),[y,Sp(Struct fields,())]
    in

    let process_clause (lhs,rhs:struct_term*struct_term)
      : (unit term*struct_term) * (struct_term*struct_term) option
      =
        arg_counter := 0;

        let f,lhs_pattern =
            match explode lhs with f::args -> f,args | [] -> assert false in

        (* we need to change the type of f from struct_term to unit term *)
        let f = match f with Var(f,()) -> Var(f,()) | _ -> assert false in

        (* process the lhs *)
        let lhs_pattern,sigma =
            let tmp = List.map process_arg lhs_pattern in
            List.map fst tmp, List.concat (List.map snd tmp)
        in

        let lhs = implode (f::lhs_pattern) in

        match sigma with
            | [] -> (lhs,rhs) , None
            | sigma ->
                let f_aux = try List.assoc lhs !aux_functions
                            with Not_found ->
                                let f_aux=new_aux() in
                                aux_functions := (lhs,f_aux)::!aux_functions;
                                f_aux
                in
                let args_aux = List.concat (List.map
                                    (function
                                        | y,Var(x,()) -> [Var(y,())]
                                        | y,Sp(Struct fields,()) -> List.map (function d,_ -> App(Proj(d,None,()),Var(y,()))) fields
                                        | _ -> assert false
                                    )
                                    sigma
                               )
                in
                let new_rhs = implode (f_aux::args_aux) in

                let new_args_aux = List.concat (List.map
                                    (function
                                        | y,Var(x,()) -> [Var(x,())]
                                        | y,Sp(Struct fields,()) -> List.map (function _,v -> v) fields
                                        | _ -> assert false
                                    )
                                    sigma
                               )
                in

                let lhs_new_clause = implode (f_aux::new_args_aux) in

                let new_clause = lhs_new_clause, rhs in

                (implode (f::lhs_pattern),new_rhs) , Some new_clause

    in

    todo "remove_match_struct"





let remove_term_struct (clauses:(var_name*unit term*struct_term) list)
  : (var_name*unit term*unit term) list
  = todo "remove_term_struct"
