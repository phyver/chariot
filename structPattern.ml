open Misc
open Env
open Utils
open State
open Pretty

type structure = Struct of (const_name * struct_term) list
and struct_term = (structure,unit) special_term

let rec string_of_struct () (Struct fields)
  = fmt "{ %s }" (string_of_list " ; " (function d,t -> fmt "%s = %s" d (string_of_struct_term t) ) fields)
and
  string_of_struct_term t = string_of_special_term () string_of_struct t

let rec subst_struct_term sigma v
    = match v with
        | Angel _ | Daimon _ | Const _ | Proj _ -> v
        | App(v1,v2) -> App(subst_struct_term sigma v1, subst_struct_term sigma v2)
        | Var(x,()) -> (try List.assoc x sigma with Not_found -> v)
        | Sp(Struct fs,()) -> Sp(Struct (List.map (function d,v -> d,subst_struct_term sigma v) fs),())

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

    let process_clause_aux (lhs,rhs:struct_term*struct_term)
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


        if List.for_all (function _,Var _ -> true | _,_ -> false) sigma
        then begin
            (map_special_term (fun _ -> assert false) identity lhs, rhs) , None
        end
        else
            let lhs = implode (f::lhs_pattern) in
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

    let rec process_clause (cl:struct_term*struct_term)
      : (unit term*struct_term) list
      =
        match process_clause_aux cl with
            | cl,None ->
                (* debug "finished with %s => %s\n" (string_of_term (fst cl)) (string_of_struct_term (snd cl)); *)
                [cl]
            | cl,Some cl' ->
                (* debug "new processed clause: %s => %s" (string_of_term (fst cl)) (string_of_struct_term (snd cl)); *)
                (* debug "new clause to process: %s => %s\n" (string_of_struct_term (fst cl')) (string_of_struct_term (snd cl')); *)
                cl::(process_clause cl')
    in

    List.concat (List.map process_clause clauses)







let remove_term_struct (clauses:(unit term*struct_term) list)
  : (unit term*unit term) list
  =
    List.map (function lhs,rhs -> lhs,map_special_term (fun _ -> assert false) identity rhs) clauses

let remove_struct_defs (defs:(var_name * type_expression option * (struct_term*struct_term) list) list)
  : (var_name * type_expression option * (unit term*unit term) list) list
  =
    let types = List.map (function f,t,_ -> f,t) defs in
    let clauses = List.concat (List.map (function f,_,clauses -> clauses) defs) in
    let new_clauses = remove_match_struct clauses in
    let new_clauses = remove_term_struct new_clauses in
    let new_defs = List.map (function lhs,rhs -> get_function_name lhs, (lhs,rhs)) new_clauses in
    let new_defs = partition (function f,_ -> f) new_defs in
    List.map
        (function
            | [] -> assert false
            | ((f,_)::_) as clauses ->
                let t = (try List.assoc f types with Not_found -> None) in
                f,t,List.map (function _,cl -> cl) clauses)
        new_defs

