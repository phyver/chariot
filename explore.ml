open Misc
open Base
open Pretty
open Compute
open Typing

let print_term_depth (env:environment) (v:term) (depth:int) : unit
  =
    let rec
      print_term_int u depth =
        let rec aux n v =
            match v with
            | Const("Zero",_) -> n,None
            | App(Const("Succ",_),v) -> aux (n+1) v
            | _ -> n,Some v
        in
            match aux 0 u with
                | n,None -> print_int n
                | 0,Some v -> raise (Invalid_argument "print_term_int")
                | n,Some v -> print_term v depth; print_string "+"; print_int n

    and
      print_paren_term v depth =
        try
            print_term_int v depth
        with Invalid_argument "print_term_int" ->
            if is_atomic v
            then print_term v depth
            else (print_string "("; print_term v depth; print_string ")")

    and
      print_non_codata_term u depth = match u with
        | Angel -> print_string "⊥"
        | Var(x) -> print_string x
        | Const(c,p) -> print_string c; print_exp p
        | Proj(d,p) -> print_string "." ; print_string d; print_exp p
        | App(v1,v2) -> print_term v1 depth; print_string " "; print_paren_term v2 depth

    and
      print_term v depth =
        try
            print_term_int v depth
        with Invalid_argument "print_term_int" ->
            begin
                match infer_type env v [] with
                    | Arrow _,_ | TVar _,_ -> print_non_codata_term v depth
                    | Data(t,_),_ ->
                        begin
                            let p = get_type_priority env t in
                            if p mod 2 = 1
                            then print_term v depth
                            else
                                if depth = 0 then print_string "..."
                                else
                                    let consts = get_type_constants env t in
                                    let fields = List.map (fun d -> d, reduce_all env (App(Proj(d,p),v))) consts in
                                    print_list "{}" "{" " ; " "}" (function d,v -> print_string (d ^ " = "); print_term v (depth-1)) fields

                        end
            end
    in
    print_term v depth

    (* let rec *)
    (*   print_paren_term v depth = *)
    (*     try *)
    (*         print_term_int v *)
    (*     with Invalid_argument "print_term_int" -> *)
    (*       match v with *)
    (*         | App(_,[]) -> print_term v depth *)
    (*         | v -> print_string "("; print_term v depth; print_string ")" *)

    (* and *)
    (*   print_atomic_term u depth = match u with *)
    (*     | Angel -> print_string "⊥" *)
    (*     | Var(x) -> print_string x *)
    (*     | Const(c,p) -> print_string c; print_exp p *)
    (*     | Proj(u,d,p) -> print_paren_term u depth; print_string "." ; print_string d; print_exp p *)
    (* and *)
    (*   print_term v depth = *)
    (*     let (App(u,args)) = v in *)
    (*     try *)
    (*         print_term_int v *)
    (*     with Invalid_argument "print_term_int" -> *)
    (*         begin *)
    (*             match infer_type env v [] with *)
    (*                 | Arrow _,_ | TVar _,_ -> print_atomic_term u depth; print_list "" " " " " "" (fun v -> print_paren_term v depth) args *)
    (*                 | Data(t,_),_ -> *)
    (*                     begin *)
    (*                         let p = get_type_priority env t in *)
    (*                         if p mod 2 = 1 *)
    (*                         then (print_atomic_term u depth; print_list "" " " " " "" (fun v -> print_paren_term v depth) args) *)
    (*                         else *)
    (*                             if depth = 0 then print_string "..." *)
    (*                             else *)
    (*                                 let consts = get_type_constants env t in *)
    (*                                 let fields = List.map (fun d -> d, reduce_all env (App(Proj(v,d,p),[]))) consts in *)
    (*                                 print_list "{}" "{" " ; " "}" (function d,v -> print_string (d ^ " = "); print_term v (depth-1)) fields *)

    (*                     end *)
    (*         end *)

    (* in print_term (reduce_all env v) depth *)
