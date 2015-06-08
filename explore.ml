open Misc
open Base
open Pretty
open Compute
open Typing

let print_term_depth (env:environment) (v:term) (depth:int) : unit
  =
  (* NOTE: not very elegant: I pasted the "print_term" function and added some things... *)
    let rec
      print_paren_term v depth =
        try
            print_term_int v
        with Invalid_argument "print_term_int" ->
            if is_atomic v
            then print_term v depth
            else (print_string "("; print_term v depth; print_string ")")

    and
      print_non_codata_term u depth = match u with
        | Angel -> print_string "⊤"
        | Var(x) -> print_string x
        | Const(c,p) -> print_string c; print_exp p
        | Proj(d,p) -> print_string "." ; print_string d; print_exp p
        | App(v1,v2) -> print_term v1 depth; print_string " "; print_paren_term v2 depth

    and
      print_term v depth =
        try
            print_term_int v
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
                                    print_list "{}" "{" "; " "}" (function d,v -> print_string (d ^ "="); print_term v (depth-1)) fields
                        end
            end
    in
    print_term v depth

