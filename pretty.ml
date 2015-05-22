open Tools
open AbstractSyntax

let verbose = ref 0

let print_constant (c:term_constant) =
    print_string c.name;
    if !verbose>0 then print_exp c.priority

(* let rec print_type = function *)
(*     | Var t -> print_string t *)
(*     | Type(t,args) -> *)
(*             print_string t.name; *)
(*             if !verbose>0 then print_exp t.priority; *)
(*             print_list "(" "," ")" print_type args *)

