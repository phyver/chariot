open Parser
open Base
open CheckTypes
open Pretty
open Misc
open Commands

let env = ref { current_priority = 0; types = []; constants = []; functions = []; vars = [] }

let main () =
    try
        while true
        do
            print_string ">>> "; flush_all();
            let lexbuf = Lexing.from_channel stdin in
            try
                match Parser.statement Lexer.token lexbuf with
                    | Eof -> raise Exit
                    | Nothing -> ()
                    | TypeDef(priority,defs) -> env := process_type_defs !env priority defs
                    | Cmd "showtypes" -> showtypes !env
                    | Cmd c -> print_string ("*** unknown command: " ^ c ^ "\n")
            with
                | Parsing.Parse_error -> print_string "*** parse error\n"
                | Error err -> print_string ("*** " ^ err ^ "\n")
        done
    with Exit -> ()

let _ = main ()
