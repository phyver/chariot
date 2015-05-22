open Tools
open Parser
open AbstractSyntax

let env = ref { types = []; consts = []; vars = [] }

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
                    | TypeDef defs -> env := process_type !env defs
            with
                | Parsing.Parse_error -> print_string "*** parse error\n"
                | Error err -> print_string ("*** " ^ err ^ "\n")
        done
    with Exit -> ()

let _ = main ()
