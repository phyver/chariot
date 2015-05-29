open Parser
open Base
open CheckTypes
open CheckFunctions
open Pretty
open Misc
open Commands

let env = ref { current_priority = 0; types = []; constants = []; functions = []; vars = [] }
let prompt = ref ">>> "

let istty () =
  print_endline (
    if Unix.isatty Unix.stdin
    then "Input comes from tty."
    else "Input doesn't come from tty."
  )

let main () =
    try
        while true
        do
            print_string !prompt; flush_all();
            let lexbuf = Lexing.from_channel stdin in
            try
                match Parser.statement Lexer.token lexbuf with
                    | Eof -> raise Exit
                    | Nothing -> ()
                    | TypeDef(priority,defs) -> env := process_type_defs !env priority defs
                    | FunDef(defs) -> env := process_function_defs !env defs
                    | Cmd("show",["types"]) -> showtypes !env
                    | Cmd("prompt", [s]) -> prompt := s
                    | Cmd(c,_) -> print_string ("*** unknown command: " ^ c ^ "\n")
            with
                | Parsing.Parse_error -> print_string "*** parse error\n"
                | Error err -> print_string ("*** " ^ err ^ "\n")
        done
    with Exit -> ()

let _ = main ()
