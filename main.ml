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

let process_statement = function
    | Eof -> raise Exit
    | Nothing -> ()
    | TypeDef(priority,defs) -> env := process_type_defs !env priority defs
    | FunDef(defs) -> env := process_function_defs !env defs
    | Cmd("show",["types"]) -> showtypes !env
    | Cmd("prompt", [s]) -> prompt := s
    | Cmd(c,_) -> print_string ("*** unknown command: " ^ c ^ "\n")

let loadfile path =
    try
        let f_in = open_in path in
        let lexbuf = Lexing.from_channel f_in in
        let cmds = Parser.statements Lexer.token lexbuf in
        List.iter process_statement cmds
    with
        | Parsing.Parse_error -> print_string "*** parse error\n"; flush_all ()
        | Error err -> print_endline ("*** " ^ err); flush_all ()
        | Sys_error err -> print_endline ("*** " ^ err); flush_all ()


let mainloop () =
    try
        while true
        do
            print_string !prompt; flush_all();
            let lexbuf = Lexing.from_channel stdin in
            flush_all ();
            try
                process_statement (Parser.single_statement Lexer.token lexbuf)
            with
                | Parsing.Parse_error -> print_string "*** parse error\n"; flush_all ()
                | Error err -> print_string ("*** " ^ err ^ "\n"); flush_all ()
        done
    with Exit -> ()

(* let _ = mainloop () *)

let _ =
    for i=1 to (Array.length Sys.argv)-1
    do
        loadfile (Sys.argv.(i));
    done;
    mainloop()
