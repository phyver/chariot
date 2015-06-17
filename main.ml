open Parser
open Base
open CheckTypes
open CheckFunctions
open Compute
open Pretty
open Misc
open Commands
open State


let process_statement = function
    | CmdTest(v,d) -> cmd_print_depth current_state.env v d

    | Eof -> raise Exit
    | CmdQuit -> raise Exit
    | Nothing -> ()

    | CmdShow(s) -> cmd_show current_state.env s
    | CmdPrompt(s) -> current_state.prompt <- s
    | CmdVerbose(v) -> current_state.verbose <- v

    | CmdReduce(t) -> cmd_reduce current_state.env t

    | TypeDef(priority,defs) -> current_state.env <- process_type_defs current_state.env priority defs
    | FunDef(defs) -> current_state.env <- process_function_defs current_state.env defs


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
    while true
    do
        print_string current_state.prompt; flush_all();
        let lexbuf = Lexing.from_channel stdin in
        flush_all ();
        try
            process_statement (Parser.single_statement Lexer.token lexbuf)
        with
            | Parsing.Parse_error -> print_string "*** parse error\n"; flush_all ()
            | Error err -> print_string ("*** " ^ err ^ "\n"); flush_all ()
    done

let _ =
    try
        for i=1 to (Array.length Sys.argv)-1
        do
            print_string ("=== loading file " ^ Sys.argv.(i)); flush_all ();
            loadfile (Sys.argv.(i));
            print_endline "  OK ";
        done;
        mainloop()
    with Exit -> ()
