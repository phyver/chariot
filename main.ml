open Parser
open Base
open CheckTypes
open CheckFunctions
open Compute
open Explore
open Pretty
open Misc
open Commands
open State

let print_help () =
    print_list "" "| " "\n| " "\n\n" print_string [
        "";
        "chariot: a language with arbitrary nested inductive and coinductive types";
        "";
        "TODO";
        "";
    ]

let explore_loop env t =
    print_list "" "| " "\n| " "\n\n" print_string [
        "Explore mode:";
        "  you can unfold a (coinductive) datastructure interactively";
        "  by inputing the corresponding indices";
        "";
        "  ':quit' to quit the explore mode"
    ];
    let t = put_priority env t in
    let t = ref (term_to_explore env t) in
    try
        while true
        do
            print_string "→ "; print_explore_term !t; print_newline();
            print_string "unfold… ";
            let lexbuf = Lexing.from_channel stdin in
            flush_all ();
            try
                match Parser.explore_command Lexer.token lexbuf with
                    | ExpEnd -> raise Exit
                    | ExpUnfold l -> t := unfold current_state.env (fun n -> List.mem n l) !t
                    | ExpUnfoldAll -> t := unfold current_state.env (fun _ -> true) !t
            with
                | Parsing.Parse_error -> print_string "*** parse error\n"; flush_all ()
                | Error err -> print_string ("*** " ^ err ^ "\n"); flush_all ()
        done
    with Exit -> print_string "end of explore mode\n"

let process_statement = function
    | CmdTest(v,d) -> cmd_print_depth current_state.env v d

    | Eof -> raise Exit
    | CmdQuit -> raise Exit
    | Nothing -> ()

    | CmdShow(s) -> cmd_show current_state.env s
    | CmdPrompt(s) -> current_state.prompt <- s
    | CmdVerbose(v) -> current_state.verbose <- v
    | CmdDebug(o,b) -> setDebugOption o b
    | CmdHelp -> print_help()

    | CmdReduce(t) -> cmd_reduce current_state.env t
    | CmdExplore(t) -> explore_loop current_state.env t

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
    print_endline "          chariot";
    print_endline "  :help for help";
    print_newline();
    try
        for i=1 to (Array.length Sys.argv)-1
        do
            print_string ("=== loading file " ^ Sys.argv.(i)); flush_all ();
            loadfile (Sys.argv.(i));
            print_endline "  OK ";
        done;
        mainloop()
    with Exit -> print_endline "Bye..."
