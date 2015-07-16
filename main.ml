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

let print_help ()
  = print_list "" "| " "\n| " "\n\n" print_string [
        "";
        "chariot: a language with arbitrary nested inductive and coinductive types";
        "";
        "TODO";
        "";
    ]

let explore_loop env t
  = print_list "" "| " "\n| " "\n\n" print_string [
        "Explore mode:";
        "  you can unfold a (coinductive) datastructure interactively";
        "  by inputing the corresponding indices";
        "";
        "  ':quit' to quit the explore mode"
    ];
    let t = ref (term_to_explore env t) in
    try
        while true
        do
            msg "result: %s" (string_of_explore_term !t);
            print_string ("unfold… "^current_state.prompt);
            let lexbuf = Lexing.from_channel stdin in
            flush_all ();
            try
                match Parser.explore_command Lexer.token lexbuf with
                    | ExpEnd -> raise Exit
                    | ExpUnfold l -> t := unfold current_state.env (fun n -> List.mem n l) !t
                    | ExpUnfoldAll -> t := unfold current_state.env (fun _ -> true) !t
            with
                | Parsing.Parse_error -> errmsg "parse error"
                | Error err -> errmsg "%s" err
        done
    with Exit -> msg "end of explore mode"

let process_statement s = match s with
    | CmdTest(v,d) -> ()

    | Eof -> raise Exit
    | CmdQuit -> raise Exit
    | Nothing -> ()

    | CmdShow(s) -> cmd_show current_state.env s
    | CmdPrompt(s) -> current_state.prompt <- s
    | CmdVerbose(v) -> current_state.verbose <- v
    | CmdOption("",b) -> showOptions current_state.options
    | CmdOption(o,b) -> setOption o b
    | CmdHelp -> print_help()
    | CmdEcho(s) -> msg "%s" s

    | CmdReduce(t) -> cmd_reduce current_state.env t
    | CmdUnfold(t,d) -> cmd_unfold current_state.env t d
    | CmdExplore(t) -> explore_loop current_state.env t

    | TypeDef(n,defs) -> current_state.env <- process_type_defs current_state.env n defs
    | FunDef(defs) -> current_state.env <- process_function_defs current_state.env defs


let loadfile path
  = try
        let f_in = open_in path in
        let lexbuf = Lexing.from_channel f_in in
        let cmds = Parser.statements Lexer.token lexbuf in
        List.iter
            (fun st ->
                try
                    process_statement st
                with
                    | Error err ->
                        if (option "continue_on_error")
                        then errmsg "%s" err
                        else error err
            )
            cmds
    with
        | Parsing.Parse_error -> errmsg "parse error"
        | Error err -> errmsg "%s" err
        | Sys_error err -> errmsg "%s" err
        | Exit -> ()


let mainloop ()
  = while true
    do
        print_string current_state.prompt; flush_all();
        let lexbuf = Lexing.from_channel stdin in
        flush_all ();
        try
            process_statement (Parser.single_statement Lexer.token lexbuf)
        with
            | Parsing.Parse_error -> errmsg "parse error"
            | Error err -> errmsg "%s" err
    done

let _
  =
    let interactive = ref false in
    let nb_files = ref 0 in

      let args = [
        ("-i",                        Arg.Unit (fun _ -> interactive := true),                           "enter interactive mode after reading file");
        ("--show_type_struct",        Arg.Unit (fun _ -> setOption "show_type_struct" true),             "show type of lazy structures in explore mode");
        ("--show_term_struct",        Arg.Unit (fun _ -> setOption "show_term_struct" true),             "show lazy terms in explore mode");
        ("--dont_show_nats",          Arg.Unit (fun _ -> setOption "dont_show_nats" true),               "do not use decimal notation for displaying natural numbers");
        ("--dont_show_lists",         Arg.Unit (fun _ -> setOption "dont_show_lists" true),              "do not use standard notations for displaying lists");
        ("--dont_check_completeness", Arg.Unit (fun _ -> setOption "dont_show_check_completeness" true), "do not check that definitions are complete");
        ("--dont_use_priorities",     Arg.Unit (fun _ -> setOption "dont_show_use_priorities" true),     "do not use priorities for checking termination (unsound)");
        ("--dont_show_priorities",    Arg.Unit (fun _ -> setOption "dont_show_priorities" true),         "do not display priorities when showing function definitions");
        ("--continue_on_error",       Arg.Unit (fun _ -> setOption "continue_on_error" true),            "do not exit on errors (only on non-interactive use)");
      ] in
    let help = "usage: " ^ Sys.argv.(0) ^ " [-i] [file]\n" in
    Arg.parse args (fun f -> incr nb_files; loadfile f) help;

    if !nb_files = 0 || !interactive
    then begin
        print_endline "          chariot";
        print_endline "  :help for help";
        print_newline();
        try
            mainloop()
        with Exit -> print_endline "Bye..."
    end
