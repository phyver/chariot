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

let parse_error lexbuf
  = let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let tok = Lexing.lexeme lexbuf in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol - (String.length tok) + 1 in
    errmsg "parse error line %d, column %d (token <%s>)" line cnum tok

let show_error lexbuf
  =
    let open Lexing in
    let s = lexbuf.lex_buffer in
    let s = String.sub s 0 ((String.index s '\000') - 1) in (* necessarry because lex_buffer contains the whole buffer (1024 characters) *)
    let tok = lexeme lexbuf in
    let pos = lexbuf.lex_curr_p.pos_cnum - (String.length tok) in
    let s_start = String.sub s 0 pos in
    let s_end = String.sub s pos ((String.length s) - pos) in
    let s_end =  Str.global_replace (Str.regexp_string "[ \t\n\r]*$") "" s_end in
    (* let s_end = ansi_code "red" s_end in *)
    let s_end = ansi_code "underline" s_end in
    errmsg "%s" (s_start ^ s_end)

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
                match Parser.explore_command Lexer.tokenize lexbuf with
                    | ExpEnd -> raise Exit
                    | ExpUnfold l -> t := unfold current_state.env (fun n -> List.mem n l) !t
                    | ExpUnfoldAll -> t := unfold current_state.env (fun _ -> true) !t
            with
                | Parsing.Parse_error -> parse_error lexbuf
                | Error err -> errmsg "%s" err
                | TypeError err -> errmsg "typing error: %s" err
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
    | CmdOption(o,b) -> setOption o b
    | CmdHelp -> print_help()
    | CmdEcho(s) -> msg "%s" s

    | CmdReduce(t) -> cmd_reduce current_state.env t
    | CmdUnfold(t,d) -> cmd_unfold current_state.env t d
    | CmdExplore(t) -> explore_loop current_state.env t

    | TypeDef(n,defs) -> current_state.env <- process_type_defs current_state.env n defs
    | FunDef(defs) -> current_state.env <- process_function_defs current_state.env defs


let loadfile path
  =
    let f_in = open_in path in
    let lexbuf = Lexing.from_channel f_in in
    try
        let cmds = Parser.statements Lexer.tokenize lexbuf in
        List.iter
            (fun st ->
                try
                    process_statement st
                with
                    | Error err ->
                        if (option "continue_on_error")
                        then errmsg "%s" err
                        else error err
                    | TypeError err ->
                        if (option "continue_on_error")
                        then errmsg "typing error: %s" err
                        else error err
            )
            cmds
    with
        | Parsing.Parse_error -> parse_error lexbuf
        | Error err -> errmsg "%s" err
        | TypeError err -> errmsg "typing error: %s" err
        | Sys_error err -> errmsg "%s" err
        | Exit -> ()


let mainloop ()
  = while true
    do
        print_string current_state.prompt; flush_all();
        let lexbuf = Lexing.from_channel stdin in
        flush_all ();
        try
            process_statement (Parser.single_statement Lexer.tokenize lexbuf)
        with
            | Parsing.Parse_error -> parse_error lexbuf; show_error lexbuf
            | Error err -> errmsg "%s" err
            | TypeError err -> errmsg "typing error: %s" err
    done

let _
  =
    let interactive = ref false in
    let nb_files = ref 0 in

      let args = [
        ("-i",                        Arg.Unit (fun _ -> interactive := true),                             "enter interactive mode after reading file");
        ("--show_type_struct",        Arg.Unit (fun _ -> setOption "show_type_struct" "true"),             "show type of lazy structures in explore mode");
        ("--show_term_struct",        Arg.Unit (fun _ -> setOption "show_term_struct" "true"),             "show lazy terms in explore mode");
        ("--dont_show_nats",          Arg.Unit (fun _ -> setOption "show_nats" "false"),                   "do not use decimal notation for displaying natural numbers");
        ("--dont_show_lists",         Arg.Unit (fun _ -> setOption "show_lists" "false"),                  "do not use standard notations for displaying lists");
        ("--dont_show_tuples",        Arg.Unit (fun _ -> setOption "show_tuples" "false"),                 "do not use standard notations for displaying tuples");
        ("--dont_check_completeness", Arg.Unit (fun _ -> setOption "show_check_completeness" "false"),     "do not check that definitions are complete");
        ("--dont_use_priorities",     Arg.Unit (fun _ -> setOption "show_use_priorities" "false"),         "do not use priorities for checking termination (unsound)");
        ("--dont_show_priorities",    Arg.Unit (fun _ -> setOption "show_priorities" "false"),             "do not display priorities when showing function definitions");
        ("--continue_on_error",       Arg.Unit (fun _ -> setOption "continue_on_error" "true"),            "do not exit on errors (only on non-interactive use)");
        ("--squash_priorities",       Arg.Unit (fun _ -> setOption "squash_priorities" "true"),            "consecutive types of same polarity get the same priority");
        ("--use_ansi_codes",          Arg.Unit (fun _ -> setOption "use_ansi_codes" "true"),               "use ANSI color codes to display various information");
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
