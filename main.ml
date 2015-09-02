(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
adequacy checker for recursive definitions involving nested least and
greatest fixed points.

This software is governed by the CeCILL-B license under French law and
abiding by the rules of distribution of free software.  You can  use,
modify and/ or redistribute the software under the terms of the CeCILL-B
license as circulated by CEA, CNRS and INRIA at the following URL
"http://www.cecill.info".

As a counterpart to the access to the source code and  rights to copy,
modify and redistribute granted by the license, users are provided only
with a limited warranty  and the software's author,  the holder of the
economic rights,  and the successive licensors  have only  limited
liability.

In this respect, the user's attention is drawn to the risks associated
with loading,  using,  modifying and/or developing or reproducing the
software by the user in light of its specific status of free software,
that may mean  that it is complicated to manipulate,  and  that  also
therefore means  that it is reserved for developers  and  experienced
professionals having in-depth computer knowledge. Users are therefore
encouraged to load and test the software's suitability as regards their
requirements in conditions enabling the security of their systems and/or
data to be ensured and,  more generally, to use and operate it in the
same conditions as regards security.

The fact that you are presently reading this means that you have had
knowledge of the CeCILL-B license and that you accept its terms.
========================================================================*)


open Env
open Misc
open State
open Explore
open Parser

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

let loadfile path
  =
    let f_in = open_in path in
    let lexbuf = Lexing.from_channel f_in in
    try
        Parser.statements Lexer.tokenize lexbuf
    with
        | Parsing.Parse_error -> parse_error lexbuf
        | Error err -> errmsg "%s" err
        | TypeError err -> errmsg "typing error: %s" err
        | Sys_error err -> errmsg "%s" err
        | Exit -> close_in f_in


let mainloop ()
  = while true
    do
        print_string current_state.prompt; flush_all();
        let lexbuf = Lexing.from_channel stdin in
        flush_all ();
        try
            Parser.single_statement Lexer.tokenize lexbuf
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
        ("-i",                        Arg.Unit (fun _ -> interactive := true),                              "enter interactive mode after reading file");
        ("--interactive",             Arg.Unit (fun _ -> interactive := true),                              "enter interactive mode after reading file");

        ("-v",                        Arg.Int (fun v -> set_option "verbose" (string_of_int v)),            "choose verbosity level");
        ("--verbose",                 Arg.Int (fun v -> set_option "verbose" (string_of_int v)),            "choose verbosity level");

        ("--show_type_struct",        Arg.Unit (fun _ -> set_option "show_type_struct" "true"),             "show type of lazy structures in explore mode");
        ("--show_term_struct",        Arg.Unit (fun _ -> set_option "show_term_struct" "true"),             "show lazy terms in explore mode");
        ("--dont_show_nats",          Arg.Unit (fun _ -> set_option "show_nats" "false"),                   "do not use decimal notation for displaying natural numbers");
        ("--dont_show_lists",         Arg.Unit (fun _ -> set_option "show_lists" "false"),                  "do not use standard notations for displaying lists");
        ("--dont_show_tuples",        Arg.Unit (fun _ -> set_option "show_tuples" "false"),                 "do not use standard notations for displaying tuples");
        ("--dont_allow_incomplete_defs",   Arg.Unit (fun _ -> set_option "allow_incomplete_defs" "false"),       "forbid incomplete definitions");
        ("--keep_useless_clauses",    Arg.Unit (fun _ -> set_option "keep_useless_clauses" "true"),         "keep useless clauses in function definitions");
        ("--dont_use_priorities",     Arg.Unit (fun _ -> set_option "show_use_priorities" "false"),         "do not use priorities for checking termination (unsound)");
        ("--dont_show_priorities",    Arg.Unit (fun _ -> set_option "show_priorities" "false"),             "do not display priorities when showing function definitions");
        ("--continue_on_error",       Arg.Unit (fun _ -> set_option "continue_on_error" "true"),            "do not exit on errors (only for non-interactive use)");
        ("--squash_priorities",       Arg.Unit (fun _ -> set_option "squash_priorities" "true"),            "consecutive types of same polarity get the same priority");
        ("--use_ansi_codes",          Arg.Unit (fun _ -> set_option "use_ansi_codes" "true"),               "use ANSI color codes to display various information");
        ("--dont_use_subsumption",    Arg.Unit (fun _ -> set_option "use_subsumption" "false"),             "don't use subsumption to simplify sets of clauses");
        ("--dont_collapse_graph",     Arg.Unit (fun _ -> set_option "collapse_graph" "false"),              "don't collapse initial call-graph");
        ("--dont_allow_inadequate_defs",   Arg.Unit (fun _ -> set_option "allow_inadequate_defs" "false"),        "forbid definitions that do not pass the SCT");
        ("--expand_clauses",            Arg.Unit (fun _ -> set_option "expand_clauses" "true"),             "use the case expression of the definitions to regenerate the clauses");
        ("--allow_structs",           Arg.Unit (fun _ -> set_option "allow_structs" "true"),                "allow structures inside terms");
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
