{
open Parser

let remove_exp s =
    let re = Str.regexp "\\(⁰\\|¹\\|²\\|³\\|⁴\\|⁵\\|⁶\\|⁷\\|⁸\\|⁹\\)*$" in
    Str.global_replace re "" s

}
let upper = [ 'A'-'Z' ]
let lower = [ 'a'-'z' ]
let other = [ '0'-'9' '_']
let exp = ("⁰" | "¹" | "²" | "³" | "⁴" | "⁵" | "⁶" | "⁷" | "⁸" | "⁹")*
let sub = ("₀" | "₁" | "₂" | "₃" | "₄" | "₅" | "₆" | "₇" | "₈" | "₉")*
let idU = upper(lower|upper|other)*exp
let idL = lower(lower|upper|other)*exp
let str = "\"" ([^ '"'] | "\\\"")* "\""
let tvar = "'" lower(lower|upper|other)*exp
let int = [ '0'-'9' ][ '0'-'9' ]*
let dummy = "_" sub


rule tokenize = parse
    | ":quit"           { CMDQUIT }
    | ":prompt"         { CMDPROMPT }
    | ":show"           { CMDSHOW }
    | ":echo"           { CMDECHO }
    | ":verbose"        { CMDVERBOSE }
    | ":set"            { CMDSET }
    | ":explore"        { CMDEXPLORE }
    | ":help"           { CMDHELP }
    | ":testcompose"    { CMDTESTCOMPOSE }
    | ":testcompare"    { CMDTESTCOMPARE }
    | ":testcollapse"    { CMDTESTCOLLAPSE }
    | ":test"           { CMDTEST }
    | ":reduce"         { CMDREDUCE }
    | ":unfold"         { CMDUNFOLD }
    | '='               { EQUAL }
    | "::"              { DOUBLECOLON }
    | ':'               { COLON }
    | ';'               { SEMICOLON }
    | '('               { LPAR }
    | ')'               { RPAR }
    | '['               { LSQBRAC }
    | ']'               { RSQBRAC }
    | ','               { COMMA }
    | '|'               { PIPE }
    | '.'               { DOT }
    | '+'               { PLUS }
    | '-'               { MINUS }
    | '*'               { STAR }
    | "\n\n"            { Lexing.new_line lexbuf; Lexing.new_line lexbuf; BLANKLINE }
    | "data"            { DATA }
    | "codata"          { CODATA }
    | "where"           { WHERE }
    | "and"             { AND }
    | "->"              { ARROW }
    | "=>"              { DOUBLEARROW }
    | "→"               { ARROW }
    | "val"             { VAL }
    | "???"             { ANGEL }
    | "⊤"               { ANGEL }
    | dummy             { DUMMY }
    | idU               { IDU(remove_exp (Lexing.lexeme lexbuf)) }
    | idL               { IDL(remove_exp (Lexing.lexeme lexbuf)) }
    | tvar              { let s = Lexing.lexeme lexbuf in TVAR(String.sub s 1 ((String.length s)-1)) }
    | str               { let s = Lexing.lexeme lexbuf in STR(String.sub s 1 ((String.length s)-2)) }
    | int               { INT(int_of_string (Lexing.lexeme lexbuf)) }

    | [' ' '\t']        { tokenize lexbuf }
    | "\n"              { Lexing.new_line lexbuf; tokenize lexbuf }
    | eof               { EOF }
    | "(*"              { comments 0 lexbuf }
    | "--" [^ '\n']*    { tokenize lexbuf }

and comments level = parse
    | "(*"              { comments (level+1) lexbuf }
    | "*)"              { if level = 0 then tokenize lexbuf else comments (level-1) lexbuf }
    | "\n"              { Lexing.new_line lexbuf; comments level lexbuf }
    | [^ '\n']          { comments level lexbuf }
    | eof               { EOF }
