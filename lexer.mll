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
let idU = upper(lower|upper|other)*exp
let idL = lower(lower|upper|other)*exp
let str = "\"" ([^ '"'] | "\\\"")* "\""
let tvar = "'" lower(lower|upper|other)*exp

rule token = parse
    | ":quit"           { CMDQUIT }
    | ":prompt"         { CMDPROMPT }
    | ":infer"          { CMDINFER }
    | ":unify"          { CMDUNIFY }
    | ":show"           { CMDSHOW }
    | '='               { EQUAL }
    | ':'               { COLON }
    | '('               { LPAR }
    | ')'               { RPAR }
    | ','               { COMMA }
    | '|'               { PIPE }
    | '.'               { DOT }
    | "data"            { DATA }
    | "codata"          { CODATA }
    | "where"           { WHERE }
    | "and"             { AND }
    | "->"              { ARROW }
    | "→"               { ARROW }
    | "val"             { VAL }
    | "!!!"             { DAIMON }
    | "⊥"               { DAIMON }
    | idU               { IDU(remove_exp (Lexing.lexeme lexbuf)) }
    | idL               { IDL(remove_exp (Lexing.lexeme lexbuf)) }
    | tvar              { let s = Lexing.lexeme lexbuf in TVAR(String.sub s 1 ((String.length s)-1)) }
    | str               { let s = Lexing.lexeme lexbuf in STR(String.sub s 1 ((String.length s)-2)) }

    | [' ' '\n' '\t']   { token lexbuf }
    | eof               { EOF }
    | "(*"              { comments 0 lexbuf }
and comments level = parse
    | "(*"              { comments (level+1) lexbuf }
    | "*)"              { if level = 0 then token lexbuf else comments (level-1) lexbuf }
    | _                 { comments level lexbuf }
    | eof               { EOF }
