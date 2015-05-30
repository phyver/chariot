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

rule token = parse
    | "\n\n"            { ENDSTATEMENT }
    | ";"               { ENDSTATEMENT }
    | [' ' '\n' '\t']   { token lexbuf }
    | '='               { EQUAL }
    | ':'               { COLON }
    | '('               { LPAR }
    | ')'               { RPAR }
    | '['               { LBRAC }
    | ']'               { RBRAC }
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
    | idU               { IDU(remove_exp (Lexing.lexeme lexbuf)) }
    | idL               { IDL(remove_exp (Lexing.lexeme lexbuf)) }
    | str               { let s = Lexing.lexeme lexbuf in STR(String.sub s 1 ((String.length s)-2)) }
    | eof               { EOF }
    | "(*"              { comments 0 lexbuf }
and comments level = parse
    | "*)"              { if level = 0 then token lexbuf else comments (level-1) lexbuf }
    | _                 { comments level lexbuf }
    | eof               { EOF }
