{
open Parser
}
let upper = [ 'A'-'Z' ]
let lower = [ 'a'-'z' ]
let other = [ '0'-'9' '_']
let idU = upper(lower|upper|other)*
let idL = lower(lower|upper|other)*

rule token = parse
    | "\n\n"            { EMPTYLINE }
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
    | idU               { IDU(Lexing.lexeme lexbuf) }
    | idL               { IDL(Lexing.lexeme lexbuf) }
    | eof               { EOF }
    | "(*"              { comments 0 lexbuf }
and comments level = parse
    | "*)"              { if level = 0 then token lexbuf else comments (level-1) lexbuf }
    | _                 { comments level lexbuf }
    | eof               { EOF }
