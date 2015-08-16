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
    | ":help"           { CMDHELP }
    | ":echo"           { CMDECHO }
    | ":set"            { CMDSET }
    | ":show"           { CMDSHOW }
    | ":reduce"         { CMDREDUCE }
    | ":unfold"         { CMDUNFOLD }
    | ":explore"        { CMDEXPLORE }
    | ":quit"           { CMDQUIT }

    | ":test" [' ' '\t']+ "unifytypes" { TESTUNIFYTYPES }
    | ":test" [' ' '\t']+ "unifyterms" { TESTUNIFYTERMS }
    | ":test" [' ' '\t']+ "compose"    { TESTCOMPOSE }
    | ":test" [' ' '\t']+ "compare"    { TESTCOMPARE }
    | ":test" [' ' '\t']+ "collapse"   { TESTCOLLAPSE }

    | "\n\n"            { Lexing.new_line lexbuf; Lexing.new_line lexbuf; BLANKLINE }

    | "="               { EQUAL }
    | "::"              { DOUBLECOLON }
    | ":"               { COLON }
    | ";"               { SEMICOLON }
    | "("               { LPAR }
    | ")"               { RPAR }
    | "["               { LSQBRAC }
    | "]"               { RSQBRAC }
    | ","               { COMMA }
    | "|"               { PIPE }
    | "."               { DOT }
    | "+"               { PLUS }
    | "-"               { MINUS }
    | "*"               { STAR }
    | "data"            { DATA }
    | "codata"          { CODATA }
    | "where"           { WHERE }
    | "and"             { AND }
    | "->"              { ARROW }
    | "→"               { ARROW }
    | "=>"              { DOUBLEARROW }
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
