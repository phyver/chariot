
let main () =
    while true
    do
        print_string ">>> "; flush_all();
        let lexbuf = Lexing.from_channel stdin in
        let _ = Parser.statement Lexer.token lexbuf in
        print_newline()
    done

let _ = main ()
