module Parse

open FSharp.Text.Lexing
open System
open AST

exception ParseError of Position * string * Exception

let parse parser src =
    let lexbuf = LexBuffer<char>.FromString src

    let parser = parser Lexer.tokenize

    try
        Ok(parser lexbuf)
    with
    | e ->
        let pos = lexbuf.EndPos
        let line = pos.Line
        let column = pos.Column
        let message = e.Message
        let lastToken = new String(lexbuf.Lexeme)
        eprintf "Parse failed at line %d, column %d:\n" line column
        eprintf "Last token: %s" lastToken
        eprintf "\n"
        Error(ParseError(pos, lastToken, e))



let rec prettyPrint (ast:AST) =
    let rec prettyPrintCmd (cmd:command) =
        match cmd with
        | Assign(s, a) -> s + " := " + prettyPrint (A a)
        | ArrAssign (s, a1, a2) -> s + "[" + prettyPrint (A a1) + "] := " + prettyPrint (A a2)
        | Skip -> "skip"
        | Seq (c1, c2) -> prettyPrint (C c1) + "; \n" + prettyPrint (C c2)
        
    let rec prettyPrintAExpr (a:arithmeticExpr) = 
        match a with
        | Num n -> string n
        | Str s -> string s

    match ast with
    | C c -> prettyPrintCmd c
    | A a -> prettyPrintAExpr a


let analysis (src: string) : string =
    match parse Parser.startCommand (src) with
        | Ok ast ->
            Console.Error.WriteLine("> {0}", ast)
            prettyPrint (C ast)
        | Error e -> "Parse error: {0}"