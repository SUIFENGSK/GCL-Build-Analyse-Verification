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

let rec prettyPrint ast =
   match ast with
    | Num n -> string n
    | Str s -> s
    | Assign (s, a) -> s + ":=" + prettyPrint a
    | ArrAssign (s, a1, a2) -> s + "[" + prettyPrint a1 + "] := " + prettyPrint a2
    | Skip -> "skip"
    | Sequence (c1, c2) -> prettyPrint c1 + "; " + prettyPrint c2
    | If gc -> "if " + prettyPrint gc + " fi"
    | Do gc -> "do " + prettyPrint gc + " od"
    | Condition (b, c) -> prettyPrint b + " -> " + prettyPrint c
    | Choice (gc1, gc2) -> prettyPrint gc1 + " [] " + prettyPrint gc2
    
let analysis (src: string) : string =
    match parse Parser.start (src) with
        | Ok ast ->
            Console.Error.WriteLine("> {0}", ast)
            prettyPrint ast
        | Error e -> "Parse error: {0}"