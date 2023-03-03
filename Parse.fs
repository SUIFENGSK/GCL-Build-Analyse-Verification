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
    | True -> "true"
    | False -> "false"
    | AndExpr (b1, b2) -> prettyPrint b1 + " & " + prettyPrint b2
    | OrExpr (b1, b2) -> prettyPrint b1 + " | " + prettyPrint b2
    | AndAndExpr (b1, b2) -> prettyPrint b1 + " && " + prettyPrint b2
    | OrOrExpr (b1, b2) -> prettyPrint b1 + " || " + prettyPrint b2
    | NotExpr b -> "!" + prettyPrint b
    | EqExpr (a1, a2) -> prettyPrint a1 + " = " + prettyPrint a2
    | NeqExpr (a1, a2) -> prettyPrint a1 + " != " + prettyPrint a2
    | GtExpr (a1, a2) -> prettyPrint a1 + " > " + prettyPrint a2
    | GteExpr (a1, a2) -> prettyPrint a1 + " >= " + prettyPrint a2
    | LtExpr (a1, a2) -> prettyPrint a1 + " < " + prettyPrint a2
    | LteExpr (a1, a2) -> prettyPrint a1 + " <= " + prettyPrint a2

let analysis (src: string) : string =
    match parse Parser.start (src) with
        | Ok ast ->
            Console.Error.WriteLine("> {0}", ast)
            prettyPrint ast
        | Error e -> "Parse error: {0}"