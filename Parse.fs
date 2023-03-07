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
        | If gc -> "if " + prettyPrintGC gc + " fi"
        | Do gc -> "do " + prettyPrintGC gc + " od"
    and prettyPrintGC (gc:guardedCommand) =
        match gc with
        | Condition (b, c) -> prettyPrint (B b) + " -> " + prettyPrint (C c)
        | Choice (gc1, gc2) -> prettyPrintGC gc1 + " [] " + prettyPrintGC gc2
        
    let rec prettyPrintAExpr (a:arithmeticExpr) = 
        match a with
        | Num n -> string n
        | Str s -> string s
        | ArrAccess (s, a) -> s + "[" + prettyPrint (A a) + "]"
        | PlusExpr (a1, a2) -> prettyPrint (A a1) + " + " + prettyPrint (A a2)
        | MinusExpr (a1, a2) -> prettyPrint (A a1) + " - " + prettyPrint (A a2)
        | TimesExpr (a1, a2) -> prettyPrint (A a1) + " * " + prettyPrint (A a2)
        | DivExpr (a1, a2) -> prettyPrint (A a1) + " / " + prettyPrint (A a2)
        | UPlusExpr a -> "+" + prettyPrint (A a)
        | UMinusExpr a -> "-" + prettyPrint (A a)
        | PowExpr (a1, a2) -> prettyPrint (A a1) + " ^ " + prettyPrint (A a2)
        | ParenAExpr a -> "(" + prettyPrint (A a) + ")"
    
    let rec prettyPrintBExpr (b:booleanExpr) = 
        match b with
        | True -> "true"
        | False -> "false"
        | AndExpr (b1, b2) -> prettyPrint (B b1) + " & " + prettyPrint (B b2)
        | OrExpr (b1, b2) -> prettyPrint (B b1) + " | " + prettyPrint (B b2)
        | AndAndExpr (b1, b2) -> prettyPrint (B b1) + " && " + prettyPrint (B b2)
        | OrOrExpr (b1, b2) -> prettyPrint (B b1) + " || " + prettyPrint (B b2)
        | NotExpr b -> "!" + prettyPrint (B b)
        | EqExpr (a1, a2) -> prettyPrint (A a1) + " = " + prettyPrint (A a2)
        | NeqExpr (a1, a2) -> prettyPrint (A a1) + " != " + prettyPrint (A a2)
        | GtExpr (a1, a2) -> prettyPrint (A a1) + " > " + prettyPrint (A a2)
        | GteExpr (a1, a2) -> prettyPrint (A a1) + " >= " + prettyPrint (A a2)
        | LtExpr (a1, a2) -> prettyPrint (A a1) + " < " + prettyPrint (A a2)
        | LteExpr (a1, a2) -> prettyPrint (A a1) + " <= " + prettyPrint (A a2)
        | ParenBExpr b -> "(" + prettyPrint (B b) + ")"

    match ast with
    | C c -> prettyPrintCmd c
    | A a -> prettyPrintAExpr a
    | B b -> prettyPrintBExpr b
    | GC gc -> prettyPrintGC gc


let analysis (src: string) : string =
    // try to parse command
    match parse Parser.startCommand (src) with
                        | Ok ast ->
                            Console.Error.WriteLine("> {0}", ast)
                            prettyPrint (C ast)   
                        | _ -> 
    // try to parse guarded command
    match parse Parser.startGuardedCommand (src) with
                        | Ok ast ->
                            Console.Error.WriteLine("> {0}", ast)
                            prettyPrint (GC ast)       
                        | _ ->
    // try to parse arithmetic expression    
    match parse Parser.start (src) with
                        | Ok ast ->
                                Console.Error.WriteLine("> {0}", ast)
                                prettyPrint (A ast)    
                        | _ ->               
    // try to parse boolean expression
    match parse Parser.startBooleanExpr (src) with
                        | Ok ast ->
                            Console.Error.WriteLine("> {0}", ast)
                            prettyPrint (B ast)
                        | Error e -> "Parse error: {0}" + e.Message