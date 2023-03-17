module Graph

open Types
open Parse
open FSharp.Text.Lexing
open System
open AST

(*
    This defines the input and output for graphs. Please do not
    change the definitions below as they are needed for the validation and
    evaluation tools!
*)

type Input = { determinism: Determinism }

type Output = { dot: string }

type Node = string

type Label = | ALabel of arithmeticExpr
             | CLabel of command
             | GCLabel of guardedCommand
             | BLabel of booleanExpr

type Edge = { source: Node;
              label: Label;   
              target: Node
            }

let edgesNonDeterministic (ast: AST, qS: int, qF: int) : List<Edge> =
    let mutable q = 0
    let rec edgeCommand (c: command) (qS : int) (qF: int) : List<Edge> =
        match c with
        | Skip -> [{source = "q"+ (string qS); label = CLabel c; target = "q"+ (string (qF))}]
        | Seq (c1, c2) -> 
                                    q <- q + 1
                                    let qTemp = q
                                    edgeCommand c1 qS qTemp @ edgeCommand c2 qTemp qF
        | If gc -> edgeGuardedCommand gc qS qF
        | Do gc -> edgeGuardedCommand gc qS qS @ (doneGuardedCommand gc qS qF)
        | Assign (s, a) -> [{source = "q"+ (string qS); label =  CLabel(Assign (s, a)); target = "q"+ (string (qF))}]
        | ArrAssign (s, a1, a2) -> [{source = "q"+ (string qS); label = CLabel(ArrAssign (s, a1, a2)); target = "q"+ (string (qF))}]
    
    and edgeGuardedCommand (gc: guardedCommand) (qS : int) (qF: int) : List<Edge> =
        match gc with
        | Condition (b, c) -> 
                                        q <- q + 1
                                        let qTemp = q
                                        [{source = "q"+ (string qS); label = BLabel b ; target = "q"+ (string (qTemp))}] @ edgeCommand c qTemp qF
        | Choice (gc1, gc2) -> (edgeGuardedCommand gc1 qS qF) @ (edgeGuardedCommand gc2 qS qF)
    
    and doneGuardedCommand (gc: guardedCommand) (qS : int) (qF: int) : List<Edge> =
        match gc with
        | Condition (b, c) -> [{source = "q"+ (string qS); label = BLabel (NotExpr (ParenBExpr(b))) ; target = "q"+ (string qF)}]
        | Choice (gc1, gc2) -> 
                                                                 let gcBlabel1 = (doneGuardedCommand gc1 qS qF).Head.label
                                                                 let gcBExpr1 = match gcBlabel1 with
                                                                                | BLabel b -> b
                                                                                | _ -> failwith "Not a boolean label"
                                                                 let gcBlabel2= (doneGuardedCommand gc2 qS qF).Head.label
                                                                 let gcBExpr2 = match gcBlabel2 with
                                                                                | BLabel b -> b
                                                                                | _ -> failwith "Not a boolean label"
                                                                 [{source = "q"+ (string qS); label = BLabel(AndAndExpr(gcBExpr1,gcBExpr2)) ; target = "q"+ (string qF)}]

    match ast with
        | C (c) -> edgeCommand c qS qF
        | _ -> []

let edgesDeterministic (ast: AST, qS: int, qF: int) : List<Edge> =
    let mutable q = 0
    let rec edgeCommand (c: command) (qS : int) (qF: int) : List<Edge> =
        match c with
        | Skip -> [{source = "q"+ (string qS); label = CLabel c; target = "q"+ (string (qF))}]
        | Seq (c1, c2) -> 
                                    q <- q + 1
                                    let qTemp = q
                                    edgeCommand c1 qS qTemp @ edgeCommand c2 qTemp qF
        | If gc -> 
                                    let (e,_) = edgeGuardedCommand gc qS qF False 
                                    e
        | Do gc -> 
                                    let (e, b) = (edgeGuardedCommand gc qS qS False) 
                                    e @ [{source = "q"+ (string qS); label = BLabel (NotExpr(b)) ; target = "q"+ (string (qF))}]
        | Assign (s, a) -> [{source = "q"+ (string qS); label =  CLabel(Assign (s, a)); target = "q"+ (string (qF))}]
        | ArrAssign (s, a1, a2) -> [{source = "q"+ (string qS); label = CLabel(ArrAssign (s, a1, a2)); target = "q"+ (string (qF))}]
    
    and edgeGuardedCommand (gc: guardedCommand) (qS : int) (qF: int) (bExpr: booleanExpr) : List<Edge>*booleanExpr =
        match gc with
        | Condition (b, c) -> 
                                        q <- q + 1
                                        let qTemp = q
                                        ([{source = "q"+ (string qS); label = BLabel (AndExpr(ParenBExpr(b),ParenBExpr(NotExpr(bExpr)))) ; target = "q"+ (string (qTemp))}] @ edgeCommand c qTemp qF, ParenBExpr(OrExpr(ParenBExpr(b),ParenBExpr(bExpr))))
        | Choice (gc1, gc2) -> 
                                        let (e1, b1) = edgeGuardedCommand gc1 qS qF bExpr
                                        let (e2, b2) = edgeGuardedCommand gc2 qS qF b1
                                        (e1 @ e2, b2)    

    match ast with
        | C (c) -> edgeCommand c qS qF
        | _ -> []

let astToProgramGraph (ast: AST)(input: Determinism) : List<Edge> = 
    if input = Deterministic then edgesDeterministic (ast, 0, 1000)
    else edgesNonDeterministic (ast, 0, 1000)


let edgeToDot (e: Edge) : string =
    let labelStr =
        match e.label with
        | ALabel ae -> prettyPrint (A ae)
        | CLabel c -> prettyPrint (C c)
        | GCLabel gc -> prettyPrint (GC gc)
        | BLabel be -> prettyPrint (B be)
    e.source + " -> " + e.target + " [label=" + "\"" + labelStr + "\"] ;"

let rec edgesToDot (pg: List<Edge>) : string =
    match pg with
    | [] -> ""
    | e::pg -> edgeToDot e + edgesToDot pg

let programGraphToDot (pg: List<Edge>) : string = 
    "digraph program_graph { rankdir=LR; " +  edgesToDot pg + " }"

let analysis (src: string) (input: Input) : Output =
        match parse Parser.startCommand (src) with
                        | Ok ast ->
                            let programGraph = astToProgramGraph (C ast) input.determinism                            
                            let dotString = programGraphToDot programGraph
                            {dot = dotString}
                        | Error e -> {dot = ""}

// dotnet run graph "skip" "{determinism: {Case:'Deterministic'}}"
// dotnet run graph "skip" "{determinism: {Case:'NonDeterministic'}}"