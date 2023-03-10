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

// partial problem with the number of nodes, the number of nodes is not correct (start and end)
// do edgeGuardedCommand doesn't work right now, ArrAssign has not been tested yet
// and this is only for the non-deterministic graph

let edges (ast: AST, qS: int, qF: int) : List<Edge> =
    let mutable q = 0
    let rec edgeCommand (c: command) (qS : int) (qF: int) : List<Edge> =
        match c with
        | Skip -> [{source = "q"+ (string qS); label = CLabel c; target = "q"+ (string (qF))}]
        | Seq (c1, c2) -> 
                                             q <- q + 1
                                             let _q = q
                                             edgeCommand c1 qS _q @ edgeCommand c2 _q qF
        | If gc -> edgeGuardedCommand gc qS qF
        | Do gc -> edgeGuardedCommand gc qS qS @ (doneGuardedCommand gc qS qF)
        | Assign (s, a) -> [{source = "q"+ (string qS); label =  CLabel(Assign (s, a)); target = "q"+ (string (qF))}]
        | ArrAssign (s, a1, a2) -> [{source = "q"+ (string qS); label = CLabel(ArrAssign (s, a1, a2)); target = "q"+ (string (qF))}]
    
    and edgeGuardedCommand (gc: guardedCommand) (qS : int) (qF: int) : List<Edge> =
        match gc with
        | Condition (b, c) -> 
                                                     q <- q + 1
                                                     let _q = q
                                                     [{source = "q"+ (string qS); label = BLabel b ; target = "q"+ (string (_q))}] @ edgeCommand c _q qF
        | Choice (gc1, gc2) -> (edgeGuardedCommand gc1 qS qF) @ (edgeGuardedCommand gc2 qS qF)
    
    and doneGuardedCommand (gc: guardedCommand) (qS : int) (qF: int) : List<Edge> =
        match gc with
        | Condition (b, c) -> [{source = "q"+ (string qS); label = BLabel (NotExpr (ParenBExpr(b))) ; target = "q"+ (string qF)}]
        | Choice (gc1, gc2) -> (doneGuardedCommand gc1 qS qF) @ (doneGuardedCommand gc2 qS qF) 

    match ast with
        | C (c) -> edgeCommand c qS qF
        | _ -> []

let astToProgramGraph (ast: AST) : List<Edge> = 
    edges (ast, 0, 1000)


let edgeToDot (e: Edge) : string =
    let labelStr =
        match e.label with
        | ALabel ae -> prettyPrint (A ae)
        | CLabel c -> prettyPrint (C c)
        | GCLabel gc -> prettyPrint (GC gc)
        | BLabel be -> prettyPrint (B be)
    e.source + " -> " + e.target + " [label=\"" + labelStr + "\"] ;"

let rec edgesToDot (pg: List<Edge>) : string =
    match pg with
    | [] -> ""
    | e::pg -> edgeToDot e + edgesToDot pg

let programGraphToDot (pg: List<Edge>) : string = 
    "digraph program_graph { rankdir=LR; " +  edgesToDot pg + " }"

let analysis (src: string) (input: Input) : Output =
        match parse Parser.startCommand (src) with
                        | Ok ast ->
                            let programGraph = astToProgramGraph (C ast)
                            // Console.Error.WriteLine ("> {0}", programGraph)
                            let dotString = programGraphToDot programGraph
                            {dot = dotString}
                        | Error e -> {dot = ""}
