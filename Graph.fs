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

let edges (ast: AST, qS: Node, qF: Node, n: int) : List<Edge> =

    let rec edgeCommand (c: command) (n : int) (t: int) : List<Edge> =
        match c with
        | Skip -> [{source = "q"+ (string n); label = CLabel c; target = "q"+ (string (t))}]
        | Seq (c1, c2) ->  (edgeCommand c1 n (t)) @ (edgeCommand c2 (n+1) (t+1))
        | If gc -> edgeGuardedCommand gc n (n+1)
        | Do gc -> (doneGuardedCommand gc n) @ edgeGuardedCommand gc (n) (n+1)
        | Assign (s, a) -> [{source = "q"+ (string n); label =  CLabel(Assign (s, a)); target = "q"+ (string (t))}]
        | ArrAssign (s, a1, a2) -> [{source = "q"+ (string n); label = CLabel(ArrAssign (s, a1, a2)); target = "q"+ (string (t))}]
    
    and edgeGuardedCommand (gc: guardedCommand) (n : int) (m: int) : List<Edge> =
        match gc with
        | Condition (b, c) -> [{source = "q"+ (string n); label = BLabel b ; target = "q"+ (string (m))}] @ (edgeCommand c (m) (n-1))
        | Choice (gc1, gc2) -> (edgeGuardedCommand gc1 (n) (n+1)) @ (edgeGuardedCommand gc2 (n) (n+2))
    
    and doneGuardedCommand (gc: guardedCommand) (n : int) : List<Edge> =
        match gc with
        | Condition (b, c) -> [{source = "q"+ (string n); label = BLabel (NotExpr (ParenBExpr(b))) ; target = qF}] 
        | Choice (gc1, gc2) -> (doneGuardedCommand gc1 (n+1)) @ (doneGuardedCommand gc2 (n+1))

    match ast with
        | C (c) -> edgeCommand c n (n+1)
        | _ -> []

let astToProgramGraph (ast: AST) : List<Edge> = 
    edges (ast, "q0", "qF", 0)


let edgeToDot (e: Edge) : string =
    let doubleQuotes = '"'
    let labelStr =
        match e.label with
        | ALabel ae -> prettyPrint (A ae)
        | CLabel c -> prettyPrint (C c)
        | GCLabel gc -> prettyPrint (GC gc)
        | BLabel be -> prettyPrint (B be)
    e.source + " -> " + e.target + " [label=" + "\"" + labelStr + "\"" + "]" + " ;"

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
