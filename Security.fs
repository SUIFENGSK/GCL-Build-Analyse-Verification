module Security

open Types
open Parse
open FSharp.Text.Lexing
open System
open AST

(*
    This defines the input and output for the security analysis. Please do not
    change the definitions below as they are needed for the validation and
    evaluation tools!
*)

type Flow = { from: string; into: string }
let flow a b : Flow = { from = a; into = b }

type Classification =
    { variables: Map<string, string>
      arrays: Map<string, string> }

type Input =
    { lattice: Flow list
      classification: Classification }

type Output =
    { actual: Flow list
      allowed: Flow list
      violations: Flow list }

// Need to consider different types of variables.
let rec assignAll (acc: List<string>) (s: string) : List<Flow> =
    match acc with
    | [] -> []@[(flow s s)]
    | x::xs -> (flow x x)::(flow s x)::(assignAll xs s)

let rec fv (ast:AST) =
    match ast with
    | A aExpr -> match aExpr with
                              | Num n -> []
                              | Str s-> [s]
                              | ArrAccess (s, a) -> [s]
                              | PlusExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | MinusExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | TimesExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | DivExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | UPlusExpr a -> fv (A a)
                              | UMinusExpr a -> fv (A a) 
                              | PowExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | ParenAExpr a -> fv (A a)
    | B bExpr -> match bExpr with
                              | True -> []
                              | False -> []
                              | AndExpr (b1, b2) -> (fv (B b1)) @ (fv (B b2))
                              | OrExpr (b1, b2) -> (fv (B b1)) @ (fv (B b2))
                              | AndAndExpr (b1, b2) -> (fv (B b1)) @ (fv (B b2))
                              | OrOrExpr (b1, b2) -> (fv (B b1)) @ (fv (B b2))
                              | NotExpr b -> fv (B b)
                              | EqExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | NeqExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | LtExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | LteExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | GtExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | GteExpr (a1, a2) -> (fv (A a1)) @ (fv (A a2))
                              | ParenBExpr b -> fv (B b)
    | _ -> []



let rec findActualFlows ast acc=
    match ast with
    | Skip -> []
    | Seq (c1, c2) -> (findActualFlows c1 acc @ findActualFlows c2 acc) |> List.distinct
    | If gc -> findActualFlowsGuard gc acc
    | Do gc -> findActualFlowsGuard gc acc
    | Assign (s, a) -> assignAll ((acc @ fv(A a))|> List.distinct) s
    | ArrAssign (s, a1, a2) -> assignAll ((acc @ fv(A a1)@fv(A a2))|> List.distinct) s
and findActualFlowsGuard gc acc=
    match gc with
    | Condition (b, c) -> findActualFlows c ((acc @ fv(B b))|> List.distinct)
    | Choice (gc1, gc2) -> (findActualFlowsGuard gc1 acc @ findActualFlowsGuard gc2 (acc@implicitDeps(gc1)))|> List.distinct
and implicitDeps gc=
    match gc with
    | Condition (b, c) -> fv(B b)
    | Choice (gc1, gc2) -> (implicitDeps gc1 @ implicitDeps gc2) |> List.distinct




let startAnalysis ast input =
    let mutable actual: List<Flow> = []
    let mutable allowed: List<Flow> = []
    let mutable violations: List<Flow> = []
    let lattice = input.lattice
    let classification = input.classification
    actual <- findActualFlows ast []
    { actual = actual
      allowed = allowed
      violations = violations}


let analysis (src: string) (input: Input) : Output =
    match parse Parser.startCommand (src) with
                        | Ok ast -> 
                                    let result = startAnalysis ast input
                                    { actual = result.actual
                                      allowed = result.allowed
                                      violations = result.violations }
                        | Error e -> failwith "Error in parsing"
