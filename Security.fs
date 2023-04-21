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
    
let rec assignAll (acc: List<string>) (s: string) : List<Flow> =
    match acc with
    | [] -> []
    | x::xs -> (flow x s)::(assignAll xs s)

let rec assignAllAllowed (acc: Flow list) (input: List<string*List<string>>)  =
    match input with
    | [] -> []
    | (x,y)::xs -> acc @ (assignAll y x) @ (assignAllAllowed acc xs)

let rec fv (ast:AST) =
    match ast with
    | A aExpr -> match aExpr with
                              | Num n -> []
                              | Str s-> [s]
                              | ArrAccess (s, a) -> [s] @ (fv (A a))
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
    | Seq (c1, c2) -> findActualFlows c1 acc @ findActualFlows c2 acc
    | If gc -> findActualFlowsGuard gc acc
    | Do gc -> findActualFlowsGuard gc acc
    | Assign (s, a) -> assignAll (acc @ fv(A a)) s
    | ArrAssign (s, a1, a2) -> assignAll (acc @ fv(A a1)@fv(A a2)) s
and findActualFlowsGuard gc acc=
    match gc with
    | Condition (b, c) -> findActualFlows c (acc @ fv(B b))
    | Choice (gc1, gc2) -> findActualFlowsGuard gc1 acc @ findActualFlowsGuard gc2 (acc@implicitDeps(gc1))
and implicitDeps gc=
    match gc with
    | Condition (b, c) -> fv(B b)
    | Choice (gc1, gc2) -> implicitDeps gc1 @ implicitDeps gc2

let rec findNextLevel (currentLevel: string) (lattice: Flow list) : string =
    match lattice with
    | [] -> ""
    | x::xs -> if x.from = currentLevel then x.into else findNextLevel currentLevel xs


let findAllowedFlows lattice classification =
    let variables = classification.variables
    let arrays = classification.arrays
    let constructEachVarResult (s: string) (sLevel: string): string*List<string> = 
            let mutable acc : List<string> = []
            let rec findSameLevelVar (v:Map<string,string>) (level:string) = 
                let mutable findSameLevelVarResult : List<string> = []
                Map.iter (fun x y -> if y = level then findSameLevelVarResult <- x::findSameLevelVarResult) v
                findSameLevelVarResult
            acc <- findSameLevelVar variables sLevel
            let rec findHigherLevelVal (v:Map<string,string>) (currentLevel: string) =
                let mutable findHigherLevelValResult : List<string> = []
                Map.iter (fun x y -> if y = currentLevel then findHigherLevelValResult <- findHigherLevelValResult @ x::(findHigherLevelVal variables (findNextLevel currentLevel lattice))) v
                findHigherLevelValResult
            acc <- acc @ findHigherLevelVal variables sLevel
            (s, acc)
    let rec constructAllVarResult (v:Map<string,string>) : List<string*List<string>> =
        let mutable constructAllVarResultResult : List<string*List<string>> = []
        Map.iter (fun x y -> constructAllVarResultResult <- constructAllVarResultResult @ [constructEachVarResult x y]) v
        constructAllVarResultResult

    assignAllAllowed List.empty (constructAllVarResult variables) |> List.distinct |> List.sort

    
                                                                 
                     
        
    

let analysis (src: string) (input: Input) : Output =
    match parse Parser.startCommand (src) with
                        | Ok ast ->                                     
                                    { actual = (findActualFlows ast []) |> List.distinct |> List.sort
                                      allowed = findAllowedFlows input.lattice input.classification
                                      violations = [] }
                        | Error e -> failwith "Error in parsing"