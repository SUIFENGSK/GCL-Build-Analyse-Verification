module Interpreter

open Types
open Graph
open Parse
open FSharp.Text.Lexing
open System
open AST

(*
    This defines the input and output for the interpreter. Please do not
    change the definitions below as they are needed for the validation and
    evaluation tools!
*)
type InterpreterMemory =
    { variables: Map<string, int>
      arrays: Map<string, List<int>> }

type Input =
    { determinism: Determinism
      assignment: InterpreterMemory
      trace_length: int }

type Node = Graph.Node

type TerminationState =
    | Running
    | Stuck
    | Terminated

type Configuration<'node> =
    { node: 'node
      memory: InterpreterMemory }

type Output =
    { execution_sequence: List<Configuration<string>>
      final : TerminationState
      }

let stringifyNode (internalNode: Node) : string =
    internalNode

let prepareConfiguration (c: Configuration<Node>) : Configuration<string> =
    { node = stringifyNode c.node
      memory = c.memory }

let rec evalAExpr aExpr memory =
   match aExpr with
    | Num n -> Convert.ToInt32(n)
    | Str s -> memory.variables.[s]
    | PlusExpr (a1, a2) -> (evalAExpr a1 memory) + (evalAExpr a2 memory)
    | MinusExpr (a1, a2) -> (evalAExpr a1 memory) - (evalAExpr a2 memory)
    | TimesExpr (a1, a2) -> (evalAExpr a1 memory) * (evalAExpr a2 memory)
    | DivExpr (a1, a2) -> (evalAExpr a1 memory) / (evalAExpr a2 memory)
    | UPlusExpr a -> evalAExpr a memory
    | UMinusExpr a -> - evalAExpr a memory
    | ArrAccess (s, a) -> let indexNumber = evalAExpr a memory
                          memory.arrays.[s].[indexNumber]
    | PowExpr  (a1, a2) -> Convert.ToInt32(Math.Pow(float(evalAExpr a1 memory), float(evalAExpr a2 memory)))
    | ParenAExpr a -> evalAExpr a memory

let rec evalBExpr bExpr memory =
    match bExpr with
    | True -> true
    | False -> false
    | AndExpr (b1,b2) -> (evalBExpr b1 memory) && (evalBExpr b2 memory) // should be &&&
    | OrExpr (b1,b2) -> (evalBExpr b1 memory) || (evalBExpr b2 memory)  // should be |||
    | AndAndExpr (b1,b2) -> (evalBExpr b1 memory) && (evalBExpr b2 memory)
    | OrOrExpr (b1,b2) -> (evalBExpr b1 memory) || (evalBExpr b2 memory)
    | NotExpr b -> not (evalBExpr b memory)
    | EqExpr (a1,a2) -> (evalAExpr a1 memory) = (evalAExpr a2 memory)
    | NeqExpr (a1,a2) -> (evalAExpr a1 memory) <> (evalAExpr a2 memory)
    | GtExpr (a1,a2) -> (evalAExpr a1 memory) > (evalAExpr a2 memory)
    | GteExpr (a1,a2) -> (evalAExpr a1 memory) >= (evalAExpr a2 memory)
    | LtExpr (a1,a2) -> (evalAExpr a1 memory) < (evalAExpr a2 memory)
    | LteExpr (a1,a2) -> (evalAExpr a1 memory) <= (evalAExpr a2 memory)
    | ParenBExpr b -> evalBExpr b memory

let rec semantic (label: Label, memory: InterpreterMemory) : Option<InterpreterMemory> =
    match label with
    | CLabel c -> match c with
                  | Skip -> Some(memory)
                
                  | Assign (s, a) -> let number = evalAExpr a memory
                                     Some({memory with variables = memory.variables.Add(s, number)})
                  | ArrAssign (s, a1, a2) -> let indexNumber = evalAExpr a1 memory
                                             let valueNumber = evalAExpr a2 memory
                                             let newMemory = memory.arrays[s] |> List.mapi (fun i x -> if i = indexNumber then valueNumber else x)
                                             Some ({memory with arrays = memory.arrays.Add(s, newMemory)})
                  | _ -> None
                                           
    | BLabel b -> 
                  let bool = evalBExpr b memory
                  if bool then Some(memory)
                  else None
    | _ -> None

let rec findNewTarget (programGraph: List<Edge>, edge: Edge) : List<Edge>*Node =
    match programGraph with
    | e::es -> let newSource = e.source
               let newTarget = e.target
               if newSource.Equals(edge.source) && not (newTarget.Equals(edge.target)) then ([e]@es, newSource)
               else findNewTarget(es, edge)
    | [] ->    ([],edge.source) // return the source of the edge if no new target is found (stuck)

// Def. 1.11
let rec executionSteps (programGraph: List<Edge>, q: Node, memory: InterpreterMemory) : List<Configuration<Node>> =
    match programGraph with
    | e::es -> 
              let label = e.label
              let target = e.target
              if not (e.source.Equals(q)) then executionSteps(es,q,memory)
              else 
                 let mprime = semantic(label, memory)
                 if mprime.IsSome then 
                    [ { node = target; memory = mprime.Value } ] @ executionSteps(es, target, mprime.Value)
                 else
                    let (newpg, newSource) = findNewTarget(es, e) 
                    if newpg.IsEmpty then [] // if the new target is the same as the current node, then there is no new target (stuck)
                    else executionSteps(newpg, newSource, memory)            
    | [] -> []

// Def. 1.13
let rec executionSequence (programGraph: List<Edge>, startNode: Node, memory: InterpreterMemory, traceLength: int) : List<Configuration<Node>>*TerminationState =
    let nextStates = executionSteps (programGraph, startNode, memory)
    match traceLength, nextStates with
    | 0, _ -> ([{node = startNode; memory=memory}], Running)
    | _, [] -> let finalState = if startNode.Equals("q1000") then Terminated else Stuck
               ([{node = startNode;  memory=memory}], finalState) 
    | _, conf :: confList ->  let next= executionSequence (programGraph, conf.node, conf.memory, traceLength-1)
                              [{node = startNode; memory=memory}] @ fst(next) , snd(next)                           


let analysis (src: string) (input: Input) : Output =

    match parse Parser.startCommand (src) with
          | Ok ast ->
                               let programGraph = astToProgramGraph (C ast) input.determinism                            
                               let (trace, final) = executionSequence (programGraph, "q0", input.assignment, input.trace_length)                         
                               { execution_sequence = List.map prepareConfiguration trace
                                 final = final
                                 }
          | Error e -> failwith "Error parsing input"

// Run script
// ./dev/win.exe --open
// dotnet run interpreter 'x:=5; if x>10 -> x:=x+1 fi' "{determinism: {Case:'Deterministic'}, assignment: {variables:{},arrays:{}}, trace_length:10}"