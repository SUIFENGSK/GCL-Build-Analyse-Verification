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
    | Num n -> try n
               with :? OverflowException -> failwith "Overflow"
    | Str s -> memory.variables.[s]
    | PlusExpr (a1, a2) ->  try
                            (evalAExpr a1 memory) + (evalAExpr a2 memory)
                            with :? OverflowException -> failwith "Overflow"
    | MinusExpr (a1, a2) -> try
                            (evalAExpr a1 memory) - (evalAExpr a2 memory)
                            with :? OverflowException -> failwith "Overflow"
    | TimesExpr (a1, a2) -> try
                            (evalAExpr a1 memory) * (evalAExpr a2 memory)
                            with :? OverflowException -> failwith "Overflow"
    | DivExpr (a1, a2) -> let m = evalAExpr a1 memory
                          let n = evalAExpr a2 memory
                          if n = 0 then failwith "Division by zero" 
                          else try 
                                  m / n
                               with :? OverflowException -> failwith "Overflow"
    | UPlusExpr a -> evalAExpr a memory
    | UMinusExpr a -> - evalAExpr a memory
    | ArrAccess (s, a) -> let indexNumber = evalAExpr a memory
                          if indexNumber < 0 then failwith "Negative index"
                          else if memory.arrays.[s].Length <= indexNumber then failwith "Index out of bounds"
                          else memory.arrays.[s].[indexNumber]
    | PowExpr  (a1, a2) -> let m = evalAExpr a1 memory
                           let n = evalAExpr a2 memory
                           if n < 0 then failwith "Negative exponent"
                           else try
                                Convert.ToInt32(Math.Pow(m,n))
                                with :? OverflowException -> failwith "Overflow"
    | ParenAExpr a -> evalAExpr a memory

let rec evalBExpr bExpr memory =
    match bExpr with
    | True -> true
    | False -> false
    | AndExpr (b1,b2) -> (evalBExpr b1 memory) && (evalBExpr b2 memory)
    | OrExpr (b1,b2) -> (evalBExpr b1 memory) || (evalBExpr b2 memory) 
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
                
                  | Assign (s, a) -> try let number = evalAExpr a memory
                                         Some({memory with variables = memory.variables.Add(s, number)})
                                     with _ -> None
                  | ArrAssign (s, a1, a2) -> try
                                                let indexNumber = evalAExpr a1 memory
                                                if indexNumber < 0 then failwith "Negative index"
                                                let valueNumber = evalAExpr a2 memory
                                                let newMemory = memory.arrays[s] |> List.mapi (fun i x -> if i = indexNumber then valueNumber else x)
                                                Some ({memory with arrays = memory.arrays.Add(s, newMemory)})
                                             with _ -> None
                  | _ -> None
                                           
    | BLabel b -> try
                    let bool = evalBExpr b memory
                    if bool then Some(memory)
                    else None
                  with _ -> None
    | _ -> None

let rec findNewTarget (programGraph: List<Edge>, edge: Edge) : List<Edge>*Edge =
    match programGraph with
    | e::es -> let newSource = e.source
               let newTarget = e.target
               if newSource.Equals(edge.source) && not (newTarget.Equals(edge.target)) then ([e]@es, e)
               else findNewTarget(es, edge)
    | [] ->    ([],edge) // return the source of the edge if no new target is found (stuck)

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
                    let (newpg, newEdge) = findNewTarget(es, e) 
                    if newpg.IsEmpty then [] // if the new target is the same as the current node, then there is no new target (stuck)
                    else executionSteps(newpg, newEdge.source, memory)            
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
                               //Console.Error.WriteLine(programGraph)                            
                               let (trace, final) = executionSequence (programGraph, "q0", input.assignment, input.trace_length)                         
                               { execution_sequence = List.map prepareConfiguration trace
                                 final = final
                                 }
          | Error e -> failwith "Error parsing input"

// Run script
// ./dev/win.exe --open
// dotnet run interpreter 'if 1/0=1/0 -> skip [] true -> x:=2 fi' "{determinism: {Case:'NonDeterministic'}, assignment: {variables:{},arrays:{}}, trace_length:10}"
// dotnet run interpreter 'if 1/0=1/0 -> skip [] true -> x:=2 fi' "{determinism: {Case:'Deterministic'}, assignment: {variables:{},arrays:{}}, trace_length:10}"