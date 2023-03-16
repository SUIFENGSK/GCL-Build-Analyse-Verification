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

// TODO: Change this to you internal version of node
// If your node type is defined in graph, consider using the following:
type Node = Graph.Node
//type Node = string

type TerminationState =
    | Running
    | Stuck
    | Terminated

type Configuration<'node> =
    { node: 'node
      memory: InterpreterMemory }

type Output =
    { execution_sequence: List<Configuration<string>>
      final: TerminationState }

let stringifyNode (internalNode: Node) : string =
    // TODO: implement for internal node type
    internalNode

let prepareConfiguration (c: Configuration<Node>) : Configuration<string> =
    { node = stringifyNode c.node
      memory = c.memory }

let semantic (label: Label, memory: InterpreterMemory) : Option<InterpreterMemory> =
    match label with
    | ALabel a -> Some(memory)
    | CLabel c -> match c with
                  | Skip -> Some(memory)
                  | _ -> None
                  // | Seq (c1, c2) -> memory
                  // | If gc -> memory
                  // | Do gc -> memory
                  // | Assign (s, a) -> memory
                  // | ArrAssign (s, a1, a2) -> memory
    | GCLabel gc -> Some(memory)
    | BLabel b -> Some(memory)

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
                   executionSteps(es, target, mprime.Value)
    | [] -> []

// Def. 1.13
let rec executionSequence (programGraph: List<Edge>, startNode: Node, memory: InterpreterMemory, traceLength: int) : List<Configuration<Node>>*TerminationState =
    let nextStates = executionSteps (programGraph, startNode, memory)
    //Console.Error.WriteLine (nextStates)
    match traceLength, nextStates with
    | 0, _ -> ([{node = startNode; memory=memory}], Running)
    | _, [] -> let finalState = if startNode.Equals("q1000") then Terminated else Stuck
               ([{node = startNode; memory=memory}], finalState) 
    | _, conf :: confList ->  let next= executionSequence (programGraph, conf.node, conf.memory, traceLength-1)
                              [{node = startNode; memory=memory}] @ fst(next) , snd(next)                           


let analysis (src: string) (input: Input) : Output =

    match parse Parser.startCommand (src) with
          | Ok ast ->
                               let programGraph = astToProgramGraph (C ast) input.determinism
                               Console.Error.WriteLine (input.trace_length)
                               let (trace, final) = executionSequence (programGraph, "q0", input.assignment, input.trace_length)                         
                               { execution_sequence = List.map prepareConfiguration trace
                                 final = final }
          | Error e -> failwith "TODO"

// dotnet run interpreter 'skip;skip;skip' "{determinism: {Case:'Deterministic'}, assignment: {variables:{},arrays:{}}, trace_length:10}"