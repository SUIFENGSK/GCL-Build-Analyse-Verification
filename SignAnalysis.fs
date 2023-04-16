module SignAnalysis

open Types
open Graph
open Parse
open FSharp.Text.Lexing
open System
open AST

(*
     This defines the input and output of the sign analysis. Please do not
    change the definitions below as they are needed for the validation and
    evaluation tools!
*)

type Sign =
    | Negative
    | Zero
    | Positive

// SignAssignment = abstract memory
type SignAssignment =
    { variables: Map<string, Sign>
      arrays: Map<string, Set<Sign>> }

type Input =
    { determinism: Determinism
      assignment: SignAssignment } // this makes up the set of initial memories

type Output =
    { initial_node: string
      final_node: string
      nodes: Map<string, Set<SignAssignment>> }
      
// abstract Operations

let abstractPlus (set1:Set<Sign>) (set2:Set<Sign>) : Set<Sign> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> Set.add Negative set
                        | Negative, Zero -> Set.add Negative set
                        | Negative, Positive -> (Set.add Negative set).Add(Zero).Add(Positive)
                        | Zero, Negative -> Set.add Negative set
                        | Zero, Zero -> Set.add Zero set
                        | Zero, Positive -> Set.add Positive set
                        | Positive, Negative -> (Set.add Negative set).Add(Zero).Add(Positive)
                        | Positive, Zero -> Set.add Positive set
                        | Positive, Positive -> Set.add Positive set
                        ) set set2
                     ) Set.empty set1

let abstractMinus (set1:Set<Sign>) (set2:Set<Sign>) : Set<Sign> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add Negative set).Add(Zero).Add(Positive)
                        | Negative, Zero -> Set.add Negative set
                        | Negative, Positive -> Set.add Negative set
                        | Zero, Negative -> Set.add Positive set
                        | Zero, Zero -> Set.add Zero set
                        | Zero, Positive -> Set.add Negative set
                        | Positive, Negative -> Set.add Positive set
                        | Positive, Zero -> Set.add Positive set
                        | Positive, Positive -> (Set.add Negative set).Add(Zero).Add(Positive)
                        ) set set2
                     ) Set.empty set1

let abstractTimes (set1:Set<Sign>) (set2:Set<Sign>) : Set<Sign> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> Set.add Positive set
                        | Negative, Zero -> Set.add Zero set
                        | Negative, Positive -> Set.add Negative set
                        | Zero, _ -> Set.add Zero set
                        | Positive, Negative -> Set.add Negative set
                        | Positive, Zero -> Set.add Zero set
                        | Positive, Positive -> Set.add Positive set
                        ) set set2
                     ) Set.empty set1

let abstractDiv (set1:Set<Sign>) (set2:Set<Sign>) : Set<Sign> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add Positive set).Add(Zero)
                        | Negative, Positive -> (Set.add Negative set).Add(Zero)
                        | Zero, Negative -> Set.add Zero set
                        | Zero, Positive -> Set.add Zero set
                        | Positive, Negative -> (Set.add Negative set).Add(Zero)
                        | Positive, Positive -> (Set.add Positive set).Add(Zero)
                        | _, Zero -> set // division by zero
                        ) set set2
                     ) Set.empty set1

let abstractUPlus (set:Set<Sign>) : Set<Sign> =
            Set.fold (fun set el -> 
                      match el with
                        | Negative -> Set.add Negative set
                        | Zero -> Set.add Zero set
                        | Positive -> Set.add Positive set
                        ) Set.empty set

let abstractUMinus (set:Set<Sign>) : Set<Sign> =
            Set.fold (fun set el -> 
                      match el with
                        | Negative -> Set.add Positive set
                        | Zero -> Set.add Zero set
                        | Positive -> Set.add Negative set
                        ) Set.empty set

let abstractPow (set1:Set<Sign>) (set2:Set<Sign>) : Set<Sign> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | _, Negative -> set // negative to negative power
                        | Positive, Positive -> Set.add Positive set
                        | Positive, Zero -> Set.add Positive set
                        | Zero, Positive -> Set.add Zero set
                        | Zero, Zero -> Set.add Positive set
                        | Negative, Positive -> (Set.add Negative set).Add(Positive)
                        | Negative, Zero -> Set.add Positive set
                        ) set set2
                     ) Set.empty set1 

let abstractAnd (set1:Set<bool>) (set2:Set<bool>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | true, true -> Set.add true set
                        | true, false -> Set.add false set
                        | false, _ -> Set.add false set
                        ) set set2
                     ) Set.empty set1

let abstractOr (set1:Set<bool>) (set2:Set<bool>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | true, _ -> Set.add true set
                        | false, true -> Set.add true set
                        | false, false -> Set.add false set
                        ) set set2
                     ) Set.empty set1

let abstractAndAnd (set1:Set<bool>) (set2:Set<bool>) : Set<bool> =
            Set.union(Set.intersect set1 (Set.add false Set.empty)) (abstractAnd set1 set2)

let abstractOrOr (set1:Set<bool>) (set2:Set<bool>) : Set<bool> =
            Set.union(Set.intersect set1 (Set.add true Set.empty)) (abstractOr set1 set2)

let abstractNot (set:Set<bool>) : Set<bool> =
            Set.fold (fun set el -> 
                      match el with
                        | true -> Set.add false set
                        | false -> Set.add true set
                        ) Set.empty set

let abstractEq (set1:Set<Sign>) (set2:Set<Sign>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add true set).Add(false)
                        | Negative, _ -> Set.add false set
                        | Zero, Zero -> Set.add true set
                        | Zero, _ -> Set.add false set
                        | Positive, Positive -> (Set.add true set).Add(false)
                        | Positive, _ -> Set.add false set
                        ) set set2
                     ) Set.empty set1

let abstractNeq (set1:Set<Sign>) (set2:Set<Sign>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add true set).Add(false)
                        | Negative, _ -> Set.add true set
                        | Zero, Zero -> Set.add false set
                        | Zero, _ -> Set.add true set
                        | Positive, Positive -> (Set.add true set).Add(false)
                        | Positive, _ -> Set.add true set
                        ) set set2
                     ) Set.empty set1

let abstractGt (set1:Set<Sign>) (set2:Set<Sign>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add true set).Add(false)
                        | Negative, _ -> Set.add false set
                        | Zero, Positive -> Set.add false set
                        | Zero, Zero -> Set.add false set
                        | Zero, Negative -> Set.add true set
                        | Positive, Positive -> (Set.add true set).Add(false)
                        | Positive, _ -> Set.add true set
                        ) set set2
                     ) Set.empty set1

let abstractGte (set1:Set<Sign>) (set2:Set<Sign>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add true set).Add(false)
                        | Negative, _ -> Set.add false set
                        | Zero, Positive -> Set.add false set
                        | Zero, _ -> Set.add true set
                        | Positive, Positive -> (Set.add true set).Add(false)
                        | Positive, _ -> Set.add true set
                        ) set set2
                     ) Set.empty set1

let abstractLt (set1:Set<Sign>) (set2:Set<Sign>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add true set).Add(false)
                        | Negative, _ -> Set.add true set
                        | Zero, Positive -> Set.add true set
                        | Zero, Zero -> Set.add false set
                        | Zero, Negative -> Set.add false set
                        | Positive, Positive -> (Set.add true set).Add(false)
                        | Positive, _ -> Set.add false set
                        ) set set2
                     ) Set.empty set1

let abstractLte (set1:Set<Sign>) (set2:Set<Sign>) : Set<bool> =
            Set.fold (fun set el1 -> 
            Set.fold (fun set el2 -> 
                      match el1, el2 with
                        | Negative, Negative -> (Set.add true set).Add(false)
                        | Negative, _ -> Set.add true set
                        | Zero, Positive -> Set.add true set
                        | Zero, Zero -> Set.add true set
                        | Zero, Negative -> Set.add false set
                        | Positive, Positive -> (Set.add true set).Add(false)
                        | Positive, _ -> Set.add false set
                        ) set set2
                     ) Set.empty set1

let rec analysisAExpr (a:arithmeticExpr) (mem:Set<SignAssignment>) : Set<Sign> = 
    match a with
    | Num n -> Set.singleton (if n < 0 then Negative else if n = 0 then Zero else Positive)
    | Str s -> 
                        let mapV = Set.fold (fun map mem -> mem.variables) Map.empty mem
                        Set.add (Map.find s mapV) Set.empty
    | ArrAccess (s, a) -> 
                                                  let mapA = Set.fold (fun map mem -> mem.arrays) Map.empty mem
                                                  if not (Set.isEmpty(Set.intersect (analysisAExpr a mem) (Set.empty.Add(Zero).Add(Positive))))
                                                  then (Map.find s mapA)
                                                  else Set.empty
    | PlusExpr (a1, a2) -> abstractPlus (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | MinusExpr (a1, a2) -> abstractMinus (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | TimesExpr (a1, a2) -> abstractTimes (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | DivExpr (a1, a2) -> abstractDiv (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | UPlusExpr a -> abstractUPlus (analysisAExpr a mem)
    | UMinusExpr a -> abstractUMinus (analysisAExpr a mem)
    | PowExpr (a1, a2) -> abstractPow (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | ParenAExpr a -> analysisAExpr a mem

let updateVarSignInMem (mem:Set<SignAssignment>) (s:string) (a:arithmeticExpr) : Set<SignAssignment> = 
    let mutable newVarSigns= Set.empty
    let mutable newMem = Set.empty
    Set.iter (fun sa -> 
              let newSign = analysisAExpr a (Set.singleton sa)
              Set.iter (fun x -> 
                                        (newVarSigns <- Set.add x newVarSigns
                                         newMem <- Set.add { sa with variables = Map.add s x sa.variables } newMem
                                        )) newSign
              
              ) mem
    newMem

let updateArrSignInMem (mem: Set<SignAssignment>) (s: string) (a1: arithmeticExpr) (a2: arithmeticExpr) : Set<SignAssignment> = 
    let resInd = analysisAExpr a1 mem
    let newArrSigns = analysisAExpr a2 mem
    if Set.intersect resInd (Set.empty.Add(Zero).Add(Positive)) = Set.empty then
        mem
    else
        let mutable spiltNewArrSigns = Set.empty
        Set.iter (fun x -> 
                  if x = Negative then
                      spiltNewArrSigns <- Set.add (Set.empty.Add(Negative)) spiltNewArrSigns
                  else if x = Zero then
                      spiltNewArrSigns <- Set.add (Set.empty.Add(Zero)) spiltNewArrSigns
                  else
                      spiltNewArrSigns <- Set.add (Set.empty.Add(Positive)) spiltNewArrSigns
                  ) newArrSigns
        // combine all possible signs between mem and newArrSigns
        let mutable combineArrSigns= Set.empty
        Set.iter (fun sa -> 
                  Set.iter (fun newArrSign -> 
                            let mutable findset = Map.find s sa.arrays
                            if findset.Count>1 then
                               // Add first total
                               combineArrSigns <- Set.add { sa with arrays = Map.add s (Set.union (Map.find s sa.arrays) newArrSign) sa.arrays } combineArrSigns
                               // Then split and add every element in findset
                               Set.iter
                                (fun x -> 
                                  combineArrSigns <- Set.add { sa with arrays = Map.add s (Set.union (Set.singleton x) newArrSign) sa.arrays } combineArrSigns
                                ) findset                                
                            else
                               combineArrSigns <- Set.add { sa with arrays = Map.add s (Set.union (Map.find s sa.arrays) newArrSign) sa.arrays } combineArrSigns
                            ) spiltNewArrSigns
                  ) mem
        let mutable finalResult: Set<SignAssignment> = Set.empty
        // add spiltNewArrSigns and combineArrSigns to finalResult
        finalResult <- combineArrSigns
        Set.iter (fun sa -> 
                  Set.iter (fun newArrSigns -> 
                            finalResult <- Set.add { sa with arrays = Map.add s newArrSigns sa.arrays } finalResult
                            ) spiltNewArrSigns
                  ) mem
        finalResult

                          
let rec analysisBExpr (b:booleanExpr) (mem:Set<SignAssignment>): Set<bool> = 
    match b with
    | True -> Set.singleton true
    | False -> Set.singleton false
    | AndExpr (b1,b2) -> abstractAnd (analysisBExpr b1 mem) (analysisBExpr b2 mem)
    | OrExpr (b1,b2) -> abstractOr (analysisBExpr b1 mem) (analysisBExpr b2 mem)
    | AndAndExpr (b1,b2) -> abstractAndAnd (analysisBExpr b1 mem) (analysisBExpr b2 mem)
    | OrOrExpr (b1,b2) -> abstractOrOr (analysisBExpr b1 mem) (analysisBExpr b2 mem)
    | NotExpr b -> abstractNot (analysisBExpr b mem)
    | EqExpr (a1,a2) -> abstractEq (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | NeqExpr (a1,a2) -> abstractNeq (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | GtExpr (a1,a2) -> abstractGt (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | GteExpr (a1,a2) -> abstractGte (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | LtExpr (a1,a2) -> abstractLt (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | LteExpr (a1,a2) -> abstractLte (analysisAExpr a1 mem) (analysisAExpr a2 mem)
    | ParenBExpr b -> analysisBExpr b mem


let analysisFunctionS (action:Label) (memSet:Set<SignAssignment>): Set<SignAssignment> = 
    match action with
    | BLabel bol -> //S[[𝑏]](𝑀) = {(̂𝜎1,𝜎2) ∣ (̂𝜎1,𝜎2) ∈ 𝑀 ∧ 𝗍𝗍 ∈B[[𝑏]](𝜎1,𝜎2)}
                                  let mutable finalResult = Set.empty
                                  Set.iter
                                      (fun mem ->
                                          let result = analysisBExpr bol (Set.singleton mem)
                                          if Set.contains true result then
                                              finalResult <- Set.add mem finalResult
                                      ) memSet
                                  finalResult
    | CLabel cmd -> match cmd with
                             | Assign (s,a) -> // s[[𝑥 ∶= 𝑎]](𝑀) = {(̂ 𝜎1[𝑥 ↦ 𝑠], ̂𝜎2) ∣ (̂ 𝜎1, ̂𝜎2) ∈ 𝑀 ∧ 𝑠 ∈ ̂s[[𝑎]]( ̂ 𝜎1, ̂𝜎2)}
                                                                        updateVarSignInMem memSet s a
                             | ArrAssign (s,a1,a2) -> updateArrSignInMem memSet s a1 a2
                             | _ -> memSet
    | _ -> memSet

                                                                         

let startAnalysis (pg:List<Edge>) (abstractMem:SignAssignment) : Map<string, Set<SignAssignment>> =
    // forall 𝑞 ∈ Q ⧵ {𝑞⊳} do A(𝑞) := { } ;
    // let Q = ((List.map (fun x -> x.source) pg)@(List.map (fun x -> x.target) pg))|> List.distinct
    let Q = pg
            |> List.collect (fun x -> [x.source; x.target])
            |> Set.ofList
            |> Set.toList
    let E = pg
    // let QwithoutStartNode = List.filter (fun x -> x <> "q0") Q
    let QwithoutStartNode = List.tail Q
    // let rec initAres (q:List<string>) (ares:Map<string, Set<SignAssignment>>) : Map<string, Set<SignAssignment>> =
    //     match q with
    //     | [] -> ares
    //     | x::xs -> initAres xs (Map.add x Set.empty ares)
    // let mutable Ares:Map<string, Set<SignAssignment>> = initAres QwithoutStartNode Map.empty
    let mutable Ares:Map<string, Set<SignAssignment>> = QwithoutStartNode|> List.fold (fun acc x -> Map.add x Set.empty acc) Map.empty
    // A(𝑞⊳) :=̂Mem⊳;
    Ares <- Map.add "q0" (Set.singleton abstractMem) Ares
    // W := {𝑞⊳};
    let W:List<Node>= ["q0"]
    // while W ̸= ∅ do choose 𝑞 ∈ W; W := W\{𝑞};
    let rec whileLoop (w_temp:List<Node>) =
        match w_temp with
        | [] -> Ares
        | n::ns ->  // for all edges (𝑞_source, 𝛼, q_target) ∈ E with 𝑞_source = 𝑞
                   let rec findAllEdgesInE n E =
                        match E with
                        | [] -> []
                        | e::es -> if e.source = n then e::(findAllEdgesInE n es) else findAllEdgesInE n es
                   let edges = findAllEdgesInE n E
                   let mutable nodesToBeAdded:List<Node> = []
                   // do if ̂S[[𝛼]](A(𝑞_source)) ⊈ A(q_target) then A(q_target) := A(q_target) ∪ ̂S[[𝛼]](A(𝑞_source)); W := W∪ {q_target};
                   let rec loop edges =
                        match edges with
                        | [] -> ()
                        | e::es -> 
                                   let setFromS = (analysisFunctionS e.label (Ares |> Map.find(e.source)))
                                   let setATarget = (Ares |> Map.find(e.target))
                                   if 
                                      not(Set.isSubset setFromS setATarget)
                                   then 
                                      Ares <- Map.add e.target (Set.union setATarget setFromS) Ares              
                                      nodesToBeAdded <- nodesToBeAdded@[e.target]
                                      loop es                               
                                   else
                                      loop es
                   loop edges
                   whileLoop (ns@nodesToBeAdded)    
    whileLoop W
    
let analysis (src: string) (input: Input) : Output =
        match parse Parser.startCommand (src) with
          | Ok ast ->
                      let programGraph = astToProgramGraph (C ast) input.determinism
                      let initialNode = (List.head programGraph).source
                      let finalNode = (List.last programGraph).target
                      let nodes = startAnalysis programGraph input.assignment
                      { initial_node = initialNode
                        final_node = finalNode
                        nodes = nodes }

          | Error e -> failwith "Error parsing input"

// Run script
// ./dev/win.exe --open