module ProgramVerification

open System
open Predicate.AST

(*
    This defines the input and output for the program verification analysis.
    Please do not change the definitions below as they are needed for the
    validation and evaluation tools!
*)

type Input = unit

type Output =
    { verification_conditions: List<SerializedPredicate> }

let mutable freshIdx = - 1

let fresh () =
    freshIdx <- freshIdx + 1
    $"_f{freshIdx}"

let analysis (src: string) (input: Input) : Output =
    let (P, C, Q) =
        match Predicate.Parse.parse src with
        | Ok (AnnotatedCommand (P, C, Q)) -> P, C, Q
        | Error e ->
            failwith
                $"Failed to parse.\n\nDid you remember to surround your program with predicate blocks, like so?\n\n  {{ true }} skip {{ true }}\n\n{e}"

    let rec subP (varTobeChanged:string, freshVar: string, input) = 
        match input with
        | Bool _ -> input
        | RelationalOp (lhs, op, rhs) -> RelationalOp (subA(varTobeChanged, freshVar, lhs), op, subA(varTobeChanged, freshVar, rhs))
        | BooleanOp (lhs, op, rhs) -> BooleanOp (subP(varTobeChanged, freshVar, lhs), op, subP(varTobeChanged, freshVar, rhs))
        | Exists (x, pred) -> if x = varTobeChanged then Exists (freshVar, subP(varTobeChanged, freshVar, pred)) else
                                                    Exists (x, subP(varTobeChanged, freshVar, pred))
        | Forall (x, pred) -> if x = varTobeChanged then Forall (freshVar, subP(varTobeChanged, freshVar, pred)) else
                                                    Forall (x, subP(varTobeChanged, freshVar, pred))
        | Not pred -> Not (subP(varTobeChanged, freshVar, pred))
    and subA (varTobeChanged:string, freshVar: string, input) =
        match input with
        | Variable x -> if x = varTobeChanged then Variable freshVar else Variable x
        | Number c -> Number c
        | LogicalVariable x -> LogicalVariable x
        | Array (x, idx) -> Array (x, subA(varTobeChanged, freshVar, idx))
        | LogicalArray (x, idx) -> LogicalArray (x, idx)
        | Binary (lhs, op, rhs) -> Binary (subA(varTobeChanged, freshVar, lhs), op, subA(varTobeChanged, freshVar, rhs))
        | Function f -> match f with
                                  | Division (lhs, rhs) -> Function (Division (subA(varTobeChanged, freshVar, lhs), subA(varTobeChanged, freshVar, rhs)))
                                  | Min (lhs, rhs) -> Function (Min (subA(varTobeChanged, freshVar, lhs), subA(varTobeChanged, freshVar, rhs)))
                                  | Max (lhs, rhs) -> Function (Max (subA(varTobeChanged, freshVar, lhs), subA(varTobeChanged, freshVar, rhs)))
                                  | Count (x, idx) -> Function (Count (x, subA(varTobeChanged, freshVar, idx)))
                                  | LogicalCount (x, idx) -> Function (LogicalCount (x, idx))
                                  | Length x -> Function (Length freshVar)
                                  | LogicalLength x -> Function (LogicalLength x)
                                  | Fac x -> Function (Fac (subA(varTobeChanged, freshVar, x)))
                                  | Fib x -> Function (Fib (subA(varTobeChanged, freshVar, x)))
                                    
    let rec doneGC GC =
        match GC with
        | Guard (b, C) -> Not b
        | Choice (gc1, gc2) -> BooleanOp (doneGC(gc1), LAnd, doneGC(gc2))


    let rec sp (C: Command, P: Predicate): Predicate =
        match C with
        | Skip -> P
        | Assign (x, a) -> 
                                          let freshVar = fresh ()
                                          Exists (freshVar, BooleanOp (subP(x, freshVar, P), LAnd, RelationalOp (Variable x, Eq, subA(x, freshVar, a))))
        | ArrayAssign (a, idx, e) -> 
                                          let freshVar = fresh ()
                                          Exists (freshVar, BooleanOp (subP(a, freshVar, P), LAnd, RelationalOp (Array (a, idx), Eq, subA(a, freshVar, e))))
        | Sep (C1, C2) -> sp(C2, sp(C1, P))
        | If (GC) -> guard_sp(GC, P)
        | Do (inv, GC) -> BooleanOp (inv, LAnd, doneGC(GC)) 
    and guard_sp = function
        | Guard (b, C1), P -> sp(C1, BooleanOp (b, LAnd, P))
        | Choice (gc1, gc2), P -> BooleanOp (guard_sp(gc1, P), LOr, guard_sp(gc2, P))


    let rec vc (C: Command, R: Predicate) : List<Predicate> =
        match C with
        | Skip -> []
        | Assign (x, e) -> []
        | ArrayAssign (a, idx, e) -> []
        | Sep (C1, C2) -> vc(C1,R) @ vc(C2,sp(C1,R))
        | If (GC) -> guard_vc(GC, R)
        | Do (inv, GC) -> (BooleanOp (R, Implies, inv) :: [BooleanOp(guard_sp(GC, inv),Implies,inv)]) @ guard_vc((GC), inv)
    and guard_vc = function
        | Guard (b, C1), R -> vc(C1, BooleanOp (b, LAnd, R))
        | Choice (gc1, gc2), R -> guard_vc(gc1, R) @ guard_vc(gc2, R)



    let verification_conditions: List<Predicate> = [BooleanOp (sp (C, P), Implies, Q)] @ vc(C, P)

    // Let this line stay as it is.
    { verification_conditions = List.map serialize_predicate verification_conditions }

// Run script
// ./dev/win.exe --open
// dotnet run program-verification '{((((a > 0) && (b = 0)) && (c < 0)) && (d = 0))} if ((65 <= d) && true) -> b := c fi ; if !false -> c := d fi ; c := 36 ; if ((99 = b) || (c > 59)) -> b := d fi ; if (59 = a) -> d := c fi ; if (b < 27) -> d := b fi ; b := 81 ; b := -86 ; if (a != c) -> b := b fi ; a := 39 {true}' "{determinism: {Case:'NonDeterministic'}}"
// {x>0} skip {x>=0}

// {((((a > 0) && (b = 0)) && (c = 0)) && (d < 0))} d := b ; b := d ; if (d <= d) -> c := -77 fi {((((a = 0) && (b = 0)) && (c > 0)) && (d = 0))}
// ((exists _f2 :: (((d <= d) & (exists _f1 :: ((exists _f0 :: (((((a > 0) && (_f1 = 0)) && (_f2 = 0)) && (_f0 < 0)) & (d = _f1))) & (b = d)))) & (c = -77))) ==> ((((a = 0) && (b = 0)) && (c > 0)) && (d = 0)))
// ((exists _f0 :: (((d <= d) & (exists _f1 :: ((exists _f2 :: (((((a > 0) && (_f1 = 0)) && (_f0 = 0)) && (_f2 < 0)) & (d = _f1))) & (b = d)))) & (c = -77))) ==> ((((a = 0) && (b = 0)) && (c > 0)) && (d = 0)))