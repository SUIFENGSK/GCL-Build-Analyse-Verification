// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module AST

type expr =
    | Num of float
    | TimesExpr of (expr * expr)
    | DivExpr of (expr * expr)
    | PlusExpr of (expr * expr)
    | MinusExpr of (expr * expr)
    | PowExpr of (expr * expr)
    | UPlusExpr of (expr)
    | UMinusExpr of (expr)
    | RootExpr of (expr)
    | LogExpr of (expr)

// Task 1
// a  ::=  n  |  x  |  A[a]  |  a + a  |  a - a  |  a * a  |  a / a  |  - a  |  a ^ a  |  (a)
type arithmeticExpr = 
    | Num of float
    | Str of string
    | ArrAccess of (string * arithmeticExpr)
    | PlusExpr of (arithmeticExpr * arithmeticExpr)
    | MinusExpr of (arithmeticExpr * arithmeticExpr)
    | TimesExpr of (arithmeticExpr * arithmeticExpr)
    | DivExpr of (arithmeticExpr * arithmeticExpr)
    | UPlusExpr of (arithmeticExpr)
    | UMinusExpr of (arithmeticExpr)
    | PowExpr of (arithmeticExpr * arithmeticExpr)
    | ParenAExpr of (arithmeticExpr)

// b  ::=  true  |  false  |  b & b  |  b | b  |  b && b  |  b || b  |  ! b
//    |  a = a  |  a != a  |  a > a  |  a >= a  |  a < a  |  a <= a  |  (b)
type booleanExpr = 
    | True
    | False
    | AndExpr of (booleanExpr * booleanExpr)
    | OrExpr of (booleanExpr * booleanExpr)
    | AndAndExpr of (booleanExpr * booleanExpr)
    | OrOrExpr of (booleanExpr * booleanExpr)
    | NotExpr of (booleanExpr)
    | EqExpr of (arithmeticExpr * arithmeticExpr)
    | NeqExpr of (arithmeticExpr * arithmeticExpr)
    | GtExpr of (arithmeticExpr * arithmeticExpr)
    | GteExpr of (arithmeticExpr * arithmeticExpr)
    | LtExpr of (arithmeticExpr * arithmeticExpr)
    | LteExpr of (arithmeticExpr * arithmeticExpr)
    | ParenBExpr of (booleanExpr)

// C  ::=  x := a  |  A[a] := a  |  skip  |  C ; C  |  if GC fi  |  do GC od
// GC ::=  b -> C  |  GC [] GC
type command = 
    | Assign of (string * arithmeticExpr)
    | ArrAssign of (string * arithmeticExpr * arithmeticExpr)
    | Skip
    | Sequence of (command * command)
    | If of guardedCommand
    | Do of guardedCommand
and guardedCommand =
    | Condition of (booleanExpr * command)
    | Choice of (guardedCommand * guardedCommand)