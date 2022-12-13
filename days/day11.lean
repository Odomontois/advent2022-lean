import Lean
import Advent

inductive Op where
  | Add : Nat -> Op
  | Mul : Nat -> Op
  | Square 
deriving Lean.ToJson

def Op.ap (x: Nat): Op -> Nat
| Add y => x + y 
| Mul y => x * y
| Square => x * x

structure Monkey where
  items: Array Nat
  op: Op
  div: Nat
  ifTrue: Nat
  ifFalse: Nat
deriving Lean.ToJson

def Option.toExcept (o: Option α) (b: β ): Except β α := match o with
  | some x => pure x
  | none   => throw b

def psOne (p: String) (s: String): Option String := 
  match s.split (· == ':') with
    | [s, r] => if s.trimLeft == p then r.trim else none
    | _ => none

def parse(l: List String): Except String Monkey := do
  let ps {α} (p: String) (f: String -> Option α) : Except String α := ((l.firstM (psOne p)).bind f).toExcept p
  let pss {α} (p: String) (f: List String -> Option α) : Except String α := 
    ((l.firstM (psOne p)).bind (fun s => (f (s.splitOn " ")))).toExcept p
  

  let items <- ps "Starting items" <| (· |> (·.splitOn ", ") |> List.mapM (·.toNat?) |> Option.map (·.toArray))
  let op: Op <- pss "Operation" <| fun strs =>  
      match strs with
        | ["new", "=", "old", "*", "old"] => Op.Square
        | ["new", "=", "old", sign, operand] => match sign with
          | "+" => operand.toNat?.map Op.Add
          | "*" => operand.toNat?.map Op.Mul
          | _ => none
        | _ => none
  let div <- pss "Test" <| fun strs => 
      match strs with 
      | ["divisible", "by", op] => op.toNat?
      | _ => none
  let ifmonkey (cond: String) := pss ("If " ++ cond) <| fun strs => 
      match strs with 
      | ["throw", "to", "monkey", n] => n.toNat?
      | _ => none
  let ifTrue <- ifmonkey "true"
  let ifFalse <- ifmonkey "false"
  pure { items := items, op := op, div := div, ifTrue := ifTrue, ifFalse := ifFalse }


def delim: String := String.join <| List.replicateTR 20 "-"

def main: IO Unit := do
  let blocks <- readBlocks 11

  for b in blocks do
    IO.println (parse b)
    
    IO.println delim