import Lean
import Advent

inductive Op where
  | Add : Nat -> Op
  | Mul : Nat -> Op
  | Square 
deriving Lean.ToJson, Inhabited

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
  inspects: Nat := 0
deriving Lean.ToJson, Inhabited

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


abbrev MB α := StateM (Array Monkey) α

abbrev Monkeys := Array Monkey

def updateArr (mi: Nat) (f: Monkey -> Monkey): MB Unit := StateT.modifyGet <| fun arr => 
  let m := arr.get! mi
  ((), arr.set! mi (f m))

def pass (i: Nat) (mi: Nat): MB Unit := updateArr mi <| fun m => { m with items := m.items.push i }

def increment (mi: Nat) (x: Nat) : MB Unit := updateArr mi <| fun m => {m with inspects := m.inspects + x}

def clearItems (mi: Nat): MB Unit := updateArr mi <| fun m => {m with items := Array.empty}

def round (op: Nat -> Nat): MB Unit := do
  let monkeys <- StateT.get
  for mi in [0: monkeys.size] do 
    let monkeys <- StateT.get
    let monkey := monkeys.get! mi
    for level in monkey.items do
      let newLevel := op (monkey.op.ap level)
      if newLevel.mod monkey.div == 0
      then pass newLevel monkey.ifTrue
      else pass newLevel monkey.ifFalse
    increment mi monkey.items.size
    clearItems mi

def delim: String := String.join <| List.replicateTR 20 "-"

def rounds (op: Nat -> Nat) (i: Nat): MB Unit := for _ in [0:i] do round op

def handleRounds (op: Nat -> Nat) (n: Nat) (monkeys: Monkeys): IO Unit := do
  IO.println s!"===== {n} rounds ======"

  let (_, final) := (rounds op n).run monkeys

  let final := final.map Monkey.inspects 

  IO.println final

  let levels := final.qsort (· > ·)
                |> Array.toList 
                |> List.take 2
                |> List.prod

  IO.println levels

def lcm (x y: Nat) := x * y / x.gcd y

def main: IO Unit := do
  let blocks <- readBlocks 11
  let monkeys <- match (blocks.mapM parse) with
  | Except.ok b => pure b.toArray
  | Except.error s => throw (IO.userError s)

  let m := monkeys.map (·.div) |> (·.foldl lcm 1)

  handleRounds (· / 3) 20 monkeys
  handleRounds (· % m) 10000 monkeys
