import Advent
import Std

open Lean (HashMap)

inductive Op | plus | minus | mul | div 
deriving Inhabited, Lean.ToJson, Hashable, BEq

class Ops (α: Type) extends Add α, Mul α, Div α, Sub α

instance : Ops Int where

namespace Op
def parse : Parse Op := Parse.choose [
  ("+", plus),
  ("-", minus),
  ("*", mul),
  ("/", div)
]

def apply [Ops α] (x y: α): Op -> α 
| plus => x + y
| minus => x - y
| div => x / y
| mul => x * y
end Op

inductive Monkey (α: Type)
| Ready (value: α)
| Calculate (op: Op) (l r: String)
deriving Inhabited, Lean.ToJson, Hashable, BEq

namespace Monkey

def map(f: α -> β): Monkey α -> Monkey β 
| Ready x => Ready (f x)
| Calculate op l r => Calculate op l r

def parse: Parse (String × Monkey Int) := open Parse in do
  let self <- name
  str ": "
  let monkey <- 
    try 
      let num <- int
      pure <| Monkey.Ready num
    catch _ => 
      let left <- name
      ws
      let op <- Op.parse
      ws
      let right <- name
      pure <| Monkey.Calculate op left right
  return (self, monkey)
where 
  name := Parse.seg (·.isAlpha) (err := "alpha")


-- instance [Ops α] : Ops (Monkey (Option α)) where
--   add x y := match x, y with
--     | Ready (some x), Ready (some y) => Ready (some (x + y))
--     | _ => Calculate Op.plus x y

end Monkey


inductive Expr (α: Type)
| Lit (value: α)
| Bin (op: Op) (l r: Expr α)
deriving Inhabited, Lean.ToJson, Hashable, BEq

namespace Expr

def collect (monkeys: String -> Option (Monkey α)): Option (Expr α) :=
  go "root" 100000000
where 
  go name 
  | 0 => none
  | fuel + 1 => monkeys name >>= fun m => open Monkey Expr in match m with
    | Ready val => some <| Lit val
    | Calculate op l r => do
      let l <- go l fuel
      let r <- go r fuel
      return Bin op l r

def calculateWith [Ops β] (f: α -> β) : Expr α -> β
  | Lit val => f val
  | Bin op l r => op.apply (l.calculateWith f) (r.calculateWith f)

def calculate [Ops α]: Expr α -> α := calculateWith id

def collectFormula (monkeys: String -> Option (Monkey α)): Option (Expr (Option α)) := open Monkey in do
  let root <- monkeys "root"
  let root: Monkey (Option α) := match root with
    | Calculate _ l r => Calculate Op.minus l r 
    | Ready x => Ready (some x)

  collect <| fun name => match name with 
  | "root" => root
  | "humn" => some <| Ready none
  | _ => (monkeys name).map (·.map some)
end Expr

def Poly := Array Int

namespace Poly

def autoGrow (p: Poly) (n: Nat): Poly :=
  if p.size < n then p.append (Array.mkArray (n - p.size) 0) else p

def zipAutoGrow (f: Int -> Int -> Int) (xs ys: Poly): Poly :=
  let xs := xs.autoGrow ys.size
  let ys := ys.autoGrow xs.size
  xs.zipWith ys f

instance : Add Poly where add := zipAutoGrow (· + ·)
instance : Sub Poly where sub := zipAutoGrow (· - ·)
instance : Mul Poly where 
  mul (xs: Array Int) (ys: Array Int): Id Poly := do
  let mut res := Array.mkArray (xs.size + ys.size - 1) 0
  for i in [0:xs.size] do 
    let x := xs[i]!
    for j in [0:ys.size] do
      let y := ys[j]!
      res := res.modify (i + j) (· + x * y)
  res
    
  instance : ToString Poly where
    toString (xs: Array Int) := String.join <| ((List.range xs.size).reverse.map (fun i => s!"{xs[i]!}x^{i}")).intersperse " + "
end Poly

structure Ratp where
  num : Poly
  den : Poly

namespace Ratp 
  def const (x: Int): Ratp := ⟨ #[x], #[1] ⟩
  def x: Ratp := ⟨ #[0, 1], #[1] ⟩

  instance: Ops Ratp where
    add x y := ⟨ x.num * y.den + y.num * x.den, x.den * y.den ⟩
    sub x y := ⟨ x.num * y.den - y.num * x.den, x.den * y.den ⟩
    mul x y := ⟨ x.num * y.num, x.den * y.den ⟩
    div x y := ⟨ x.num * y.den, x.den * y.num ⟩

  instance : ToString Ratp where
    toString |⟨x, y⟩ => s!"({x})/({y})"

end Ratp
   


def main: IO Unit := do
  let lines <- readLines 21
  let monkeys <- lines.mapM Monkey.parse.runIO
  let monkeys: HashMap _ _ := HashMap.ofList monkeys

  let full := (Expr.collect monkeys.find?).get!

  IO.println <| full.calculate

  let full' := (Expr.collectFormula monkeys.find?).get!
  let res := full'.calculateWith <| (·.elim Ratp.x Ratp.const)
  let numer: Array Int := res.num
  let solution <- 
    if numer.size == 2 then pure (-numer[0]! / numer[1]!) else throw (IO.userError "help")
  IO.println solution

  
