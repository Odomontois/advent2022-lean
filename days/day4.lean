import Advent.Read

def Pair (α : Type) :=  α × α
 
def parsePair  (f : String -> Option α) (sep s: String) : Option (Pair α) := do
  match (s.splitOn sep).mapM f with
  | some [x, y] => some (x, y)
  | _ => none

def Assignment := parsePair (parsePair (·.toNat?) "-") ","

def contains: Pair Nat -> Pair Nat -> Bool
| (a1, b1), (a2, b2) => a1 <= a2 && b2 <= b1

def before : Pair Nat -> Pair Nat -> Bool
| (_, b1), (a2, _) => b1 < a2

def anyOrder (f: α -> α -> Bool):  Pair α -> Bool
| (i1, i2) => f i1 i2 || f i2 i1

def main : IO Unit := do
 let lines <- readLines 4
 let asssignments := lines.filterMap Assignment
 let count (p: Pair (Pair Nat) -> Bool): Nat := (asssignments.filter p).length
 IO.println (count (anyOrder contains))
 IO.println (count (not ∘ anyOrder before))
