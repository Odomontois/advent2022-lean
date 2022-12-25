import Advent

def crop (lst: List α) := (lst.dropLast.drop 1).toArray

def Sim := Array <| Array <| Array Bool deriving Repr, ToString

def Sim.mark (s: Sim) (i j k : Nat): Sim := s.modify i (·.modify j (·.set! k true))
def Sim.allow (s: Sim) (i j k: Nat): Bool := !(Array.get! s i)[j]![k]!

open Array (mkArray)

def fillInit (xs: Array <| Array Char): (Sim × Nat × Nat × Nat) := go 
where go: Id _ := do
  let n := xs.size
  let m := xs[0]!.size
  let l := n.lcm m
  let mut s: Sim := mkArray n <| mkArray m <| mkArray l false
  for i in finRange xs.size do
    let row := xs[i]
    for j in finRange row.size do
      let c := row[j]
      if let some (dx, dy) := match c with 
        | '>' => some (0, 1)
        | '<' => (0, m - 1)
        | 'v' => (1, 0)
        | '^' => (n - 1, 0)
        | _   => none
      then for k in [0:l] do
        let i' := (i + dx * k) % n
        let j' := (j + dy * k) % m
        s := s.mark i' j' k
  return (s, n, m, l)


inductive State 
| Start  (step: Nat)
| Inside (step x y: Nat)

open State
def walk (sim: Sim) (n m l: Nat) (phases := 3): List Nat :=
  (List.range phases).scanl (fun step phase => go sim (Queue.empty.send <| State.Start step) phase 10000000) 0
where

  sendMark q s step (ps : List (Nat × Nat)): (Queue State × Sim) := 
    let k := (step + 1) % l
    let ps := ps.eraseReps.filter (fun (i, j) => if i < n && j < m then s.allow i j k else false)
    let s := ps.foldl (fun s (i, j) => s.mark i j k) s
    let q := ps.foldl (fun q (i, j) => q.send (Inside (step + 1) i j)) q
    (q, s)
  init (phase: Nat) := if phase % 2 == 0 then (0, 0) else (n - 1, m - 1)
  go s q phase
  | 0 => 0
  | fuel + 1 => match q.pull with
    | none => 0
    | some ((.Start step), q) => 
      let (q, s) := sendMark q s step [init phase]
      let q := q.send (Start (step + 1))
      go s q phase fuel
    | some ((.Inside step x y), q) => 
      if (x, y) == init (phase + 1) then step + 1 else 
        let (q, s) := sendMark q s step [(x - 1, y), (x, y), (x, y - 1), (x + 1, y), (x, y + 1)]
        go s q phase fuel


def main: IO Unit := do
  let lines <- readLines 24
  let xs := (crop lines).map (crop ·.toList)
  xs.forM <| IO.println
  let (sim, n, m, l) := fillInit xs
  IO.println <| walk sim n m l

  