import Advent

open Lean (HashSet)

def Map := Array (Array Char)

instance : Lean.ToJson Map where
  toJson (m: Map) := Lean.ToJson.toJson <| m.toList.map (String.mk ∘ Array.toList)

def Map.at (map: Map) (x y: Nat): Char :=
 let row := ((map.get? x).orElse (fun _ => panic! s!"row {x}")).get!
 ((row.get? y).orElse (fun _ => panic! s!"row {x} col {y}")).get!

def Map.lookup (map: Map) (symbs: List Char): List (Nat × Nat) := 
  map.toList.enum.bind <| 
  fun (i, row) => row.toList.enum.bind <|
  fun (j, c) => if symbs.contains c then [(i, j)] else []
  

def allowed (c c' : Char): Bool := 
  let c: Int :=  (if c == 'S' then 'a' else c).toNat
  let c': Int :=  (if c' == 'E' then 'z' else c').toNat
  (c' - c) <= 1

def Map.good (map: Map) (i j: Nat): Bool := 
  let n := map.size
  let m := (map.get! 0).size
  i >= 0 && j >= 0 && i < n && j < m 

def next (map: Map) (x y: Nat): List (Nat × Nat) := 
  let cur := map.at x y
  [(x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)].filter <|
    fun (i, j) => if (i, j) != (x, y) && map.good i j
                  then allowed cur (map.at i j)
                  else false
      
def Seen := HashSet (Nat × Nat) 

instance : Lean.ToJson Seen where
  toJson := Lean.ToJson.toJson ∘ HashSet.toList

structure Item where
  steps: Nat
  x: Nat
  y: Nat
deriving Lean.ToJson

structure SState where
  map: Map 
  q: Queue Item 
  target: (Nat × Nat)
  seen: Seen
deriving Lean.ToJson

def Map.start (symbs: List Char) (map: Map) : SState := 
  let starts := map.lookup symbs
  let q := starts.foldl (fun q (x, y) => q.send ⟨0, x, y⟩) Queue.empty
  let seen := starts.foldl (·.insert ·) HashSet.empty
  let target := (map.lookup ['E']).head!
  {
    map := map
    q := q
    seen := seen
    target := target
  }

abbrev Search α := StateM SState α

def pull: Search (Option Item) := 
  StateT.modifyGet <| fun s => 
    match s.q.pull with 
    | some (x, q) => (some x, {s with q := q})
    | none => (none, s) 

def send (item: Item): Search Unit := 
  StateT.modifyGet <| fun s => 
    let xy := (item.x, item.y)
    let next :=  
      if s.seen.contains xy then s else 
      {s with 
        q := s.q.send item
        seen := s.seen.insert xy
      }
    ((), next)

def markSeen (i j: Nat): Search Unit :=
  StateT.modifyGet <| fun s => 
    ((), {s with seen := s.seen.insert (i, j)})

partial def go: Search (Option Nat) := do
  if let some ⟨steps, x, y⟩ ← pull
  then do
    let st <- StateT.get
    if (x, y) == st.target 
    then return some steps 
    else do
      for (i, j) in next st.map x y do
        if !st.map.good i j then panic! s!"not good {i} {j}"
        send ⟨ steps + 1, i, j ⟩
      go
  else return none




def main : IO Unit := do
  let map <- readLines 12
  let map: Map := map.toArray.map (·.toList.toArray)
  IO.println (map.map (·.size))
  let result1 := go.run (map.start ['S'])
  IO.println result1.fst
  let result2 := go.run (map.start ['S', 'a'])
  IO.println result2.fst