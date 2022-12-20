import Advent 

open Lean (HashMap HashSet)


structure ArrArr  (α : Type) where
  elements: Array (Array (Nat × α))
  positions: Array (Nat × Nat)
deriving BEq, Lean.ToJson, Repr

namespace ArrArr
  variable [Inhabited α] (arr: ArrArr α)

  def fromList (blockSize: Nat) (ls: List α): ArrArr α :=
    let lse := ls.enum.group blockSize
    let elements := (lse.map (·.toArray)).toArray
    let positions := List.toArray <| lse.enum.bind <| fun (i, b) => b.enum.map <| fun (j, _) => (i, j)
    ⟨elements, positions⟩

  def toList: List α := 
    arr.elements.toList.bind ( ·.toList.map (·.snd) )




  def relativePos (i: Nat): Id Nat := do
    let (bi, j) := arr.positions[i]!
    let mut res := j
    for k in [0:bi] do
      res := res + arr.elements[k]!.size
    return res

  private def shiftPositions 
    (pos: Array (Nat × Nat)) 
    (block: Array (Nat × α)) 
    (start: Nat) 
    (f: Nat -> Nat): Id (Array (Nat × Nat)) := do
    let mut positions := pos
    for k in [start:block.size] do
      let (t, _) := block[k]!
      positions := positions.modify t <| fun (i, j) => (i, f j) 
    positions
    
  def remove (i: Nat): Id (ArrArr α × α) := do
    let mut ⟨elements, positions⟩ := arr
    let (bi, j) := positions[i]!
    let (_, el) := elements[bi]![j]!
    elements := elements.modify bi (·.eraseIdx j)
    positions := shiftPositions positions elements[bi]! j (· - 1)
    return (⟨elements, positions⟩, el)

  def absolutePos (i: Nat): Id (Nat × Nat) := do
    let mut i := i
    let elements := arr.elements
    for k in [0:elements.size] do
      let s := elements[k]!.size
      if i < s then
        return (k, i)
      else i := i - s
    return (0, 0)

  def insert (i el: Nat) (x: α) : Id (ArrArr α) := do
    let (bi, j) := arr.absolutePos i
    let mut ⟨elements, positions⟩ := arr
    positions := positions.set! el (bi, j)
    elements := elements.modify bi (·.insertAt! j (el, x))
    positions := shiftPositions positions elements[bi]! (j + 1) (· + 1)
    return ⟨elements, positions⟩

  def removeInsert (i: Nat) (f: Nat -> α -> Nat) : ArrArr α :=
    let rpos := arr.relativePos i
    let (arr, x) := arr.remove i
    let newPos := f rpos x
    arr.insert newPos i x

  def byKey (i: Nat): α := 
    let (i, j) := arr.positions[i]!
    let (_, x) := arr.elements[i]![j]!
    x

  def byPos (i: Nat): α := 
    let (i, j) := arr.absolutePos i
    arr.elements[i]![j]!.snd

end ArrArr


def solution (count: Nat) (input: List Int): IO Unit := do
  let blockSize := input.length.toFloat.sqrt.ceil.toUInt32.toNat
  let mut aa := ArrArr.fromList blockSize input
  let n := input.length
  let iz : Nat  := if let some x := input.toArray.indexOf? 0 then x else 0
  let f (old: Nat) (i: Int) := 
    let d := (i.abs / (n - 1) + 1) * (n - 1)
    ((old + i + d) % (n - 1)).toNat
  for _ in [0:count] do
    for (i, _) in input.enum do
      aa := aa.removeInsert i f
  let zp: Nat := aa.relativePos iz
  let mut res := 0
  for y in [1000, 2000, 3000] do 
    let xp := (zp + y) % n
    let v := aa.byPos xp
    IO.println s!"{y}-th number is {v}"
    res := res + v
  IO.println s!"result is {res}"



def main : IO Unit := do
  let lines <- readLines 20
  let input: List Int := lines.mapM (·.toInt?) |> (·.get!)
  IO.println "PART 1"
  solution 1 input
  IO.println "PART 2"
  let input' := input.map (· * 811589153)
  solution 10 input'

  -- let ixs := List.range input.length
  -- IO.println <| ixs.map aa.value
  -- IO.println <| ixs.map aa.relativePos
  -- IO.println <| aa
  -- let (aa, x) := aa.remove 0
  -- IO.println <| aa
  -- let aa := aa.insert 0 1

  -- IO.println aa