import Advent
open Lean (HashSet)
structure Cube where
  x: Int
  y: Int 
  z: Int
deriving Lean.ToJson, Inhabited, Hashable, BEq
namespace Cube
variable (c: Cube)

def parse: Parse Cube := open Parse in do
  let x <- int
  str ","
  let y <- int
  str ","
  let z <- int
  return ⟨x, y, z⟩

def neighbors: List Cube := 
  let ⟨x, y, z⟩ := c
  [
    ⟨x - 1, y, z⟩,
    ⟨x + 1, y, z⟩,
    ⟨x, y - 1, z⟩,
    ⟨x, y + 1, z⟩,
    ⟨x, y, z - 1⟩,
    ⟨x, y, z + 1⟩
  ] 

def sides(cs: List Cube): Nat := 
  let ss := HashSet.empty.insertMany cs
  let side (c: Cube) := if ss.contains c then 0 else 1
  
  (cs.bind neighbors).foldl (· + side ·) 0



def inside (c cl ch: Cube) : Bool := 
  let inBy f := let d := f c ; d >= f cl && d <= f ch
  inBy x && inBy y && inBy z



def exterior (cs: List Cube): HashSet Cube := 
    let minBy f := (cs.map f).minimum?.getD 0 - 1
    let maxBy f := (cs.map f).maximum?.getD 0 + 1
    let cl : Cube := ⟨minBy x, minBy y, minBy z⟩
    let ch : Cube := ⟨maxBy x, maxBy y, maxBy z⟩
    let q := Queue.empty.send cl
    let h := HashSet.empty.insert cl
    let ss := HashSet.empty.insertMany cs
    
    go q h ss cl ch 1000000
where 
  go q h ss cl ch fuel := match fuel with
  | 0 => h
  | fuel + 1 => 
    if let some (c, q) := q.pull then
      let next := c.neighbors.filter (fun c => c.inside cl ch && !(h.contains c) && !(ss.contains c))
      let h := h.insertMany next
      let q := q.sendMany next
      go q h ss cl ch fuel
    else h

def externalSides(cs: List Cube): Nat := 
  let ext := exterior cs

  let side (c: Cube) := if ext.contains c then 1 else 0
  
  (cs.bind neighbors).foldl (· + side ·) 0

end Cube

def main: IO Unit := do
  let lines <- readLines 18
  let cubes <- lines.mapM Cube.parse.runIO

  IO.println <| Cube.sides cubes
  IO.println <| Cube.externalSides cubes