import Advent
import Std

structure Map where
  n: Nat
  m: Nat
  elements :Array (Array Char)
  hportals :Array (Nat × Nat)
  vportals :Array (Nat × Nat)
  trace :Array (Array Char) := elements
  gone: Array (Nat × Nat) := Array.empty
  cubic: Bool := false
deriving Inhabited, Lean.ToJson, Repr, BEq

inductive Dir | R | D | L | U
deriving Inhabited, Lean.ToJson, Repr, BEq, Ord

namespace Dir
def rechtsaf: Dir -> Dir
| R => D
| D => L
| L => U
| U => R

def linksaf: Dir -> Dir
| D => R
| L => D
| U => L
| R => U

def code: Dir -> Fin 4 
| R => 0
| D => 1
| L => 2
| U => 3

theorem leftRight (d: Dir): d.linksaf.rechtsaf = d := by
  cases d <;> simp [linksaf, rechtsaf] 

theorem rightLeft (d: Dir): d.rechtsaf.linksaf = d := by
  cases d <;> simp [linksaf, rechtsaf]

def parse: Parse Dir := Parse.choose [("R", R), ("D", D), ("U", U), ("L", L)] 
end Dir
open Dir
namespace Map 
variable (map: Map)

def get (x y: Nat): Char := map.elements[x]![y]!  

def start: (Nat × Nat) := (0, (map.elements[0]!.indexOf? '.').elim 0 (· + 0) )

def step (x y: Nat)(d: Dir): (Nat × Nat) := 
  let (x', y') := move x y d 
  let (x', y') := 
    if x' == map.m || y' == map.n then teleport x y d
    else if map.get x' y' == ' ' then teleport x y d
    else (x', y')
  if map.elements[x']![y']! == '#' then (x, y) else (x', y')
where 
  move 
  | x, y, R => (x, y + 1)
  | x, y, D => (x + 1, y)
  | x, 0, L => (x, map.n)
  | x, y + 1, L =>(x, y)
  | 0, y, U => (map.m, y)
  | x + 1, y, U => (x, y)
  teleport
  | x, _, R => (x, map.hportals[x]!.1)
  | x, _, L => (x, map.hportals[x]!.2)
  | _, y, D => (map.vportals[y]!.1, y)
  | _, y, U => (map.vportals[y]!.2, y)

def stepTrace (d: Dir): (Map × Nat × Nat) -> (Map × Nat × Nat)
| (map, (x, y)) =>  
  let char := match d with 
  | D => 'V'
  | R => '>'
  | L => '<'
  | U => '^'
  let (x', y') := map.step x y d
  ({map with 
    trace := map.trace.modify x (·.set! y char)
    gone := map.gone.push (x, y)
  }, (x', y'))
  

def walk( xs: List (Nat × Dir)): (Map × (Nat × Nat)) := 
  xs.foldl (fun (m, p) (c, d) => compN (stepTrace d) c (m, p)) (map, map.start)

def make (ls: List String): Map := 
  let elements := (ls.map (·.toList.toArray)).toArray
  let n := elements.foldl (max · ·.size) 0
  let m := elements.size
  let elements := elements.map (·.autoGrow n ' ')
  {elements, n, m, hportals:= horPortals elements , vportals:=  verPortals elements}
where 
  horPortals (elems: Array (Array Char)): Array  (Nat × Nat) := elems.map <| fun arr => 
    let x := (arr.findIdx? (· != ' ')).getD 0
    let y := arr.size -  (arr.reverse.findIdx? (· != ' ')).getD 0 - 1
    (x, y)

  verPortals elems := elems.transpose |> horPortals

def strings := map.trace.map (String.mk <| ·.toList)
end Map

def parseCommande: Parse (List (Nat × Dir)) :=  do
  let init <- Parse.nat
  let ls <- parseOne.rep
  let tts := ls.scanl (fun (_, d) (x, tl) => (x, if tl then d.linksaf else d.rechtsaf) ) (init, R)
  return tts
where
  parseOne := do
  let turn <- Parse.choose [("L", true), ("R", false)]
  let cnt <- Parse.nat  
  return (cnt, turn)

def main: IO Unit := do
  let lines <- readLines 22
  let map := lines.takeWhile (· != "")
  let last := lines.dropWhile (· != "") |> (·[1]!)

  map.forM IO.println
  IO.println last
  let x := last.split (·.isAlpha) |> (·.mapM (·.toNat?)) |> (·.map (·.sum))|> (·.getD 0)
  IO.println x
  let map := Map.make map
  map.strings.forM IO.println
  let coms <- parseCommande.runIO last
  IO.println map.start

  let (map, x, y) := map.walk coms
  IO.println coms
  let d := coms.getLast?.get!.2
  IO.println (x, y, d)
  IO.println map.gone
  map.strings.forM IO.println
  let code := (x + 1) * 1000 + (y + 1) * 4 + d.code
  IO.println code

  