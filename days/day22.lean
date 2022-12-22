import Advent
import Std

open Lean (RBMap HashMap)

inductive Dir | R | D | L | U
deriving Inhabited, Lean.ToJson, Repr, BEq, Ord, Hashable

inductive Turn | Straight| Linksaf| Rechtsaf
deriving Inhabited, Lean.ToJson, Repr, BEq, Ord, Hashable

structure Side where
  x: Nat
  y: Nat
  dir: Dir
deriving BEq, Ord, Hashable, Lean.ToJson, Repr

abbrev Glue := Side × Side

structure Map where
  n: Nat
  m: Nat
  elements: Array (Array Char)
  side: Nat
  glues: Array Glue
  trace :Array (Array Char) := elements
deriving Inhabited, Lean.ToJson, Repr, BEq



open Turn
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

def turn: Turn -> Dir -> Dir
| Turn.Straight  => id
| Turn.Linksaf => linksaf
| Turn.Rechtsaf=> rechtsaf 

def code: Dir -> Fin 4 
| R => 0
| D => 1
| L => 2
| U => 3

def back: Dir -> Dir 
| R => L
| L => R
| U => D
| D => U

theorem leftRight (d: Dir): d.linksaf.rechtsaf = d := by
  cases d <;> simp [linksaf, rechtsaf] 

theorem rightLeft (d: Dir): d.rechtsaf.linksaf = d := by
  cases d <;> simp [linksaf, rechtsaf]

theorem backBack (d: Dir): d.back.back = d := by
  cases d <;> simp [back]

def parse: Parse Dir := Parse.choose [("R", R), ("D", D), ("U", U), ("L", L)] 
end Dir
open Dir
namespace Map 
variable (map: Map)

def get (x y: Nat): Char := map.elements[x]![y]!  


def step (x y: Nat) (d: Dir): (Dir × Nat × Nat) := 
  let (x', y') := move x y d 
  let tele := if x' == map.m || y' == map.n then true else map.get x' y' == ' '
  let (d', x', y') := if tele then teleport x y d else (d, x', y')
  if map.elements[x']![y']! == '#' then (d, x, y) else (d',x', y')
where 
  move 
  | x, y, R => (x, y + 1)
  | x, y, D => (x + 1, y)
  | x, 0, L => (x, map.n)
  | x, y + 1, L =>(x, y)
  | 0, y, U => (map.m, y)
  | x + 1, y, U => (x, y)
  invert u := map.side - u - 1
  leave x y: Dir -> Nat
  | R => x
  | L => invert x
  | U => y
  | D => invert y  
  enter q : Dir -> (Nat × Nat)
  | R => (q, invert 0)
  | L => (invert q, 0)
  | U => (0, q)
  | D => (invert 0, invert q)
  findGlue x y d : Option Side := 
    let s := ⟨x / map.side, y / map.side, d⟩
    (map.glues.find? (·.1 == s) ).map (·.2)
  teleport x y d := 
    if let some ⟨i, j, dir⟩ := findGlue x y d then
      let q := invert <| leave (x % map.side) (y % map.side) d
      let (dx, dy) := enter q dir
      (dir.back, i * map.side + dx, j * map.side + dy)
    else
      panic! s!"can't find glue for {x} {y} {d}"
structure Step where
  map: Map
  dir: Dir
  x: Nat 
  y: Nat

def start: Step := {map , dir := R, x := 0, y := (map.elements[0]!.indexOf? '.').elim 0 (· + 0) }

def stepTrace: Step -> Step
| {map, dir, x, y} =>  
  let char := match dir with 
  | D => 'V'
  | R => '>'
  | L => '<'
  | U => '^'
  let map := {map with trace := map.trace.modify x (·.set! y char)}
  let (dir, x, y) := map.step x y dir
  {map, dir, x, y}
  

def walkBunch (c: Nat) (t: Turn) (s: Step): Id Step := do
  let mut s := {s with dir := s.dir.turn t}
  for _ in [0:c] do
    s := stepTrace s
  return s


def walk( xs: List (Nat × Turn)): Step := 
  xs.foldl (fun pos (c, t) => walkBunch c t pos) map.start

def make (ls: List String) (side: Nat) (glues: Array Glue): Map := 
  let elements := (ls.map (·.toList.toArray)).toArray
  let n := elements.foldl (max · ·.size) 0
  let m := elements.size
  let elements := elements.map (·.autoGrow n ' ')
  {elements, n, m, side, glues}

def strings := map.trace.map (String.mk <| ·.toList)
end Map

def parseCommande: Parse (List (Nat × Turn)) :=  do
  let init <- Parse.nat
  let ls <- parseOne.rep
  let tts := (init, Straight) :: ls
  return tts
where
  parseOne := do
  let turn <- Parse.choose [("L", Linksaf), ("R", Rechtsaf)]
  let cnt <- Parse.nat  
  return (cnt, turn)

def parseGlues: Parse (Array Glue) := do
  let glues <- glue.repSep! ", "
  let glues := glues.toArray
  let glues' := glues.map (fun (l, r) => (r, l))
  return glues ++ glues'
where
  side: Parse Side := open Parse in do
    let x <- nat
    ws
    let y <- nat
    ws
    let dir <- Dir.parse
    return {x, y, dir}
  glue := do
    let left <- side
    Parse.str " <-> "
    let right <- side
    return (left, right)

def main: IO Unit := do
  let lines <- readLines 22
  let map := lines.takeWhile (· != "")
  let tail := (lines.dropWhile (· != "")).drop 1 
  
  let coms <- parseCommande.runIO tail[0]!
  let side := tail[1]!.toNat!
  for l in tail.drop 2 do
    let glues <- parseGlues.runIO l
    let map := Map.make map side glues 
    let {map, dir, x, y} := map.walk coms
    IO.println (x, y, dir)
    map.strings.forM IO.println
    let code := (x + 1) * 1000 + (y + 1) * 4 + dir.code
    IO.println code

  