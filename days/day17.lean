import Advent
import Std

open Lean (HashSet)

def Figure := List (Nat × Nat) deriving Inhabited, Lean.ToJson
namespace Figure
variable (fig: Figure)
variable (tower: Array (Array Bool))



end Figure

inductive Command where | L |R deriving Inhabited, Lean.ToJson

def Command.fromChar: Char -> Option Command
| '<' => L
| '>' => R
| _ => none

def makePiece (ls: List String): Figure := 
  ls.reverse.enum.bind <| fun (i, s) => 
    s.toList.enum.filterMap <| fun (j, c) => 
      if c = '#' then (i, j + 2) else none

def pieces := makePiece <$> [[
    "####"
  ],[
    ".#.",
    "###.",
    ".#."
  ],[
    "..#",
    "..#",
    "###"
  ],[
    "#",
    "#",
    "#",
    "#"
  ],[
    "##",
    "##"
]]

structure Cycling (α : Type) where
  elems : Array α
  cur : Nat
deriving Lean.ToJson, Inhabited

namespace Cycling
  variable (cyc: Cycling α)
  
  def next [Inhabited α]: (α × Cycling α) := (cyc.elems[cyc.cur]!, {cyc with cur := (cyc.cur + 1) % cyc.elems.size})

  def ofList (ls: List α): Cycling α := {elems := ls.toArray, cur := 0 }

end Cycling

structure Falling where
  commands: Cycling Command
  figures: Cycling Figure
  figure: Figure
  tower : Array (Array Bool) := Array.empty
  count : Nat := 0
deriving Lean.ToJson, Inhabited

namespace Falling     
variable (f: Falling)

def go? (g: Nat -> Nat -> (Nat × Nat)): Option Falling := 
  if f.figure.all (λ (x, y) => 
      let (x', y') := g (x + 1) (y + 1)
      x' > 0 && y' > 0 && y' <= 7 && 
      (x' > f.tower.size || !f.tower[x' - 1]![y' - 1]!))
    then some <| {f with figure := f.figure.map (λ (x, y) => g x y) }
    else none

def goSide? (g: Nat -> Nat): Falling := (f.go? (λ x y => (x, g y))).getD f

def goLeft := f.goSide? (· - 1)
def goRight := f.goSide? (· + 1)
def goDown? : Option Falling :=  f.go? (λ x y => (x - 1, y))

def pullNext: Falling := 
  let (fig, figures) := f.figures.next
  let l := f.tower.size + 3
  let fig := fig.map <| fun (x, y) => (x + l, y)
  {f with figure := fig, figures := figures}

def ofCommands (comms: List Command) (p : !comms.isEmpty) : Falling :=
  { commands := Cycling.ofList comms  
    figure   := Inhabited.default
    figures  := Cycling.ofList pieces
    : Falling
  }.pullNext

def append := 
  let fig := f.figure
  let mx := (fig.map (·.fst)).maximum?.get!
  let tower := f.tower.append <| Array.mkArray (mx + 1 - f.tower.size) <| Array.mkArray 7 false
  let tower := fig.foldl (fun t (x, y) => t.modify x (·.set! y true)) tower
  {f with tower := tower, count := f.count + 1}.pullNext

def height := f.tower.size

def tryStep: (Bool × Falling) := 
  let (com, commands) := f.commands.next

  let f := {f with commands := commands}

  let f := match com with 
  | Command.L => f.goLeft
  | Command.R => f.goRight

  if let some f := f.goDown? then (false, f) else (true, f.append)

def smallStep: Falling := f.tryStep.snd

partial def step (f: Falling): Falling := 
    let (ap, f) := f.tryStep
    if ap then f
    else step f

def printOut : IO Unit := do
  f.append.tower.reverse.forM 
    (IO.println <| String.mk <| ·.toList.map (if · then '#' else '.'))

def wait (f: Falling): Nat -> Falling
  | 0 => f
  | c + 1 => wait f.step c

partial def bigWait (f: Falling): Falling := 
  go HashSet.empty f
where
  go (h: HashSet (Nat × Nat)) (f: Falling)  := 
    let q := (f.figures.cur, f.commands.cur)
    if h.contains q then f 
    else go (h.insert q) f.step


end Falling

partial def loop (x: α) (f: α -> α) (action: α -> IO Unit): IO Unit := do
  let i <- IO.getStdin
  action x
  _ <- i.read 1  
  loop (f x) f action

def iters (count: Nat) (x: α) (f: α -> α): List α := 
  match count with
  | 0 => []
  | c + 1 => x :: iters c (f x) f

def main : IO Unit := do
  let input <- readInput 17
  let input := (input.toList.mapM Command.fromChar).get!
  let falling <- match input with 
    | x :: xs => 
      pure <| Falling.ofCommands (x :: xs) <| by simp [List.isEmpty]
    | [] => throw <| IO.userError "empty input"
  
  IO.println falling.figure
  -- loop falling (·.step) (·.printOut )
  let f := falling.wait 2022
  IO.println f.tower.size
  IO.println f.count
  -- let fs := iters 6 falling (·.bigWait)

  -- let dx := fs.tail.zipWith (·.count - ·.count)  fs
  -- let dy := fs.tail.zipWith (·.tower.size - ·.tower.size)  fs
  
  -- IO.println dx
  -- IO.println dy

  let need := 1000000000000

  let (f1, f2) := match iters 3 falling (·.bigWait) with
    | [_, x1, x2] => (x1, x2)
    | _ => panic! "!!!"

  let need' := need - f1.count
  let loopSize := f2.count - f1.count
  let loops := need' / loopSize
  let finalize := need' % loopSize
  let f3 := f1.wait finalize
  let height := (f2.height - f1.height) * loops + f3.height
  IO.println height

