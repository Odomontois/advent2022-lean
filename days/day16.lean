import Advent
import Lean
import Std

open Lean (HashMap)

structure Pipe (α : Type) where
  name: α
  flow: Nat
  next: List α
  flowIdx: Nat := 0
deriving Inhabited, Lean.ToJson

def pipeName := Parse.seg (·.isUpper)

def parsePipe: Parse (Pipe String) := open Parse in do
  Parse.str "Valve "
  let name <- pipeName
  str " has flow rate="
  let flow <- nat
  str "; "
  str "tunnels lead to valves " ||| str "tunnel leads to valve "
  let next <- pipeName.repSep! ", "  
  return ⟨ name, flow, next, 0 ⟩

-- optimization to use indices instead of names
def reindexPipes [Hashable α] [BEq α] (pipes: Array (Pipe α)): Id (Array (Pipe Nat)) := do
  let mut names := HashMap.empty

  for (i, p) in pipes.toList.enum do
    names := names.insert p.name i
  
  pipes.map <| λ p => { p with 
    name := names[p.name].get!
    next := p.next.map (names[·].get!)
  }

abbrev Pipes := Array (Pipe Nat)

structure Position where
  opened: Nat := 0 -- bitArray
  cur: Nat := 0
  time: Nat := 30
deriving BEq, Hashable
namespace Position 
  variable (pos: Position)
  variable (pipes: Pipes)

  def curOpened? : Bool := pos.opened &&& (1 <<< pipes[pos.cur]!.flowIdx) != 0

  def openCur: Position := { pos with 
    time := pos.time - 1
    opened := pos.opened ||| (1 <<< pipes[pos.cur]!.flowIdx)
  }

  def goTo (i: Nat): Position :=  {
    pos with 
    time := pos.time - 1
    cur := i
  }
end Position


abbrev Cache.Value := Nat
abbrev Cache.Key := Position

def Cache := HashMap Cache.Key Cache.Value

def Cache.init: Cache := HashMap.empty

abbrev Search α := StateM Cache α

def maxFlow (pipes: Pipes) (pos: Position): Search Nat :=
  match decidable (0 < pos.time) with 
      | isFalse _ => pure 0
      | isTrue _ => do

    let c <- StateT.get

    if let some res := c.find? pos
    then return res

    let mut res := 0

    if pipes[pos.cur]!.flow > 0 && !pos.curOpened? pipes then 
      let curFlow := (pos.time - 1) * pipes[pos.cur]!.flow

      let next <- maxFlow pipes <| pos.openCur pipes
      res := next + curFlow

    for i in pipes[pos.cur]!.next do
      have: (pos.goTo i).time < pos.time := by 
        simp [Position.goTo] ; 
        apply @Nat.sub_lt_sub_left 0
        . assumption
        . apply Nat.zero_lt_of_ne_zero
          intro ; contradiction
      let step <- maxFlow pipes <| pos.goTo i 
      res := max res step

    res := res

    StateM.update (·.insert pos res)

    return res
termination_by maxFlow _ pos => pos.time


def runMaxFlow pipes time opened := 
  maxFlow pipes {time := time, opened := opened}

def runAllFlows (pipes: Pipes) (time: Nat) : Search (List Nat) := 
  let nzCount := 1 <<< (pipes.filter (·.flow > 0)).size
  let allBits := nzCount  - 1
  (List.range nzCount).mapM (λ allow => (runMaxFlow pipes time (allBits ^^^ allow)))


def sumFlow (results: List Nat) : Id (Nat × Nat × Nat) := do
  let mut best := 0
  let mut bestI := 0
  let mut bestJ := 0
  for (i, resMy) in results.enum do
    for (j, resElephant) in results.enum do
      let res := resMy + resElephant
      if i &&& j == 0 && best < res then 
        best := res
        bestI := i
        bestJ := j
  return (best, bestI, bestJ)

def main: IO Unit := do
  let lines <- readLines 16
  let ls <- lines.mapM parsePipe.runIO 
  let nzFlow := ls.filter (·.flow > 0) |> (·.enum) |> (·.map <| fun (i, p) => {p with flowIdx := i})
  let ls := nzFlow ++ (ls.filter (·.flow == 0))
  -- setting AA pipe first
  let pipes := reindexPipes <| ls.toArray.qsort (fun p _ => p.name == "AA")
  IO.println pipes.size
  pipes.forM IO.println  
  let (res, c) := runMaxFlow pipes 30 0 Cache.init
  IO.println res
  IO.println c.size
  let (allRes, _) := runAllFlows pipes 26 Cache.init
  IO.println allRes.length
  IO.println <| sumFlow allRes
