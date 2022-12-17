import Advent
import Lean
import Std

open Lean (HashMap)

structure Pipe (α : Type) where
  name: α
  flow: Nat
  next: List (Nat × α)
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
  return ⟨ name, flow, next.map ((0, ·)), 0 ⟩

-- optimization to use indices instead of names
def reindexPipes [Hashable α] [BEq α] (pipes: Array (Pipe α)): Id (Array (Pipe Nat)) := do
  let mut names := HashMap.empty

  for (i, p) in pipes.toList.enum do
    names := names.insert p.name i
  
  pipes.map <| λ p => { p with 
    name := names[p.name].get!
    next := p.next.map (λ (s, n) => (s, names[n].get!))
  }

abbrev Pipes := Array (Pipe Nat)

structure Position where
  opened: Nat := 0-- bitArray
  cur: Nat := 0
  elephant: Nat := 0
  time: Nat := 30
deriving BEq, Hashable, Lean.ToJson

namespace Position 
  variable (pos: Position)
  variable (pipes: Pipes)

  def curOpened? : Bool := pos.opened &&& (1 <<< pipes[pos.cur]!.flowIdx) != 0

  def elephantOpened?: Bool := pos.opened &&& ( 1 <<< pos.elephant) != 0

  def openCurElephant : Position := { pos with 
    opened := pos.opened ||| (1 <<< pos.elephant)
  }

  def openCur: Position := { pos with 
    time := pos.time - 1
    opened := pos.opened ||| (1 <<< pipes[pos.cur]!.flowIdx)
  }

  def goToElephant (s: Nat) (i: Nat): Position :=  { pos with 
      elephant := i 
      time := pos.time - s
    }

  def goTo (s: Nat) (i: Nat): Position :=  {
    pos with 
    time := pos.time - (s + 1)
    cur := i
  }

  theorem twiceLess {qt : pos.time > 0} (s : Nat) :  2 * (pos.time - (s + 1)) + 1 < 2 * pos.time := by
    generalize p: pos.time = x at qt
    cases x <;> simp 
    . contradiction
    . case succ x => 
        rw [Nat.mul_sub_left_distrib]
        simp [HMul.hMul, Mul.mul, Nat.mul]
        apply Nat.lt_of_succ_le
        apply Nat.add_le_add_right _ 2
        apply @Nat.sub_le_sub_left 0
        apply Nat.zero_le
         
end Position


abbrev Cache.Value := Nat
abbrev Cache.Key := Position

def Cache := HashMap Cache.Key Cache.Value

namespace Cache
  variable (cache: Cache)

  def init: Cache := HashMap.empty
end Cache

abbrev Search α := StateM Cache α

def decidable (P: Prop) [inst: Decidable P]: Decidable P := inst

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

    for (s, i) in pipes[pos.cur]!.next do
      have: (pos.goTo s i).time < pos.time := by 
        simp [Position.goTo] ; 
        apply @Nat.sub_lt_sub_left 0
        . assumption
        . apply Nat.zero_lt_of_ne_zero
          intro ; contradiction
      let step <- maxFlow pipes <| pos.goTo s i 
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
  let (allRes, c) := runAllFlows pipes 26 Cache.init
  -- allRes.enum.forM IO.println
  IO.println allRes.length
  IO.println <| sumFlow allRes
  IO.println c.size