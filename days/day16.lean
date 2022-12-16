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

  def curOpened?: Bool := pos.opened &&& (1 <<< pos.cur) != 0

  def elephantOpened?: Bool := pos.opened &&& ( 1 <<< pos.elephant) != 0

  def openCurElephant : Position := { pos with 
    opened := pos.opened ||| (1 <<< pos.elephant)
  }

  def openCur : Position := { pos with 
    time := pos.time - 1
    opened := pos.opened ||| (1 <<< pos.cur)
  }

  def goToElephant (i: Nat): Position :=  { pos with  elephant := i }

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

def maxFlow (pipes: Pipes) (flow: Nat) (pos: Position): Search Nat :=
  match decidable (0 < pos.time) with 
      | isFalse _ => pure 0
      | isTrue _ => do

    let c <- StateT.get

    if let some res := c.find? pos
    then return res

    let mut res := 0

    if !pos.curOpened? && pipes[pos.cur]!.flow > 0 then 
      let curFlow := pipes[pos.cur]!.flow
      res <- maxFlow pipes (flow + curFlow) pos.openCur

    for (s, i) in pipes[pos.cur]!.next do
      have: (pos.goTo s i).time < pos.time := by 
        simp [Position.goTo] ; 
        apply @Nat.sub_lt_sub_left 0
        . assumption
        . apply Nat.zero_lt_of_ne_zero
          intro ; contradiction
      let step <- maxFlow pipes flow <| pos.goTo s i 
      res := max res step

    res := res + flow

    StateM.update (·.insert pos res)

    return res
termination_by maxFlow _ _ pos => pos.time

mutual 
def maxFlowElephant (pipes: Pipes)  (flow: Nat) (pos: Position): Search Nat :=
  match decidable (0 < pos.time) with 
      | isFalse _ => pure 0
      | isTrue q => do

    let c <- StateT.get

    if let some res := c.find? pos
    then return res

    let mut res := 0

    if !pos.elephantOpened? && pipes[pos.elephant]!.flow > 0 then 
      let curFlow := pipes[pos.elephant]!.flow
      have : 2 * pos.openCurElephant.time < 2 * pos.time + 1 := by
        simp [Position.openCurElephant] 

      res <- maxFlowYou pipes (flow + curFlow) pos.openCurElephant  q

    for (s, i) in pipes[pos.elephant]!.next do
      have : 2 * (pos.goToElephant i).time < 2 * pos.time + 1 := by 
        simp [Position.goToElephant]
      let step <- maxFlowYou pipes flow (pos.goToElephant i) q
      res := max res step

    res := res + flow

    StateM.update (·.insert pos res)

    return res

def maxFlowYou (pipes: Pipes) (flow: Nat) (pos: Position) (qt : pos.time > 0): Search Nat := do
    let mut res := 0

    if !pos.curOpened? && pipes[pos.cur]!.flow > 0 then 
      let curFlow := pipes[pos.cur]!.flow
      have: 2 * pos.openCur.time + 1 < 2 * pos.time := by 
        simp [Position.openCur] ; apply Position.twiceLess ; assumption

      res <- maxFlowElephant pipes (flow + curFlow) pos.openCur

    for (s, i) in pipes[pos.cur]!.next do
      have: 2 * (pos.goTo s i).time + 1 < 2 * pos.time := by 
        simp [Position.goTo]; apply Position.twiceLess; assumption
      let step <- maxFlowElephant pipes flow <| pos.goTo s i 
      res := max res step

    return res
end
termination_by 
  maxFlowYou _  _ pos _ => 2 * pos.time
  maxFlowElephant pos => 2 * pos.time + 1


def runMaxFlow pipes time  := 
  maxFlow pipes 0 {time := time} Cache.init 

def runMaxFlowElephant pipes time  := 
  maxFlowElephant pipes 0 {time := time} Cache.init 

def main: IO Unit := do
  let lines <- readLines 16
  let ls <- lines.mapM parsePipe.runIO 
  let nzFlow := ls.filter (·.flow > 0) |> (·.enum) |> (·.map <| fun (i, p) => {p with flowIdx := i})
  let ls := nzFlow ++ (ls.filter (·.flow == 0))
  -- setting AA pipe first
  let pipes := reindexPipes <| ls.toArray.qsort (fun p _ => p.name == "AA")
  IO.println pipes.size
  pipes.forM IO.println  
  let (res, c) := runMaxFlow pipes 30
  IO.println res
  IO.println c.size

  let (res, c) := runMaxFlowElephant pipes 26
  IO.println res
  IO.println c.size