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
  opened: Nat := 0-- bitArray
  cur: Nat := 0
  time: Nat := 30
deriving BEq, Hashable, Lean.ToJson

namespace Position 
  variable (pos: Position)

  def curOpened?: Bool := pos.opened &&& (1 <<< pos.cur) != 0

  def openCur : Position := { pos with 
    time := pos.time - 1
    opened := pos.opened ||| (1 <<< pos.cur)
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

namespace Cache
  variable (cache: Cache)

  def init: Cache := HashMap.empty
end Cache

abbrev Search α := StateM Cache α

def decidable (P: Prop) [inst: Decidable P]: Decidable P := inst

def maxFlow (pipes: Pipes)  (flow: Nat) (pos: Position): Search Nat :=
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

    for i in pipes[pos.cur]!.next do
      let step <- maxFlow pipes flow <| pos.goTo i 
      res := max res step

    res := res + flow

    StateM.update (·.insert pos res)

    return res
termination_by maxFlow _ pos => pos.time

def runMaxFlow (pipes: Pipes)  := 
  maxFlow pipes 0 {} Cache.init 

def main: IO Unit := do
  let lines <- readLines 16
  let ls <- lines.mapM parsePipe.runIO 
  let nzFlow := ls.filter (·.flow > 0) |> (·.enum) |> (·.map <| fun (i, p) => {p with flowIdx := i})
  let ls := nzFlow ++ (ls.filter (·.flow == 0))
  -- setting AA pipe first
  let pipes := reindexPipes <| ls.toArray.qsort (fun p _ => p.name == "AA")
  IO.println pipes.size
  pipes.forM IO.println  
  let (res, c) := runMaxFlow pipes
  IO.println res
  IO.println c.size