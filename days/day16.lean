import Advent

structure Pipe where
  name: String
  flow: Nat
  next: List String
deriving Inhabited, Lean.ToJson

def pipeName := Parse.seg (·.isUpper)

def parsePipe: Parse Pipe := open Parse in do
  Parse.str "Valve "
  let name <- pipeName
  str " has flow rate="
  let flow <- nat
  str "; "
  str "tunnels lead to valves " ||| str "tunnel leads to valve "
  let next <- pipeName.repSep! ", "  
  return ⟨ name, flow, next ⟩

def main: IO Unit := do
  let lines <- readLines 16
  lines.map (parsePipe.runE) |> (·.forM IO.println)
