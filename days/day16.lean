import Advent
-- import Lean

structure Pipe where
  name: String
  flow: Nat
  next: List String
  idx: Nat
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
  return ⟨ name, flow, next, 0 ⟩

def main: IO Unit := do
  let lines <- readLines 16
  let ls <- lines.mapM parsePipe.runIO 
  let nzFlow := ls.filter (·.flow > 0) |> (·.enum) |> (·.map <| fun (i, p) => {p with idx := i})
  let ls := nzFlow ++ (ls.filter (·.flow == 0))
  ls.forM IO.println  