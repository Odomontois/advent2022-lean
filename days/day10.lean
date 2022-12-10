import Advent

def parse (cmd: String): List (Option Int) :=
  match cmd.splitOn with 
  | ["addx", s] => [none, s.toInt?]
  | _ => [none]

def handle (cmd: Option Int): StateM Int Int :=  fun x => (x, x + cmd.getD 0)

def main : IO Unit := do
  let inps <- readLines 10
  let cmds := inps.bind parse
  let cycles := [20, 60, 100, 140, 180, 220]
  let (res, _) := cmds.mapM handle 1
  let ress := cycles.map (fun i => res[i - 1]! * Int.ofNat i)
  IO.println ress
  IO.println ress.sum
  let pos := res.enum.map (fun (i, x) => if (x - i.mod 40).abs <? 2 then '#' else '.')
  IO.println res
  let posLines := pos.group 40 |> List.map String.mk 
  posLines.forM IO.println

