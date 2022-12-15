def readInput (i: Int) : IO String := do
  let full <- IO.getEnv "full"
  let add <- IO.getEnv "add"
  let dir := if full == some "true" 
    then "full-input"
    else "test-input"
  let suffix := if let some s := add 
    then "-" ++ s
    else ""
  let path := s!"./{dir}/day{i}{suffix}.txt"
  IO.FS.readFile path

def br: String := "\n"

def readLines (i: Int) : IO (List String) := do
  (readInput i).map (·.splitOn br)

def readBlockLines (i: Int): IO (List String) := (readInput i).map (·.splitOn (br ++ br))

def readBlocks (i: Int) : IO (List (List String)) := (readBlockLines i).map (·.map (·.splitOn br))

