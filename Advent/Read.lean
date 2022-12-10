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


def readLines (i: Int) : IO (List String) := do
  let input <- readInput i
  return (String.splitOn input "\n")
