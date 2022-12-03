def readInput (i: Int) : IO String := do
  let full <- IO.getEnv "full"
  let dir := if full == some "true" 
    then "full-input"
    else "test-input"
  let path := s!"./{dir}/day{i}.txt"
  IO.FS.readFile path


def readLines (i: Int) : IO (List String) := do
  let input <- readInput i
  return (String.splitOn input "\n")
