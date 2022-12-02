def readInput (i: Int) : IO String := do
  let full <- IO.getEnv "full"
  let dir := if full == some "true" 
    then "full-input"
    else "test-input"
  let path := s!"./{dir}/day{i}.txt"
  IO.FS.readFile path