def hello := "world"

def main : IO Unit := do
  IO.println s!"Hellollolo"
  IO.println s!"Hello, {hello}!"