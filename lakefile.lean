import Lake
open Lake DSL

package advent {
  -- add package configuration options here
}

lean_lib Advent {
  -- add library configuration options here
}

@[default_target]
lean_exe advent {
  root := `Main
}
