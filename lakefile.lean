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

lean_exe day1{ root := `days.day1 }

lean_exe day2{ root := `days.day2 }