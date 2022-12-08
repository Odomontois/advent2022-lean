import Lake
open Lake DSL

package advent {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Advent {
  -- add library configuration options here
}

@[default_target]
lean_exe advent {
  root := `Main
}

lean_exe day1{ root := `days.day1 }

lean_exe day2{ root := `days.day2 }

lean_exe day3{ root := `days.day3 }

lean_exe day4{ root := `days.day4 }

lean_exe day5{ root := `days.day5 }

lean_exe day6{ root := `days.day6 }

lean_exe day7 {root := `days.day7 }