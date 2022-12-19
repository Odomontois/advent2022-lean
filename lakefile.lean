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

lean_exe day8 {root := `days.day8 }

lean_exe day9 {root := `days.day9 }

lean_exe day10 {root := `days.day10 }

lean_exe day11 { root := `days.day11 }

lean_exe day12 { root := `days.day12 }

lean_exe day13 { root := `days.day13 }

lean_exe day14 { root := `days.day14 }

lean_exe day15 { root := `days.day15 }

lean_exe day16 { root := `days.day16 }

lean_exe day17 { root := `days.day17 }

lean_exe day18 { root := `days.day18 }

lean_exe day19 { root := `days.day19 }