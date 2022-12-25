import Lake
open Lake DSL

package advent {
  isLeanOnly := true
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

-- @[default_target]
lean_exe fpbench {root := `playground.fpbench }

--@[default_target]
lean_exe day1{ root := `days.day1 }

--@[default_target]
lean_exe day2{ root := `days.day2 }

--@[default_target]
lean_exe day3{ root := `days.day3 }

--@[default_target]
lean_exe day4{ root := `days.day4 }

--@[default_target]
lean_exe day5{ root := `days.day5 }

--@[default_target]
lean_exe day6{ root := `days.day6 }

--@[default_target]
lean_exe day7 {root := `days.day7 }

--@[default_target]
lean_exe day8 {root := `days.day8 }

--@[default_target]
lean_exe day9 {root := `days.day9 }

--@[default_target]
lean_exe day10 {root := `days.day10 }

--@[default_target]
lean_exe day11 { root := `days.day11 }

--@[default_target]
lean_exe day12 { root := `days.day12 }

--@[default_target]
lean_exe day13 { root := `days.day13 }

--@[default_target]
lean_exe day14 { root := `days.day14 }

--@[default_target]
lean_exe day15 { root := `days.day15 }

--@[default_target]
lean_exe day16 { root := `days.day16 }

--@[default_target]
lean_exe day17 { root := `days.day17 }

--@[default_target]
lean_exe day18 { root := `days.day18 }

--@[default_target]
lean_exe day19 { root := `days.day19 }

--@[default_target]
lean_exe day20 { root := `days.day20 }

--@[default_target]
lean_exe day21 { root := `days.day21 }

--@[default_target]
lean_exe day22 { root := `days.day22 }

lean_exe day23 { root := `days.day23 }

lean_exe day24 { root := `days.day24 }

lean_exe day25 { root := `days.day25 }