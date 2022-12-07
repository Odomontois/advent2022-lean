theorem bool_and_true (x y: Bool): ((x && y) = true) <-> (x = true) /\ (y = true) := by 
  cases x <;> cases y <;> simp