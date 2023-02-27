import Lean
import Std
import Mathlib.Tactic.LeftRight

theorem problem_3 : ((p ∨ q) ∧ (p → r) ∧ (q → s)) → (r ∨ s) := by
  intro ⟨pq, f, g⟩
  cases pq 
  . left
    apply f 
    assumption
  . right
    apply g
    assumption
    

