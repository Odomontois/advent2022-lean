def appendFin (x: α) (xs: List α) (i : Fin (xs.length)): Fin ((x :: xs).length) :=
  ⟨ Nat.succ i.val, Nat.succ_le_succ i.isLt ⟩

def shuffleIndex {n: Nat}(i : Fin (n + 2)): Fin (n + 2)  :=
match i.val with
  | 0 => ⟨1, Nat.succ_le_succ (Nat.zero_lt_succ _) ⟩
  | 1 => ⟨0, Nat.zero_lt_succ _⟩
  | _ + 2 => i

theorem shuffleCancelable {n: Nat} {i : Fin (n + 2)}: shuffleIndex (shuffleIndex i) = i := by
  cases i with | mk v lt => 
  cases v with
  | zero => simp [shuffleIndex] 
  | succ v1 => cases v1 <;> simp [shuffleIndex]

theorem shuffledGet {x y : α} {xs : List α} (i : Fin (xs.length + 2)): (x :: y :: xs).get i = (y :: x :: xs).get (shuffleIndex i) := by
  cases i with 
    | mk v _ => 
      cases v with 
      | zero => simp [List.get]
      | succ v1 => cases v1 <;> simp [List.get]