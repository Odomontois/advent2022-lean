import Advent.List

import Advent.List.Shuffles

def DifferentList [BEq α] (xs: List α): Prop := ∀ i j : Fin (xs.length), (xs.get i = xs.get j) -> i = j

theorem DifListTail [BEq α] {xs: List α} (x: α): DifferentList (x :: xs) -> DifferentList xs := by
  intros xxs
  unfold DifferentList
  intros i j iej
  apply Fin.eq_of_val_eq
  let i1 := appendFin x xs i
  let j1 := appendFin x xs j
  let h1 := xxs i1 j1
  simp [List.get] at h1
  let i1ej1 := h1 iej
  simp [appendFin] at i1ej1
  exact i1ej1

theorem DifListShuffle [BEq α] {x y : α} {xs: List α}: 
  DifferentList (x :: y :: xs) -> DifferentList (y :: x :: xs) := by
  intros dl i j iej
  rw [shuffledGet i, shuffledGet j] at iej
  let siej := dl _ _ iej
  let ssiej := congrArg shuffleIndex siej
  rw [shuffleCancelable, shuffleCancelable] at ssiej
  assumption  
  
theorem DifListHead [da: DecidableEq α] {x: α} {xs: List α}: 
  DifferentList (x::xs) -> xs.all (· != x) = true := by
  intros h
  cases xs 
  . simp [List.all, List.foldr]
  . case cons y ys => 
    simp [List.all, List.foldr]
    constructor
    . simp [bne, BEq.beq, decide]
      apply decide_eq_false
      intro yex
      let i: Fin (x :: y :: ys).length := ⟨ 0, Nat.zero_lt_succ _ ⟩
      let j: Fin (x :: y :: ys).length := ⟨ 1, Nat.succ_le_succ (Nat.zero_lt_succ _) ⟩
      let h2 := h i j
      simp [List.get] at h2
      apply h2
      rw [yex]
    . apply DifListHead
      apply DifListTail y
      apply DifListShuffle
      exact h



theorem nilDifferent [BEq α] : DifferentList ([] : List α) := by
  unfold DifferentList
  intro i
  intros
  simp [List.length] at i
  cases i.isLt  

theorem listAllCorrect {xs : List α} {p : α -> Bool} (i: Fin (xs.length)) :
  xs.all p = true -> p (xs.get i) = true := by 
  intro all
  cases i 
  case mk iv ilt => 
  cases xs
  . contradiction
  . case cons h t =>
    simp [List.all, List.foldr] at all 
    cases all with | intro first rest =>
    cases iv <;> simp [List.get]
    assumption
    case succ iv =>
    apply listAllCorrect
    assumption    
  

theorem differsHead [de: DecidableEq α] {x : α} {xs : List α} {i: Fin (xs.length)}
  (d: differs (x :: xs) = true) : 
  ¬ (x = xs.get i) := by
  intro p
  unfold differs at d
  simp at d
  cases d with | intro all _ =>
  let une := listAllCorrect i all
  simp [bne, BEq.beq] at une
  generalize List.get xs i = li at *
  let dd := (decide_eq_true (p.symm)).symm
  let uu := dd.trans une
  contradiction


theorem correctLeft[DecidableEq α] (xs: List α) (p: differs xs = true): DifferentList xs := by 
  cases xs
  . apply nilDifferent
  . case cons h t => 
    unfold DifferentList
    intros i j iej
    cases i with | mk iv ilt =>
    cases j with | mk jv jlt => 
    apply Fin.eq_of_val_eq
    simp
    cases iv 
    . cases jv
      simp
      case succ j => 
        simp [List.get] at iej
        let xs := differsHead p iej
        contradiction                
    . case succ i => 
      cases jv
      . simp [List.get] at iej
        let xs := differsHead p iej.symm
        contradiction
      . case succ j => 
        simp [List.get] at iej
        simp
        simp [differs] at p
        cases p with | intro _ tdiff =>
        let td := correctLeft t tdiff        
        let u := td _ _ iej
        simp at u
        assumption
  

theorem correctRight [DecidableEq α] (xs: List α) (dl: DifferentList xs): differs xs = true := by
  cases xs
  . simp [differs]
  . case cons h t =>
    unfold differs 
    apply (bool_and_true _ _).mpr
    constructor
    apply DifListHead dl
    apply correctRight
    apply DifListTail _ dl

theorem differsIsCorect [DecidableEq α] (xs: List α): (differs xs = true) <-> DifferentList xs := by
  apply Iff.intro
  apply correctLeft
  apply correctRight
