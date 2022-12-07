import Advent.Bool

def group (l: List α) (n: Nat): List (List α) := 
  loop l n [] []
where
  loop : List α -> Nat ->  List α -> List (List α)  -> List (List α)
  | [], _, gacc, acc=> (gacc.reverse :: acc).reverse
  | x :: xs, 0, gacc, acc => loop xs (n - 1)  [x] (gacc.reverse :: acc) 
  | x :: xs, rem + 1, gacc, acc => loop xs rem (x :: gacc) acc  

def transpose : List (List α) -> List (List α)  
| [] => []
| [lst] => lst.map ([·])
| head :: rest => head.zipWith (· :: ·) (transpose rest)

def transposeRev : List (List α) -> List (List α)
  | fst :: rest => loop (fst.map ([·])) rest
  | [] => []
where 
loop (acc: List (List α)): (List (List α)) -> List (List α)
  | [] => acc
  | head :: rest => loop (head.zipWith (· :: ·) acc) rest

def tails: List α -> List (List α)
| x :: xs => (x :: xs) :: tails xs
| [] => []

def differs [BEq α]: List α -> Bool
| [] => true
| x :: xs => xs.all (· != x) && differs xs

namespace differs


def DifferentList [BEq α] (xs: List α): Prop := ∀ i j : Fin (xs.length), (xs.get i = xs.get j) -> i = j

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

theorem DifListTail [BEq α] {x: α} {xs: List α}: DifferentList (x :: xs) -> DifferentList xs := by
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

theorem DifListShuffle [BEq α] {x y : α} {xs: List α}: DifferentList (x :: y :: xs) -> DifferentList (y :: x :: xs) := by
  intros dl i j iej
  rw [shuffledGet i, shuffledGet j] at iej
  let siej := dl _ _ iej
  let ssiej := congrArg shuffleIndex siej
  rw [shuffleCancelable, shuffleCancelable] at ssiej
  assumption  
  
theorem DifListHead [da: DecidableEq α] {x: α} {xs: List α}: 
  DifferentList (x::xs) -> xs.all (· != x) = true := by
  intros h
  cases xs with 
  | nil => 
    simp [List.all, List.foldr]
  | cons y ys => 
    simp [List.all, List.foldr]
    constructor
    simp [bne, BEq.beq, decide]
    apply decide_eq_false
    intro yex
    let i: Fin (x :: y :: ys).length := Fin.mk 0 (Nat.zero_lt_succ _)
    let j: Fin (x :: y :: ys).length := Fin.mk 1 (Nat.succ_le_succ (Nat.zero_lt_succ _))
    let h2 := h i j
    simp [List.get] at h2
    apply h2
    rw [yex]
    apply DifListHead
    apply @DifListTail _ _ y _
    apply DifListShuffle
    exact h



theorem nilDifferent [BEq α] : DifferentList ([] : List α) := by
  unfold DifferentList
  intro i
  intros
  simp [List.length] at i
  cases i.isLt  


theorem differsHead [DecidableEq α] {x : α} {xs : List α} {i: Fin (xs.length)}
  (d: differs (x :: xt) = true) : 
  Not (x = xs.get i) := by admit


theorem correctLeft[DecidableEq α] (xs: List α) (p: differs xs = true): DifferentList xs := by 
  cases xs with
  | nil => apply nilDifferent
  | cons h t => 
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
    case succ i => 
      cases jv
      case zero => 
        simp [List.get] at iej
        let xs := differsHead p iej.symm
        contradiction
      case succ j => 
        simp [List.get] at iej
        simp
        simp [differs] at p
        cases p 
        case intro _ tdiff =>
        let td := correctLeft t tdiff        
        let u := td _ _ iej
        simp at u
        assumption





  

theorem correctRight [DecidableEq α] (xs: List α) (dl: DifferentList xs): differs xs = true := by
  cases xs with
  | nil => simp [differs]
  | cons h t =>
    unfold differs 
    apply (bool_and_true _ _).mpr
    constructor
    apply DifListHead dl
    apply correctRight
    apply DifListTail dl

theorem differsIsCorect [DecidableEq α] (xs: List α): (differs xs = true) <-> DifferentList xs := by
  apply Iff.intro
  apply correctLeft
  apply correctRight
end differs
  