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

theorem DifListTail [BEq α] {x: α} {xs: List α}: DifferentList (x :: xs) -> DifferentList xs := by
  intros xxs
  unfold DifferentList
  generalize xs.length = ul

theorem nilDifferent [BEq α] : DifferentList ([] : List α) := by
  unfold DifferentList
  intro i
  intros
  simp [List.length] at i
  cases i.isLt  


theorem correctLeft[DecidableEq α] (xs: List α) (p: differs xs = true): DifferentList xs := by 
  cases xs
  apply nilDifferent
  sorry

theorem correctRight [DecidableEq α] (xs: List α) (dl: DifferentList xs): differs xs = true := by
  cases xs with
  | nil => simp [differs]
  | cons h t =>
    unfold differs 
    apply (bool_and_true _ _).mpr
    constructor
    sorry
    apply correctRight
    apply DifListTail dl

theorem differsIsCorect [DecidableEq α] (xs: List α): (differs xs = true) <-> DifferentList xs := by
  apply Iff.intro
  apply correctLeft
  apply correctRight
end differs
  