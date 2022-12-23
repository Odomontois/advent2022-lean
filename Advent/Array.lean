import Lean
import Std
import Lean.Elab.Command

structure FinRange (n: Nat)

abbrev Matrix α := Array (Array α)

namespace Array

theorem modify_stable_size(arr: Array α) (f: α -> α) (n: Nat): arr.size = (arr.modify n f).size := by
  simp [modify, modifyM, dite]
  generalize Nat.decLt n (size arr) = q
  cases q <;> simp [Id.run] 

theorem zipWith_eq_size {n: Nat} {arr: Array α} {arr' : Array β} (f: α -> β -> γ) 
  (p: arr.size = n) (p': arr'.size = n)
  : (arr.zipWith arr' f).size = n := by 
    simp [zipWith,  size]
    unfold zipWithAux
    match n with 
    | 0 => 
      rw [<- p]
      simp [List.length]
      rw [p] 
    | n + 1 => 
      admit

def uniques [Ord α] [Inhabited α] [BEq α] (arr: Array α) : Id (Array α) := do
  if arr.isEmpty then return arr
  let arr := arr.qsort (compare · · == Ordering.lt)
  let mut res := #[arr[0]!]
  for i in [1:arr.size] do
    if arr[i]! != arr[i - 1]! then
      res := res.push arr[i]!
  return res

open Lean (HashMap)

def groupBy [Hashable β] [BEq β] (f: α -> β) (arr: Array α): Id (HashMap β (List α)) := do
  let mut res := HashMap.empty
  for a in arr do
    let g := f a
    res := res.insert g <| 
      if let some lst := res.find? g
      then a :: lst
      else [a]

  return res

def autoGrow (p: Array α) (n: Nat) (elem: α): Array α :=
  if p.size < n then p.append (Array.mkArray (n - p.size) elem) else p

def zipWithGrow (xs: Array α) (ys: Array β) (f: α -> β -> γ) (x: α) (y: β): Array γ :=
  let xs := xs.autoGrow ys.size x
  let ys := ys.autoGrow xs.size y
  xs.zipWith ys f

-- TODO proof of indexing
def transpose [Inhabited α] (arr: Array (Array α)): Array (Array α) := 
  let m := arr.size
  let n := arr.foldl (min · ·.size) (arr[0]?.elim 0 (·.size))
  let res := Array.mkArray n <| Array.mkArray m default
  (fill res).2
where 
  fill: StateM _ _ := fun res => do
    let res <- res.mapIdxM <| fun i row =>
        row.mapIdxM <| fun j _ => arr[j]![i]!
    ((), res)

end Array