import Lean
import Std
import Lean.Elab.Command

-- set_option max_re
abbrev Matrix α := Array (Array α)


structure FinRange (n: Nat) 

def finRange (n: Nat): FinRange n := {}

def FinRange.forIn [Monad m] (rng: FinRange n) (b: β) (f: Fin n -> β -> m (ForInStep β)) (i: Nat): m β :=
  if p: i < n then do 
      match (<- f ⟨i, p⟩ b) with
      | .done b' => pure b'
      | .yield b'=> forIn rng b' f (i + 1) 
  else pure b
termination_by forIn _ _ _ i => n - i

instance {n: Nat}: ForIn m (FinRange n) (Fin n) where
  forIn rng b f := FinRange.forIn rng b f 0

namespace Array

theorem modify_stable_size(arr: Array α) (f: α -> α) (n: Nat): arr.size = (arr.modify n f).size := by
  simp [modify, modifyM, dite]
  generalize Nat.decLt n (size arr) = q
  cases q <;> simp [Id.run] 


namespace ZipWithN
variable (as: Array α) (bs: Array β) (f: α -> β -> γ) (p: as.size = bs.size)

def go (arr: Array γ) (i: Nat): Array γ   := 
  if q : i < as.size then
    let a := as[i]'q
    let b := bs[i]'(by rw [<-p]; exact q)
    go (arr.push <| f a b) (i + 1)
  else arr
  termination_by go _ i => as.size - i

def zipWithN: Array γ := go as bs f p Array.empty 0

theorem zipWithNSizeGo (ip: i <= as.size) (ap: i = arr.size): (go as bs f p arr i).size = as.size := by
  unfold go
  split
  . apply zipWithNSizeGo
    . apply Nat.succ_le_of_lt
      assumption
    . rw [Array.size_push]
      simp
      assumption
  . rw [<-ap] 
    apply Nat.le_antisymm
    . assumption
    . apply Nat.le_of_not_lt
      assumption
termination_by zipWithNSizeGo => as.size - i

theorem zipWithNSize: (zipWithN as bs f p).size = as.size := by 
  apply zipWithNSizeGo 
  . apply Nat.zero_le
  . simp [Array.size, List.length]

end ZipWithN

def zipWithN as bs (f: α -> β -> γ) := ZipWithN.zipWithN as bs f

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

structure Matr (α: Type) where
  data: Array (Array α) 
  n: Nat
  m: Nat
  ns: data.size = n
  ms (i: Fin n): (data.get ⟨i.val, by rw [ns] ; exact i.isLt⟩).size = m


namespace Matr
  variable (mat: Matr α)
  def get (i: Fin mat.n) (j: Fin mat.m): α := 
    let row := mat.data.get ⟨i.val, by rw[mat.ns] ; exact i.isLt⟩
    row[j]'(by rw [mat.ms i]; exact j.isLt)
  
  instance {α}: GetElem (Matr α) (Nat × Nat) α fun mat (i, j) => i < mat.n ∧ j < mat.m where
    getElem mat := fun (i, j) ⟨pi, pj⟩ => mat.get ⟨i, pi⟩ ⟨j, pj⟩

  structure Indices {α : Type} (mat: Matr α) where

  instance {mat: Matr α} : ForIn w (Indices mat) (Fin mat.n × Fin mat.m) where
    forIn _ b f := do
      let mut b := b
      for i in finRange mat.n do
        for j in finRange mat.m do
          match (<- f (i, j) b) with
          | .yield b' => b := b'
          | .done b'  => return b'
      return b

  -- def happend (mat': Matr α) (p: mat.n = mat'.n): { m: Matr α // m.n = mat.n ∧ m.m = (mat.m + mat'.m) } := 
  --   let ⟨data, q⟩ := mat.data.zipWithN mat'.data (· ++ ·) <| by rw [mat.ns, mat'.ns, p]
  --   let m := {
  --       data 
  --       n := mat.n
  --       m := mat.m + mat'.m
  --       ns := by rw [q, mat.ns]
  --       ms := by intro i; admit
  --   }
  --   ⟨m, by simp⟩
  def happend (mat': Matr α) (p: mat.n = mat'.n): Matr α := 
    let data := mat.data.zipWithN mat'.data (· ++ ·) <| by rw [mat.ns, mat'.ns, p]
    have q: data.size = mat.data.size := by apply Array.ZipWithN.zipWithNSize 
    {
        data 
        n := mat.n
        m := mat.m + mat'.m
        ns := by rw [q, mat.ns]
        ms := by intro i; admit
    }
end Matr




