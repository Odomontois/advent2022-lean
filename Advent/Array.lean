import Lean
import Std
import Lean.Elab.Command


abbrev Matrix α := Array (Array α)


structure FinRange (n: Nat) 

def finRange (n: Nat): FinRange n := {}

def FinRange.forIn [Monad m] (rng: FinRange n) (b: β) (f: Fin n -> β -> m (ForInStep β)) (i: Nat): m β :=
  if p: i < n then do 
      let step <- f ⟨i, p⟩ b
      match step with 
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
end Matr




