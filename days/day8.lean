import Advent.Read
import Advent.List
import Advent.Ord
import Lean

class Visible (α β : Type _) where
  vision: List α -> List β
  combine: β -> β -> β

instance [Ord α]: Visible α Bool where
  combine := (· ||  ·)

  vision: List α -> List Bool
    | [] => []
    | x :: xs => true :: (xs.mapM see).run' x
    where 
      see (x: α) : StateM α Bool := 
        fun p => ((compare x p) == Ordering.gt, omax p x) 

instance [Ord α]: Visible α Nat where
  combine := (· * ·)

  vision (xs: List α ):= (xs.mapM see).run' (1, [])
    where 
      see (x: α) : StateM (Nat × List (α × Nat)) Nat
      | (i, []) => (i - 1, i + 1, [(x, i)])
      | (i, (y, j) :: rest) => 
        if y <? x 
        then see x (i, rest)
        else (i - j, i + 1, (x, i) :: (y, j) :: rest)
      
def vision2 [v: Visible α β] (xs: List α): List β := 
  let str : List β := v.vision xs
  let back: List β := (v.vision xs.reverse).reverse
  str.zipWith v.combine back

def vision4 (β : Type) [v: Visible α β] (xs: List (List α)): List (List β) := 
  let hor := xs.map vision2
  let vert := (xs.transpose.map vision2).transpose
  hor.zipWith (·.zipWith v.combine ·) vert

def main: IO Unit := do
  let ls <- readLines 8
  let cs := ls.map (·.toList)
  let visibles := vision4 Bool cs
  let visible := visibles.foldl (· + ·.foldl (· + if · then 1 else 0) 0) 0 
  IO.println cs
  let scores := vision4 Nat cs
  IO.println visible
  scores.bind (·) |> (·.foldl Max.max 0) |> IO.println

