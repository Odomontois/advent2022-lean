def List.group (l: List α) (n: Nat): List (List α) := 
  loop l n [] []
where
  loop : List α -> Nat ->  List α -> List (List α)  -> List (List α)
  | [], _, gacc, acc=> (gacc.reverse :: acc).reverse
  | x :: xs, 0, gacc, acc => loop xs (n - 1)  [x] (gacc.reverse :: acc) 
  | x :: xs, rem + 1, gacc, acc => loop xs rem (x :: gacc) acc  

def List.transpose : List (List α) -> List (List α)  
| [] => []
| [lst] => lst.map ([·])
| head :: rest => head.zipWith (· :: ·) (transpose rest)

def List.transposeRev : List (List α) -> List (List α)
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

def List.scanl (xs: List α) (f: β -> α -> β) (init: β): List β := 
  let go (a: α): StateM β β := fun b => 
    let x := f b a
    (x, x)
  init :: (xs.mapM go).run' init

def List.sum [HAdd α α α] [OfNat α 0] (xs: List α): α := xs.foldl (· + ·) 0

def List.product [HMul α α α] [OfNat α 1] (xs: List α): α := xs.foldl (· * ·) 1

def List.append_eq_nil {xs ys : List α} : [] = xs ++ ys -> [] = xs /\ [] = ys := by
  intro p
  cases xs
  . simp at p
    simp
    assumption
  . contradiction
