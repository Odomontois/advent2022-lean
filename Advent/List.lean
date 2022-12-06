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
