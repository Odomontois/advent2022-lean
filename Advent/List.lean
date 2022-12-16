def List.group (l: List α) (n: Nat): List (List α) := 
  loop l n [] []
where
  loop : List α -> Nat ->  List α -> List (List α)  -> List (List α)
  | [], _, gacc, acc=> (gacc.reverse :: acc).reverse
  | x :: xs, 0, gacc, acc => loop xs (n - 1)  [x] (gacc.reverse :: acc) 
  | x :: xs, rem + 1, gacc, acc => loop xs rem (x :: gacc) acc  
  
def tails: List α -> List (List α)
| x :: xs => (x :: xs) :: tails xs
| [] => []

def differs [BEq α]: List α -> Bool
| [] => true
| x :: xs => xs.all (· != x) && differs xs

def List.sum [HAdd α α α] [OfNat α 0] (xs: List α): α := xs.foldl (· + ·) 0

def List.prod [HMul α α α] [OfNat α 1] (xs: List α): α := xs.foldl (· * ·) 1
