def omax [Ord α] (x y : α): α := 
  if compare x y == Ordering.gt then x else y

def blt [Ord α] (x y: α): Bool := compare x y == Ordering.lt



infix:50 " <? " => blt