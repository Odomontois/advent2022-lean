def omax [Ord α] (x y : α): α := 
  if compare x y == Ordering.gt then x else y

def blt [Ord α] (x y: α): Bool := compare x y == Ordering.lt
def bgt [Ord α] (x y: α): Bool := compare x y == Ordering.gt



infixl:50 " <? " => blt
infixl:50 " >? " => bgt