def compN (f: α -> α) (n: Nat) (a: α) : α := match n with
| 0 => a
| n' + 1 => compN f n' (f a) 