open Ordering 
namespace Int
def signum: Int -> Int
| ofNat 0 => 0
| ofNat (Nat.succ _) => 1
| negSucc _ => -1

def abs: Int -> Nat
| ofNat x => x
| negSucc y => y + 1

end Int