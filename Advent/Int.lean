open Ordering 

def Int.signum(x: Int) :Int := match compare x 0 with
| lt => -1
| eq => 0
| gt => 1

def Int.abs(x: Int) := x * signum x