import Advent


abbrev Point := Int × Int

inductive Event |start | stop | beac

deriving Ord, Lean.ToJson, Inhabited
open Event
instance: BEq Event where
  beq := (compare · · == Ordering.eq)

structure Sensor where
  location : Point
  beacon: Point
deriving Inhabited, Lean.ToJson


structure Rectangle where
  topLeft: Point
  bottomRight: Point
deriving Inhabited, Lean.ToJson

namespace Sensor
  variable (s: Sensor)

  def dist := (s.location.fst - s.beacon.fst).abs + (s.location.snd - s.beacon.snd).abs
  
  def interval(y: Int): Option (Int × Int) := do
    let ydist := (s.location.snd - y).abs
    let x := s.location.fst
    if ydist > s.dist then throw ()
    let rem := s.dist - ydist
    return (x - rem, x + rem + 1)

  def events (y: Int): List (Int × Event) := 
    let bs := if s.beacon.snd == y then [(s.beacon.fst, beac)] else []
    let is := if let some (b, e) := s.interval y then [(b, start), (e, stop)] else []
    bs ++ is

  def rotate: Rectangle := 
    let (x, y) := s.location
    let (rx, ry) := (x + y, x - y)
    let d := s.dist
    ⟨ (rx - d, ry - d), (rx + d + 1, ry + d + 1) ⟩
end Sensor

open Prod (fst snd)

structure Segment where
  b: Int
  e: Int

deriving Lean.ToJson

namespace Segment 
 variable (seg: Segment)

 def intersects (seg2: Segment): Bool := 
  seg2.e > seg.b && seg.e > seg2.b

 def inside (seg2: Segment): Bool :=
  seg2.b <= seg.b && seg.e <= seg2.e

 def contains (x: Int): Bool := 
  seg.b <= x && x < seg.e 

 def prod (seg2: Segment): Rectangle := 
  ⟨ (seg.b, seg2.b), (seg.e, seg2.e) ⟩

end Segment

namespace Rectangle
  variable (r: Rectangle)
  
  def area: Nat := 
    (r.topLeft.snd - r.bottomRight.snd).abs * (r.topLeft.fst - r.bottomRight.fst).abs

  def points : List Point := [r.topLeft, r.bottomRight]

  def hor: Segment := ⟨ r.topLeft.fst, r.bottomRight.fst ⟩

  def vert: Segment := ⟨ r.topLeft.snd, r.bottomRight.snd ⟩

  def contains (p: Point): Bool := 
    r.hor.contains p.fst && r.vert.contains p.snd   

  def corners: Id (Array Point) := do
    let mut res := Array.empty
    for x in [r.topLeft.fst, r.bottomRight.fst] do
      for y in [r.topLeft.snd, r.bottomRight.snd] do
        res := res.push (x, y)
    res
  
  def inside (r2: Rectangle): Bool := 
    r.vert.inside r2.vert && r.hor.inside r2.hor

  def intersects (r2: Rectangle): Bool := 
    r.hor.intersects r2.hor && r.vert.intersects r2.vert

  def cut (r2: Rectangle): List Rectangle := 
    if r.inside r2 then []
    else if !(r.intersects r2) then [r]
    else 
      let ps := r.points ++ r2.points
      let segs (f: Point -> Int) : List Segment := 
        let ps := ((ps.map f).toArray.qsort (· < ·)).toList
        ps.dropLast.zipWith Segment.mk ps.tail!

      let rects := (segs (·.fst)).bind (λ h => (segs (·.snd)).map h.prod)

      rects.filter (fun r3 => r3.inside r && !(r3.inside r2) && r3.area > 0)

end Rectangle

def unrotate (p: Point) : Point := 
  ((p.fst + p.snd) / 2, (p.fst - p.snd) / 2)


def parseLine: Parse Sensor := do
  Parse.str "Sensor at "
  let location <- parsePoint
  Parse.str ": closest beacon is at "
  let beacon <- parsePoint
  return ⟨ location, beacon ⟩
where 
  parsePoint := do
    Parse.str "x="
    let x <- Parse.int
    Parse.str ", y="
    let y <- Parse.int
    return (x, y)  

def countIntervals (xs: Array (Int × Event)) : Id Int := do
  let mut level := 0
  let mut prev := 0
  let mut count := 0
  let mut prevBeacon := none
  for (x, event)  in xs do
    match event with
    | start => 
      if level == 0 then
        prev := x
      level := level.succ
    | stop =>
      level := level.pred
      if level == 0 then
        count := count + x - prev
    | beac => 
      if level > 0 && some x != prevBeacon then 
        count := count - 1
        prevBeacon := some x

  return count     


instance : Ord (Int × Event) := lexOrd 
instance : LE (Int × Event) := leOfOrd




def main : IO Unit := do

  let lines <- readLines 15
  -- for l in lines do
  --   IO.println <| parseLine.runE l
  let y := lines.head!.toInt!
  let lines := lines.drop 1
  let sensors := (lines.mapM parseLine.run').get!
  let intervals := sensors.bind (·.events y) 
                   |> (·.toArray)
                   |> (·.qsort (· <= ·))
  IO.println intervals
  IO.println <| countIntervals intervals
  
  let start := Rectangle.mk (0, - 2 * y) (4 * y + 1, 2 * y + 1)

  let rects := sensors.foldl (fun rs s => rs.bind (·.cut s.rotate)) [start]
  
  let unite := rects.filter (·.area == 1)

  let goodPoints := unite.map (unrotate ·.topLeft)

  let freqs := goodPoints.map (fun (x, y) => x * 4000000 + y)
 
  IO.println rects.length
  IO.println unite
  IO.println goodPoints
  IO.println freqs