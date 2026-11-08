module

public import ArtGallery.Orthogonal.BoundaryPoint.CorridorProgram
public import Mathlib.Data.List.Sort

/-! # Boundary traversal for a finite union of rational rectangles

Use the finite coordinate grid. An occupied open cell contributes each side
whose neighbour is empty, oriented with the occupied cell to the left.
Accept a single oriented boundary cycle and omit its intermediate collinear
vertices. Component, pinch and input-order failures return none.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RectContour
open CorridorProgram

abbrev Vertex := ℚ × ℚ

def levels (l : List ℚ) : Array ℚ := (l.eraseDups.mergeSort (· ≤ ·)).toArray

def turn (a b c : Vertex) : Bool :=
  !((a.1 == b.1 && b.1 == c.1) || (a.2 == b.2 && b.2 == c.2))

def boundary (rs : List (Rect ℚ)) : Option (List Vertex) := Id.run do
  if rs.isEmpty then return none
  let xs := levels (rs.flatMap fun r => [r.1,r.2.1])
  let ys := levels (rs.flatMap fun r => [r.2.2.1,r.2.2.2])
  let ny := ys.size
  let nx := xs.size
  if nx < 2 ∨ ny < 2 then return none
  let index := fun i j : Nat => i*ny+j
  let mut occupied := Array.replicate (nx*ny) false
  for r in rs do
    let i := xs.findIdx (· == r.1)
    let j := ys.findIdx (· == r.2.2.1)
    let k := xs.findIdx (· == r.2.1)
    let h := ys.findIdx (· == r.2.2.2)
    if k ≤ i ∨ h ≤ j then return none
    for a in [i:k] do
      for b in [j:h] do occupied := occupied.setIfInBounds (index a b) true
  let fill := fun i j => occupied[index i j]?.getD false
  let mut next : Array (Option Nat) := Array.replicate (nx*ny) none
  let mut edgeCount := 0
  for i in [:nx-1] do
    for j in [:ny-1] do
      if fill i j then
        let a := index i j
        let b := index (i+1) j
        let c := index (i+1) (j+1)
        let d := index i (j+1)
        let sides := [(j==0 || !fill i (j-1),a,b),
                      (!fill (i+1) j,b,c),(!fill i (j+1),c,d),
                      (i==0 || !fill (i-1) j,d,a)]
        for (exposed,u,v) in sides do
          if exposed then
            if (next[u]?.join).isSome then return none
            next := next.setIfInBounds u (some v)
            edgeCount := edgeCount+1
  let some start := next.findIdx? Option.isSome | return none
  let mut cycle : Array Vertex := #[]
  let mut current := start
  for t in [:edgeCount] do
    if (0 < t) && (current == start) then return none
    let some nextIndex := next[current]?.join | return none
    cycle := cycle.push (xs[current/ny]?.getD 0,ys[current%ny]?.getD 0)
    current := nextIndex
  if current != start then return none
  let mut corners := #[]
  for j in [:edgeCount] do
    let z := cycle[j]?.getD (0,0)
    if turn (cycle[(j+edgeCount-1)%edgeCount]?.getD (0,0)) z (cycle[(j+1)%edgeCount]?.getD (0,0)) then
      corners := corners.push z
  if corners.size<4 then return none
  return some corners.toList

end ArtGallery.Orthogonal.BoundaryPoint.RectContour
end
