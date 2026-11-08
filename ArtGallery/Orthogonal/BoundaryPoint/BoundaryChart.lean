module

public import ArtGallery.Orthogonal.BoundaryPoint.GeometryTime
public import ArtGallery.Orthogonal.BoundaryPoint.GridPins

/-! # Drawing a catalogued wing and its common hub
The coordinate ranks and the cyclic list of turns of each private wing are
fixed. Looking up the specified ranks avoids a traversal of the parameter
grid. The hub turns are listed in order along its floor and then its ceiling. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.BoundaryChart
open RoomGrid CorridorProgram RectContour BankCoordinates PlanGeometry
open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade ArtGallery.Orthogonal.Hard

structure Chart where
  x : List Nat
  y : List Nat
  cycle : Cycle

def pool {α : Type} (ys : Bool) (g : Data α) : List α :=
  (g.1.flatMap fun r => if ys then [r.2.2.1,r.2.2.2] else [r.1,r.2.1]) ++
    g.2.flatten.map (fun v => if ys then v.2 else v.1)

def selected {α : Type} [Zero α] (p : List α) (indices : List Nat) := indices.map fun i => p.getD i 0

def chartPt {α : Type} [Zero α] (xs ys : List α) (j : Index) := (xs.getD j.1 0,ys.getD j.2 0)

def Chart.draw (c : Chart) (g : Data ℚ) : List Vertex :=
  let xs := selected (pool false g) c.x
  let ys := selected (pool true g) c.y
  c.cycle.points.map (chartPt xs ys)

private theorem cast_getD (l : List ℚ) (i : Nat) :
    ((l.getD i 0 : ℚ):ℝ)=(l.map ((↑) : ℚ → ℝ)).getD i 0 := by
  simpa using (List.getD_map (l:=l) (d:=0) (n:=i) ((↑) : ℚ → ℝ)).symm

def actual (c : Chart) (g : Data ℚ) : Polygon := ⟨(c.draw g).map ratPoint⟩

theorem actual_grid (c : Chart) (g : Data ℚ) :
    actual c g = ⟨c.cycle.points.map (gridPt
      ((selected (pool false g) c.x).map ((↑) : ℚ → ℝ))
      ((selected (pool true g) c.y).map ((↑) : ℚ → ℝ)))⟩ := by
  unfold actual Chart.draw
  congr 1
  simp only [List.map_map,Function.comp_def,ratPoint,chartPt,cast_getD]
  rfl

theorem orthogonal (c : Chart) (h : cyclicAxis c.cycle.points) (g : Data ℚ) :
    (actual c g).Orthogonal := by rw [actual_grid]; exact grid_orthogonal _ _ _ h

theorem simple (c : Chart) (check : c.cycle.ok=true)
    (bounds : ∀ p∈c.cycle.points, p.1<c.x.length ∧ p.2<c.y.length) (g : Data ℚ)
    (hx : ((selected (pool false g) c.x).map ((↑) : ℚ → ℝ)).IsChain (·<·))
    (hy : ((selected (pool true g) c.y).map ((↑) : ℚ → ℝ)).IsChain (·<·)) :
    (actual c g).Simple := by
  rw [actual_grid]
  apply c.cycle.simple hx hy _ check
  simpa [selected] using bounds

def foot (f : ℚ) (j : Nat) : List Vertex :=
  let d := door j
  let l := d+100-1/1000
  let r := d+100+1/1000
  [(l,f),(l,2*f),(r,2*f),(r,f)]

def divider (f p : ℚ) : List Vertex :=
  let d := p-2
  [(d-1,f),(d-1,f+1/4),(d,f+1/4),(d,f+1/100000000),(d-1/10,f+1/100000000),(d-1/10,f)]

def shaft (f p : ℚ) : List Vertex :=
  [(p+3/2,-6),(p+3/2,-6-f),(p,-6-f),(p,-6)]

def capPath (count j : Nat) : List Vertex :=
  let d := door j
  [(d+110,-6),(d+110,1-1/10000),(d+110+1/10,1-1/10000),(d+110+1/10,1),(d-30,1)] ++
    (if j+1<count then [(d-30,-6)] else [])

def hubCycle (n count : Nat) (slots : List ℚ) : List Vertex :=
  let f := 1-D n
  let l := door (count-1)-30
  let r := slots.getLastD 0+10
  [(l-1/10,f)] ++ (List.range count).reverse.flatMap (foot f) ++ slots.tail.flatMap (divider f) ++
    [(r,f),(r,-6)] ++ slots.reverse.flatMap (shaft f) ++ (List.range count).flatMap (capPath count) ++
    [(l,f+1/100000000),(l-1/10,f+1/100000000)]

section Time
variable {α : Type} [Code α]

@[fun_prop] theorem pool_pt (b : Bool) {g : α → Data ℚ} (hg : PT g) : PT (fun a => pool b (g a)) := by
  cases b <;> unfold pool <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop

@[fun_prop] theorem selected_pt {p : α → List ℚ} {i : α → List Nat} (hp : PT p) (hi : PT i) :
    PT (fun a => selected (p a) (i a)) := by unfold selected; fun_prop

@[fun_prop] theorem chart_pt {xs ys : α → List ℚ} {j : α → Index} (hx : PT xs) (hy : PT ys) (hj : PT j) :
    PT (fun a => chartPt (xs a) (ys a) (j a)) := by unfold chartPt; fun_prop

theorem draw_pt (c : Chart) {g : α → Data ℚ} (hg : PT g) : PT (fun a => c.draw (g a)) := by
  unfold Chart.draw; fun_prop

@[fun_prop] theorem foot_pt {f : α → ℚ} {j : α → Nat} (hf : PT f) (hj : PT j) :
    PT (fun a => foot (f a) (j a)) := by unfold foot; fun_prop
@[fun_prop] theorem divider_pt {f p : α → ℚ} (hf : PT f) (hp : PT p) :
    PT (fun a => divider (f a) (p a)) := by unfold divider; fun_prop
@[fun_prop] theorem shaft_pt {f p : α → ℚ} (hf : PT f) (hp : PT p) :
    PT (fun a => shaft (f a) (p a)) := by unfold shaft; fun_prop
@[fun_prop] theorem cap_pt {n j : α → Nat} (hn : PT n) (hj : PT j) :
    PT (fun a => capPath (n a) (j a)) := by unfold capPath; fun_prop

theorem hub_pt {n count : α → Nat} {ss : α → List ℚ} (hn : PT n) (hc : PT count) (hs : PT ss) :
    PT (fun a => hubCycle (n a) (count a) (ss a)) := by unfold hubCycle; fun_prop

end Time
end ArtGallery.Orthogonal.BoundaryPoint.BoundaryChart
end
