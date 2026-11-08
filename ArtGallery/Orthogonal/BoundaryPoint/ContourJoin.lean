module

public import ArtGallery.Orthogonal.BoundaryPoint.RectContour
public import ArtGallery.Stade.PTimeRat

/-! # Polynomial-time splicing of the actual local boundary paths

Each horizontal hub edge lists the wing doors it contains. The complementary
paths replace those door intervals in descending spatial order. The total
number of replacements must equal the number of wings. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ContourJoin
open RectContour Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

abbrev Entrance := ℚ × List Vertex

def compat (w : ℚ) (e : Vertex × Vertex) (v : Entrance) : Bool :=
  e.1.2==1 && e.2.2==1 && decide (e.2.1<e.1.1) &&
    decide (e.2.1≤v.1) && decide (v.1+w≤e.1.1)

def sections (w : ℚ) (hub : List Vertex) (wings : List Entrance) : List (Vertex × List (List Vertex)) :=
  (hub.zip (hub.drop 1 ++ hub.take 1)).map fun e =>
    (e.1,(wings.filter (compat w e)).map Prod.snd)

def splice (w : ℚ) (hub : List Vertex) (wings : List Entrance) : Option (List Vertex) :=
  let rows := sections w hub wings
  if (rows.map fun r => r.2.length).sum=wings.length then
    some (rows.flatMap fun r => r.1::r.2.flatten)
  else none

def atDoor (d w : ℚ) (cycle : List Vertex) : Option (List Vertex) :=
  let i := cycle.idxOf (0,1)
  if (i ≥ cycle.length) || (cycle.getD ((i+1)%cycle.length) (0,0) != (w,1)) then none
  else some ((cycle.drop (i+1) ++ cycle.take (i+1)).map fun p => (p.1+d,p.2))

section Cost
variable {α : Type} [Code α]

private theorem nonneg_num (q : ℚ) : 0≤q.num ↔ 0≤q := Rat.num_nonneg

@[fun_prop] theorem rat_le {a b : α → ℚ} (ha : PT a) (hb : PT b) :
    PT (fun z => decide (a z≤b z)) := by
  have h : PT (fun z => !(intDigits (b z-a z).num).1) := by fun_prop
  apply h.of_eq
  intro z
  by_cases k : a z≤b z
  · have nonneg := (nonneg_num _).mpr (sub_nonneg.mpr k)
    simp [intDigits,k,not_lt.mpr nonneg]
  · have negative : (b z-a z).num<0 := lt_of_not_ge (fun hh => k (sub_nonneg.mp ((nonneg_num _).mp hh)))
    simp [intDigits,k,negative]

@[fun_prop] theorem rat_lt {a b : α → ℚ} (ha : PT a) (hb : PT b) :
    PT (fun z => decide (a z<b z)) := by
  have h : PT (fun z => !(decide (b z≤a z))) := by fun_prop
  apply h.of_eq
  intro z
  by_cases k : a z<b z
  · simp [k,not_le.mpr k]
  · simp [k,le_of_not_gt k]

@[fun_prop] theorem compatible_pt {w : α → ℚ} {e : α → Vertex × Vertex} {v : α → Entrance}
    (hw : PT w) (he : PT e) (hv : PT v) : PT (fun a => compat (w a) (e a) (v a)) := by
  unfold compat; fun_prop

@[fun_prop] theorem sections_pt {w : α → ℚ} {h : α → List Vertex} {ws : α → List Entrance}
    (hw : PT w) (hh : PT h) (hws : PT ws) : PT (fun a => sections (w a) (h a) (ws a)) := by
  unfold sections; fun_prop

theorem splice_pt {w : α → ℚ} {h : α → List Vertex} {ws : α → List Entrance}
    (hw : PT w) (hh : PT h) (hws : PT ws) : PT (fun a => splice (w a) (h a) (ws a)) := by
  unfold splice; dsimp only; fun_prop

theorem at_door_pt {d w : α → ℚ} {h : α → List Vertex}
    (hd : PT d) (hw : PT w) (hh : PT h) : PT (fun a => atDoor (d a) (w a) (h a)) := by
  unfold atDoor; dsimp only; fun_prop

end Cost
end ArtGallery.Orthogonal.BoundaryPoint.ContourJoin
end
