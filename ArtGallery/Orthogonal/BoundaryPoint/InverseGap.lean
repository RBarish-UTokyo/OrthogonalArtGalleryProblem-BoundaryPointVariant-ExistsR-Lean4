module

public import ArtGallery.Orthogonal.BoundaryPoint.AxisBlock
public import ArtGallery.Membership.Witness.Visibility

/-! # Recover an inverse comparison from a physically guarded room
Closedness of the two receiver visibility regions transfers a cover of the
open side of the critical box to its limiting axis. A strictly inverted pair
of intercepts would leave their midpoint unseen. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.InverseGap
open Set Geometry RoomCoordinates RoomPolynomials RoomGrid CorridorProgram RoomExclusion
open GridParity PinGridData ArtGallery.Orthogonal.Hard

theorem axis_order {P : Polygon} {g h : Point} {left axis bottom top a b : ℝ}
    (width : left<axis) (aBounds : bottom<a ∧ a<top) (bBounds : bottom<b ∧ b<top)
    (cover : ∀ X, left≤X → X<axis → ∀ Y, bottom≤Y → Y≤top → P.Sees g (X,Y) ∨ P.Sees h (X,Y))
    (above : ∀ Y, bottom≤Y → Y≤top → P.Sees g (axis,Y) → a≤Y)
    (below : ∀ Y, bottom≤Y → Y≤top → P.Sees h (axis,Y) → Y≤b) : a≤b := by
  by_contra! bad
  let mid := (a+b)/2
  have lo : bottom≤mid := by dsimp [mid]; linarith [aBounds.1,bBounds.1]
  have hi : mid≤top := by dsimp [mid]; linarith [aBounds.2,bBounds.2]
  let visible : Set Point := {p | P.Sees g p} ∪ {p | P.Sees h p}
  have closed : IsClosed visible :=
    (Membership.Witness.isClosed_sees P g).union (Membership.Witness.isClosed_sees P h)
  have cont : Continuous (fun X : ℝ => ((X,mid):Point)) := by fun_prop
  have sub : Ico left axis ⊆ (fun X : ℝ => ((X,mid):Point)) ⁻¹' visible :=
    fun X hX => cover X hX.1 hX.2 mid lo hi
  have limit := closure_minimal sub (closed.preimage cont)
  rw [closure_Ico width.ne] at limit
  rcases limit (right_mem_Icc.mpr width.le) with seen|seen
  · have := above mid lo hi seen; dsimp [mid] at this; linarith
  · have := below mid lo hi seen; dsimp [mid] at this; linarith

def fits (x y : Axis) (l r low high : P) (c : Rect Nat) :=
  (leP ((axisPolys x).getD c.1 []) l && leP r ((axisPolys x).getD c.2.1 [])) &&
    (leP ((axisPolys y).getD c.2.2.1 []) low && leP high ((axisPolys y).getD c.2.2.2 []))

theorem free_box {s : ℝ} (hs : 0<s) (hu : s≤1/65) {Q : Polygon} {x y : Axis} {rs : List (Rect Nat)}
    (hf : Q.filled=cellsR (x.coordsR s) (y.coordsR s) rs) {r : Rect Nat} (hr : r∈rs)
    {l h b t : P} (check : fits x y l h b t r=true) (X Y : ℝ)
    (xl : evalR s l≤X) (xh : X≤evalR s h) (yl : evalR s b≤Y) (yh : Y≤evalR s t) : (X,Y)∈Q.filled := by
  simp only [fits,Bool.and_eq_true] at check
  have L := le_sound hs hu check.1.1
  have R := le_sound hs hu check.1.2
  have B := le_sound hs hu check.2.1
  have T := le_sound hs hu check.2.2
  rw [index_value] at L R B T
  exact hf ▸ ⟨r,hr,L.trans xl,xh.trans R,B.trans yl,yh.trans T⟩

theorem slot_member {s : ℝ} (x y : Axis) (roles : List (List Index)) (i : Nat) {u : ℝ}
    (hu : DerivedAlgebra.InRange u) :
    SlotLines.slot (gridPt (x.coordsR s) (y.coordsR s)) roles i (u-1/2) ∈
      ArtGallery.segment (pt s ((AxisBlock.ends x y roles i).getD 0 ([],[])))
        (pt s ((AxisBlock.ends x y roles i).getD 1 ([],[]))) := by
  change _ ∈ ArtGallery.segment (pt s (polyNode x y (nodeAt roles i 1))) (pt s (polyNode x y (nodeAt roles i 2)))
  rw [node_value,node_value]
  apply lerp_mem_segment
  · linarith [hu.1]
  · linarith [hu.2]

theorem target {s Y : ℝ} {t b a : P} (hl : evalR s b≤Y) (hu : Y≤evalR s t) :
    ((evalR s a,Y):Point)∈ArtGallery.segment (pt s (a,b)) (pt s (a,t)) :=
  Jordan.mem_segment_of_vertical rfl rfl hl hu

end ArtGallery.Orthogonal.BoundaryPoint.InverseGap
end
