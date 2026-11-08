module

public import ArtGallery.Orthogonal.BoundaryPoint.SingleWindow
public import ArtGallery.Geometry.Det

/-! # Sight lines through the closed door of a wing

A guard outside the wing sees a wing point only through the closed horizontal
door. A target strictly beyond the line through the guard and the right door
corner is therefore invisible, and a guard seeing a target meets the door at a
point of the same sight line. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyDoor
open Set

variable {P L : Polygon} {rest : Set Point} {W : ℝ}

/-- A guard outside the wing and below the door line meets the door on every sight line
into the wing. -/
theorem door_point (fill : P.filled=L.filled∪rest) (closed : IsClosed rest)
    (contact : L.filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) {B z : Point}
    (hB : B∈rest) (hz : z∈L.filled) (sees : P.Sees B z) :
    ∃ q∈ArtGallery.segment B z, q∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1) := by
  obtain ⟨q,hq,both⟩ := SingleWindow.segment_meets_window closed (Jordan.isClosed_filled L) hB hz
    (fun y hy => by rw [Set.union_comm,←fill]; exact sees hy)
  refine ⟨q,hq,?_⟩
  rw [←contact]; exact ⟨both.2,both.1⟩

theorem door_coords {q : Point} (hW : 0≤W) (hq : q∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) :
    q.2=1 ∧ 0≤q.1 ∧ q.1≤W := by
  obtain ⟨t,t0,t1,rfl⟩ := hq
  simp only
  refine ⟨by ring,by nlinarith,by nlinarith⟩

/-- Beyond the line through the guard and the right door corner nothing is visible. -/
theorem beyond_right (fill : P.filled=L.filled∪rest) (closed : IsClosed rest)
    (contact : L.filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W) {B z : Point}
    (hB : B∈rest) (hBy : B.2<1) (hz : z∈L.filled)
    (right : ArtGallery.det B (W,1) z<0) : ¬P.Sees B z := by
  intro sees
  obtain ⟨q,hq,door⟩ := door_point fill closed contact hB hz sees
  obtain ⟨qy,q0,qW⟩ := door_coords hW door
  have qB : q≠B := by intro h; rw [h] at qy; linarith
  obtain ⟨μ,μ0,μ1,e⟩ := hq
  have μpos : 0<μ := by
    rcases eq_or_lt_of_le μ0 with h|h
    · exfalso; apply qB; rw [e,←h]; simp
    · exact h
  have dq : ArtGallery.det B (W,1) q=μ*ArtGallery.det B (W,1) z := by
    rw [e]; simp only [ArtGallery.det]; ring
  have dq' : ArtGallery.det B (W,1) q=(1-B.2)*(W-q.1) := by
    simp only [ArtGallery.det,qy]; ring
  have := mul_neg_of_pos_of_neg μpos right
  nlinarith

/-- On the door point of a sight line, the sign of a determinant with any corner is that of
the target, up to a positive factor. -/
theorem det_on_line {B z q c : Point} (hq : q∈ArtGallery.segment B z) (qz : q≠z) :
    ∃ k : ℝ, 0<k ∧ ArtGallery.det z q c=k*ArtGallery.det z B c := by
  obtain ⟨μ,μ0,μ1,e⟩ := hq
  have μlt : μ<1 := by
    rcases eq_or_lt_of_le μ1 with h|h
    · exfalso; apply qz; rw [e,h]; simp
    · exact h
  refine ⟨1-μ,by linarith,?_⟩
  rw [e]; simp only [ArtGallery.det]; ring

/-- A guard outside the wing sees a wing point only if the door point of the sight line
sees it inside the wing. With a certified sign at the door, the guard's own sign excludes it. -/
theorem through_door (fill : P.filled=L.filled∪rest) (closed : IsClosed rest)
    (contact : L.filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W) {B z c : Point} {σ : ℝ}
    (hB : B∈rest) (hz : z∈L.filled) (hzy : 1<z.2) (side : 0<σ*ArtGallery.det z B c)
    (door : ∀ q∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), 0<σ*ArtGallery.det z q c → ¬L.Sees q z) :
    ¬P.Sees B z := by
  intro sees
  obtain ⟨q,hq,inDoor⟩ := door_point fill closed contact hB hz sees
  obtain ⟨qy,_,_⟩ := door_coords hW inDoor
  have qz : q≠z := by intro e; rw [e] at qy; linarith
  obtain ⟨k,kp,dk⟩ := det_on_line (c:=c) hq qz
  have qL : q∈L.filled := (contact ▸ inDoor).1
  have seesQ : P.Sees q z := by
    intro p hp
    apply sees
    exact Geometry.segment_subset_of_convex (Geometry.segment_convex B z) hq (Geometry.right_mem_segment _ _) hp
  have convex : Convex ℝ (L.filled∩rest) := contact ▸ Geometry.segment_convex _ _
  apply door q inDoor (by rw [dk]; nlinarith)
  exact (SingleWindow.sees_iff fill closed convex qL hz).mp seesQ

end ArtGallery.Orthogonal.BoundaryPoint.CopyDoor
end
