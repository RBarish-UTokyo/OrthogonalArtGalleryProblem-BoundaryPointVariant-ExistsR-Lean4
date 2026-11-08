module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyGap
public import ArtGallery.Orthogonal.BoundaryPoint.CopyDoor

/-! # The two copy tests of a channel

A base guard `B=(W+bD+tB,1-D)` below the door of a wing and a receiver
`R=(cx+d(r+tR/D),1-d)` in its room cover a thin box above the lower axis
`y=1+H`, where `W-bH=cx-rH`. The base sees only to the left of its ray through
the right door corner, the receiver only to the right of its ray through the
window corner. If no other guard sees the box, the two rays leave no gap on the
axis, which is exactly `tB ≤ tR`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyTest
open Set

/-- The point of the line through `B` and the door corner `(W,1)` at height `y`. -/
theorem base_side {W b D t y x : ℝ} (hD : 0<D)
    (right : W-(b+t/D)*(y-1)<x) : ArtGallery.det (W+b*D+t,1-D) (W,1) (x,y)<0 := by
  have h1 : -(b+t/D)*(y-1)<x-W := by linarith
  have h2 := mul_lt_mul_of_pos_left h1 hD
  have e2 : D*(-(b+t/D)*(y-1))=-(b*D+t)*(y-1) := by field_simp
  rw [e2] at h2
  have e3 : ArtGallery.det (W+b*D+t,1-D) (W,1) (x,y)=-(b*D+t)*(y-1)-D*(x-W) := by
    simp only [ArtGallery.det]; ring
  rw [e3]; linarith

theorem lower {P L : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=L.filled∪rest)
    (closed : IsClosed rest) (contact : L.filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {G : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈G, P.Sees g z)
    {b D tB cx d r tR H ε xa xb : ℝ} (hD : 0<D) (hH : 0<H) (hε : 0<ε) (deep : H+ε<D)
    (hB : ((W+b*D+tB,1-D):Point)∈rest) (hR : ((cx+d*(r+tR/D),1-d):Point)∈L.filled)
    (inside : ∀ x y : ℝ, xa<x → x<xb → 1+H<y → y<1+H+ε → (x,y)∈L.filled)
    (receiver : ∀ x y : ℝ, xa<x → x<xb → 1+H<y → y<1+H+ε → x<cx-(r+tR/D)*(y-1) →
      ¬L.Sees (cx+d*(r+tR/D),1-d) (x,y))
    (others : ∀ g∈G, g≠(W+b*D+tB,1-D) → g≠(cx+d*(r+tR/D),1-d) → ∀ x y : ℝ, xa<x → x<xb →
      1+H<y → y<1+H+ε → ¬P.Sees g (x,y))
    (incidence : W-b*H=cx-r*H)
    (ha : xa<W-(b+tB/D)*H) (hb : cx-(r+tR/D)*H<xb) : tB≤tR := by
  have sub : L.filled⊆P.filled := by rw [fill]; exact subset_union_left
  have key := CopyGap.no_gap (P:=P) (G:=G) cover (p:=(W+b*D+tB,1-D)) (q:=(cx+d*(r+tR/D),1-d))
    (a:=1+H) (ε:=ε) (xa:=xa) (xb:=xb) (αp:=W-(b+tB/D)*H) (βp:=-(b+tB/D))
    (αq:=cx-(r+tR/D)*H) (βq:=-(r+tR/D)) true hε
    (fun x y h0 h1 hy => by simp only [ite_true] at hy; exact sub (inside x y h0 h1 hy.1 hy.2))
    (fun x y h0 h1 hy right => by
      simp only [ite_true] at hy
      apply CopyDoor.beyond_right fill closed contact hW hB (by simp; linarith) (inside x y h0 h1 hy.1 hy.2)
      apply base_side hD
      have : W-(b+tB/D)*(y-1)=W-(b+tB/D)*H+-(b+tB/D)*(y-(1+H)) := by ring
      rw [this]; exact right)
    (fun x y h0 h1 hy left => by
      simp only [ite_true] at hy
      intro sees
      have convex : Convex ℝ (L.filled∩rest) := contact ▸ Geometry.segment_convex _ _
      have zL := inside x y h0 h1 hy.1 hy.2
      apply receiver x y h0 h1 hy.1 hy.2 (by
        have : cx-(r+tR/D)*(y-1)=cx-(r+tR/D)*H+-(r+tR/D)*(y-(1+H)) := by ring
        rw [this]; exact left)
      exact (SingleWindow.sees_iff fill closed convex hR zL).mp sees)
    (fun g hg e1 e2 x y h0 h1 hy _ _ => by simp only [ite_true] at hy; exact others g hg e1 e2 x y h0 h1 hy.1 hy.2)
    ha hb
  -- the incidence turns the axis inequality into tB ≤ tR
  have : tB*(H/D)≤tR*(H/D) := by
    have e : cx-(r+tR/D)*H-(W-(b+tB/D)*H)=(tB-tR)*(H/D) := by
      field_simp; linear_combination (-D)*incidence
    nlinarith
  exact le_of_mul_le_mul_right this (div_pos hH hD)

end ArtGallery.Orthogonal.BoundaryPoint.CopyTest
end
