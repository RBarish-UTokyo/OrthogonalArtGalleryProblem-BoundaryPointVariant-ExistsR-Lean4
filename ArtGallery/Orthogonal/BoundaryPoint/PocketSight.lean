module

public import ArtGallery.Orthogonal.BoundaryPoint.PerpendicularPin
public import Mathlib.Tactic.LinearCombination

/-! # A uniform angular bound for a thin single-mouth witness pocket

The frame puts the witness on the far wall and the mouth at a greater
normal coordinate. Outside the pocket, a visible point satisfies the
closed aperture inequality. The statement distinguishes a guard inside
the pocket, where its transverse distance is bounded by the pocket width.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PocketSight
open Set PerpendicularPin

theorem direction {p w q : Point} (hq : q ∈ segment w p)
    (h : w.2<q.2) :
    w.2<p.2 ∧ |p.1-w.1| * (q.2-w.2) = |q.1-w.1| * (p.2-w.2) := by
  obtain ⟨t,ht,_,rfl⟩ := hq
  change w.2<w.2+t*(p.2-w.2) at h
  have hprod : 0<t*(p.2-w.2) := by linarith only [h]
  have hn := pos_of_mul_pos_right hprod ht
  change _ ∧ |p.1-w.1| * (w.2+t*(p.2-w.2)-w.2) =
    |w.1+t*(p.1-w.1)-w.1| * (p.2-w.2)
  rw [add_sub_cancel_left,add_sub_cancel_left,abs_mul,abs_of_nonneg ht]
  exact ⟨sub_pos.mp hn,by ring⟩

theorem cone {P : Polygon} {F R : Set Point} (closedF : IsClosed F) (closedR : IsClosed R)
    (filled : P.filled=F∪R) (f : Frame) {w g : Point} (hw : w∈F) {A B : ℝ} (hA : 0<A)
    (pocket : ∀ p∈F, (f.pt w).2≤(f.pt p).2 ∧ |(f.pt p).1-(f.pt w).1| ≤ B)
    (mouth : ∀ q∈F∩R, (f.pt q).2=(f.pt w).2+A)
    (seen : P.Sees w g) :
    (f.pt w).2≤(f.pt g).2 ∧
    (|(f.pt g).1-(f.pt w).1| ≤ B ∨
      |(f.pt g).1-(f.pt w).1| * A≤B*((f.pt g).2-(f.pt w).2)) := by
  have hg := seen (Geometry.right_mem_segment w g)
  rw [filled] at hg
  rcases hg with inside|other
  · exact ⟨(pocket _ inside).1,Or.inl (pocket _ inside).2⟩
  obtain ⟨q,qseg,meet⟩ := SingleWindow.segment_meets_window closedF closedR hw other (filled ▸ seen)
  have he := mouth q meet
  have ⟨hn,eq⟩ := direction (f.segment qseg) (show (f.pt w).2<(f.pt q).2 by linarith)
  rw [he,add_sub_cancel_left] at eq
  refine ⟨hn.le,Or.inr (eq.trans_le ?_)⟩
  exact mul_le_mul_of_nonneg_right (pocket _ meet.1).2 (sub_nonneg.mpr hn.le)

theorem exclude {P : Polygon} {F R : Set Point} (closedF : IsClosed F) (closedR : IsClosed R)
    (filled : P.filled=F∪R) (f : Frame) {w g : Point} (hw : w∈F) {A B : ℝ} (hA : 0<A)
    (pocket : ∀ p∈F, (f.pt w).2≤(f.pt p).2 ∧ |(f.pt p).1-(f.pt w).1| ≤ B)
    (mouth : ∀ q∈F∩R, (f.pt q).2=(f.pt w).2+A)
    (test : (f.pt g).2<(f.pt w).2 ∨
      (B < |(f.pt g).1-(f.pt w).1| ∧
       B*((f.pt g).2-(f.pt w).2) < |(f.pt g).1-(f.pt w).1| * A)) :
    ¬P.Sees w g := by
  intro h
  have ⟨hn,hg⟩ := cone closedF closedR filled f hw hA pocket mouth h
  rcases test with back|gap
  · exact back.not_ge hn
  rcases hg with h|h
  · exact gap.1.not_ge h
  · exact gap.2.not_ge h

end ArtGallery.Orthogonal.BoundaryPoint.PocketSight
end
