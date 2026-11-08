module

public import ArtGallery.Orthogonal.BoundaryPoint.SlabSight
public import ArtGallery.Geometry.Det
public import Mathlib.Tactic.Ring

/-! # Cross-section exclusions for continuous sets of guards and targets

The oriented area across a cut is separately affine in the guard and target.
A strict sign verified at every endpoint pair therefore holds on both convex
hulls. A single empty band then excludes all their sightlines. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CutHull
open Set Geometry

private theorem convex_pos (f : Point → ℝ)
    (aff : ∀ p q t, f (lerp p q t)=(1-t)*f p+t*f q) :
    Convex ℝ {z | 0<f z} := by
  apply convex_iff_segment_subset.mpr
  intro a ha b hb
  rw [← segment_eq]
  rintro p ⟨t,ht,hu,rfl⟩
  change 0<f (lerp a b t)
  rw [aff]
  change 0<f a at ha
  change 0<f b at hb
  rcases eq_or_lt_of_le ht with e|h
  · rw [← e]; simpa using ha
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hu) ha.le) (mul_pos h hb)

theorem signed_hulls {A B : Set Point} (v : Point) (sign : ℝ)
    (corners : ∀ a∈A, ∀ b∈B, 0<sign*det a b v) {p q : Point}
    (hp : p∈convexHull ℝ A) (hq : q∈convexHull ℝ B) :
    0<sign*det p q v := by
  have along (a : Point) (ha : a∈A) : 0<sign*det a q v := by
    apply convexHull_min (s:=B) (t:={z | 0<sign*det a z v}) (corners a ha) _ hq
    exact convex_pos _ (fun p q t => by rw [det_lerp_mid]; ring)
  apply convexHull_min (s:=A) (t:={z | 0<sign*det z q v}) along _ hp
  exact convex_pos _ (fun p r t => by rw [det_lerp_left]; ring)

theorem cut_value {p q : Point} {c h : ℝ} (hd : p.1<q.1) :
    (SlabSight.height p.1 p.2 q.1 q.2 c-h)*(q.1-p.1) = -det p q (c,h) := by
  unfold SlabSight.height det
  dsimp only
  field_simp [sub_ne_zero.mpr hd.ne'] <;> ring

theorem excludes {P : Polygon} {A B : Set Point} {l r c : ℝ}
    (empty : ∀ y, l<y → y<r → (c,y)∉P.filled)
    (lower : ∀ a∈A, ∀ b∈B, 0 < (-1:ℝ)*det a b (c,l))
    (upper : ∀ a∈A, ∀ b∈B, 0 < (1:ℝ)*det a b (c,r))
    {p q : Point} (hp : p∈convexHull ℝ A) (hq : q∈convexHull ℝ B)
    (pleft : p.1<c) (qright : c<q.1) : ¬P.Sees p q := by
  intro h
  have hd := pleft.trans qright
  have lo := signed_hulls _ _ lower hp hq
  have hi := signed_hulls _ _ upper hp hq
  rw [neg_one_mul,← cut_value hd] at lo
  rw [one_mul] at hi
  have bound := cut_value (c:=c) (h:=r) hd
  have pos := sub_pos.mpr hd
  let y := SlabSight.height p.1 p.2 q.1 q.2 c
  have yl : l<y := sub_pos.mp (pos_of_mul_pos_left lo pos.le)
  have yr : y<r := by
    apply sub_neg.mp
    apply neg_of_mul_neg_left (b:=q.1-p.1) _ pos.le
    rw [bound]; exact neg_neg_of_pos hi
  have cut : c∈uIcc p.1 q.1 := Set.uIcc_of_le hd.le ▸ ⟨pleft.le,qright.le⟩
  exact empty y yl yr (h (SlabSight.path hd.ne cut false))

end ArtGallery.Orthogonal.BoundaryPoint.CutHull
end
