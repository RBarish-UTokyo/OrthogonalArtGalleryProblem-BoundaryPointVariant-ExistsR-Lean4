module

public import ArtGallery.Orthogonal.BoundaryPoint.SingleWindow
public import ArtGallery.Orthogonal.BoundaryPoint.ChimneyCells
public import Mathlib.Tactic.Linarith

/-! # Two-tip shaft witnesses in an attached polygon

The two far corners of a rectangular shaft force the guard's horizontal
coordinate into its closed mouth interval. Each tip separately bounds the
possible viewer abscissae using the known available vertical depth. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ShaftPortal
open Set ChimneyRegion

def mouth (l r h : ℝ) : Set Point := {p | l ≤ p.1 ∧ p.1 ≤ r ∧ p.2=h}

private theorem arm {l r h v : ℝ} {g q : Point} {x : ℝ}
    (hne : h ≠ v) (hq : q ∈ segment (x,v) g) (hm : q ∈ mouth l r h) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧ h-v=t*(g.2-v) ∧ l≤x+t*(g.1-x) ∧ x+t*(g.1-x)≤r := by
  obtain ⟨t,ht,ht',rfl⟩ := hq
  rcases hm with ⟨hlo,hhi,hy⟩
  change v+t*(g.2-v)=h at hy
  refine ⟨t,lt_of_le_of_ne ht ?_,ht',by linarith,hlo,hhi⟩
  rintro rfl
  exact hne (by simpa using hy.symm)

theorem two_tips {P : Polygon} {shaft rest : Set Point} (hs : IsClosed shaft) (hr : IsClosed rest)
    (hfill : P.filled = shaft ∪ rest) {l r h v : ℝ} (hne : h ≠ v)
    (hdoor : shaft ∩ rest ⊆ mouth l r h)
    (hl : (l,v) ∈ shaft) (hu : (r,v) ∈ shaft) {g : Point} (hg : g ∈ rest)
    (h₁ : P.Sees (l,v) g) (h₂ : P.Sees (r,v) g) : l ≤ g.1 ∧ g.1 ≤ r := by
  obtain ⟨q,hq,hm⟩ := SingleWindow.segment_meets_window hs hr hl hg (hfill ▸ h₁)
  obtain ⟨t,ht,_,_,hleft,_⟩ := arm hne hq (hdoor hm)
  obtain ⟨z,hz,hw⟩ := SingleWindow.segment_meets_window hs hr hu hg (hfill ▸ h₂)
  obtain ⟨u,hu',_,_,_,hright⟩ := arm hne hz (hdoor hw)
  constructor
  · by_contra! hn
    have := mul_neg_of_pos_of_neg ht (sub_neg.mpr hn)
    linarith
  · by_contra! hn
    have := mul_pos hu' (sub_pos.mpr hn)
    linarith

/-- If the viewer-to-tip vertical distance is at most three times the
mouth-to-tip distance, the left tip confines the viewer to three mouth widths. -/
theorem left_tip_band {P : Polygon} {shaft rest : Set Point} (hs : IsClosed shaft) (hr : IsClosed rest)
    (hfill : P.filled = shaft ∪ rest) {l r h v : ℝ}
    (hdoor : shaft ∩ rest ⊆ mouth l r h) (hl : (l,v) ∈ shaft) {g : Point} (hg : g ∈ rest)
    (hgap : 0 < |h-v|) (hdepth : |g.2-v| ≤ 3*|h-v|)
    (hsees : P.Sees (l,v) g) : l ≤ g.1 ∧ g.1 ≤ l+3*(r-l) := by
  have hne : h ≠ v := sub_ne_zero.mp (abs_pos.mp hgap)
  obtain ⟨q,hq,hm⟩ := SingleWindow.segment_meets_window hs hr hl hg (hfill ▸ hsees)
  obtain ⟨t,ht,_,hy,hleft,hright⟩ := arm hne hq (hdoor hm)
  have hy' := congrArg abs hy
  rw [abs_mul,abs_of_pos ht] at hy'
  have hcross := mul_le_mul_of_nonneg_left hdepth ht.le
  have h₃ : 1/3 ≤ t := by
    by_contra! hsmall
    have := mul_lt_mul_of_pos_right (show 3*t < 1 by linarith) hgap
    nlinarith only [this,hy',hcross]
  have hpos : 0 ≤ g.1-l := by
    by_contra! hn
    have := mul_neg_of_pos_of_neg ht hn
    linarith
  have hwidth := mul_le_mul_of_nonneg_right h₃ hpos
  exact ⟨by linarith,by nlinarith only [hright,hwidth]⟩

/-- The shaft itself supplies the same abscissa restriction for a viewer
inside it. This form may be applied before classifying the boundary edge. -/
theorem localized_abscissa {P : Polygon} {shaft rest : Set Point}
    (hs : IsClosed shaft) (hr : IsClosed rest) (hfill : P.filled = shaft ∪ rest)
    {l r h v : ℝ} (hne : h ≠ v) (hdoor : shaft ∩ rest ⊆ mouth l r h)
    (hx : ∀ p ∈ shaft, l ≤ p.1 ∧ p.1 ≤ r)
    (hl : (l,v) ∈ shaft) (hu : (r,v) ∈ shaft) {g : Point} (hg : g ∈ P.filled)
    (h₁ : P.Sees g (l,v)) (h₂ : P.Sees g (r,v)) : l ≤ g.1 ∧ g.1 ≤ r := by
  rw [hfill] at hg
  rcases hg with h | h
  · exact hx g h
  · apply two_tips hs hr hfill hne hdoor hl hu h
    · simpa only [Polygon.Sees,Geometry.segment_comm (l,v) g] using h₁
    · simpa only [Polygon.Sees,Geometry.segment_comm (r,v) g] using h₂

end ArtGallery.Orthogonal.BoundaryPoint.ShaftPortal
end
