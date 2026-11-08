module

public import ArtGallery.Orthogonal.BoundaryPoint.HubColumns
public import ArtGallery.Orthogonal.BoundaryPoint.SingleWindow
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalShape

/-! # Windows of shafts and feet in the joined gallery

A base shaft is a closed rectangle meeting the rest of the joined polygon only
in its mouth on the low roof; a foot meets the rest only in its mouth on the
floor. A viewer outside such a rectangle of one of its far corners sees it
through the mouth, which bounds the viewer's abscissa. Two far corners force
the abscissa into the mouth interval, and a single far corner confines it to a
band of three mouth widths. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubWindows
open Set RectContour BoundaryChart BankCoordinates Geometry HubColumns

/-! ## Generic windows -/

def mouth (l r h : ℝ) : Set Point := {p | l≤p.1 ∧ p.1≤r ∧ p.2=h}

private theorem arm {l r h v : ℝ} {g q : Point} {x : ℝ}
    (hne : h≠v) (hq : q∈ArtGallery.segment (x,v) g) (hm : q∈mouth l r h) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧ h-v=t*(g.2-v) ∧ l≤x+t*(g.1-x) ∧ x+t*(g.1-x)≤r := by
  obtain ⟨t,ht,ht',rfl⟩ := hq
  rcases hm with ⟨hlo,hhi,hy⟩
  change v+t*(g.2-v)=h at hy
  refine ⟨t,lt_of_le_of_ne ht ?_,ht',by linarith,hlo,hhi⟩
  rintro rfl
  exact hne (by simpa using hy.symm)

/-- A viewer outside the rectangle of the far corner `(l,v)` sees it through the mouth `[l,r]`:
its abscissa is at least `l`, and at most `l+3(r-l)` when its depth is at most three mouth depths. -/
theorem left_tip {P : Polygon} {F R : Set Point} (hF : IsClosed F) (hR : IsClosed R)
    (cover : P.filled⊆F ∪ R) {l r h v : ℝ} (hne : h≠v) (hdoor : F∩R⊆mouth l r h)
    (hl : (l,v)∈F) {g : Point} (hg : g∈R) (sees : P.Sees (l,v) g) :
    l≤g.1 ∧ (|g.2-v|≤3*|h-v| → g.1≤l+3*(r-l)) := by
  obtain ⟨q,hq,hm⟩ := SingleWindow.segment_meets_window hF hR hl hg (fun z hz => cover (sees hz))
  obtain ⟨t,ht,_,hy,hleft,hright⟩ := arm hne hq (hdoor hm)
  have hpos : 0≤g.1-l := by
    by_contra! hn
    have := mul_neg_of_pos_of_neg ht hn
    linarith
  refine ⟨by linarith,fun hdepth => ?_⟩
  have hgap : 0 < |h-v| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hy' := congrArg abs hy
  rw [abs_mul,abs_of_pos ht] at hy'
  have hcross := mul_le_mul_of_nonneg_left hdepth ht.le
  have h₃ : 1/3≤t := by
    by_contra! hsmall
    have := mul_lt_mul_of_pos_right (show 3*t<1 by linarith) hgap
    nlinarith only [this,hy',hcross]
  have hwidth := mul_le_mul_of_nonneg_right h₃ hpos
  nlinarith only [hright,hwidth]

theorem right_tip {P : Polygon} {F R : Set Point} (hF : IsClosed F) (hR : IsClosed R)
    (cover : P.filled⊆F ∪ R) {l r h v : ℝ} (hne : h≠v) (hdoor : F∩R⊆mouth l r h)
    (hr : (r,v)∈F) {g : Point} (hg : g∈R) (sees : P.Sees (r,v) g) :
    g.1≤r ∧ (|g.2-v|≤3*|h-v| → r-3*(r-l)≤g.1) := by
  obtain ⟨q,hq,hm⟩ := SingleWindow.segment_meets_window hF hR hr hg (fun z hz => cover (sees hz))
  obtain ⟨t,ht,_,hy,hleft,hright⟩ := arm hne hq (hdoor hm)
  have hneg : g.1-r≤0 := by
    by_contra! hn
    have := mul_pos ht hn
    linarith
  refine ⟨by linarith,fun hdepth => ?_⟩
  have hgap : 0 < |h-v| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hy' := congrArg abs hy
  rw [abs_mul,abs_of_pos ht] at hy'
  have hcross := mul_le_mul_of_nonneg_left hdepth ht.le
  have h₃ : 1/3≤t := by
    by_contra! hsmall
    have := mul_lt_mul_of_pos_right (show 3*t<1 by linarith) hgap
    nlinarith only [this,hy',hcross]
  have hwidth := mul_le_mul_of_nonneg_right h₃ (show 0≤r-g.1 by linarith)
  nlinarith only [hleft,hwidth]

/-! ## Slots of the hub -/

theorem placed_apart {ss : List ℚ} (h : ss.Pairwise fun x y => x+10≤y) {x y : ℚ} (hx : x∈ss) (hy : y∈ss)
    (ne : x≠y) : x+10≤y ∨ y+10≤x := by
  induction ss with
  | nil => simp at hx
  | cons a ss ih =>
    obtain ⟨ha,hs⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hx with rfl|hx' <;> rcases List.mem_cons.mp hy with rfl|hy'
    · exact absurd rfl ne
    · exact Or.inl (ha y hy')
    · exact Or.inr (ha x hx')
    · exact ih hs hx' hy'

end ArtGallery.Orthogonal.BoundaryPoint.HubWindows
end
