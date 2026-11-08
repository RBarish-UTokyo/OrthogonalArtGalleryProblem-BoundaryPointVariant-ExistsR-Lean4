module

public import ArtGallery.Geometry.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! # Visibility across bands of an orthogonal polygon

Inside an open coordinate slab a sightline remains in a single transverse
band. Closedness includes its two limits even where the polygon has an extra
edge on a slab wall. Back projection turns these constraints into intervals
on a guard edge. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SlabSight
open Set

abbrev Band := ℝ × ℝ
def band (b : Band) := Icc b.1 b.2
def cover (bs : List Band) : Set ℝ := {y | ∃ b ∈ bs, y ∈ band b}

private theorem cover_cons (b : Band) (bs : List Band) : cover (b::bs)=band b ∪ cover bs := by
  ext y
  simp [cover]

private theorem closed_cover (bs : List Band) : IsClosed (cover bs) := by
  induction bs with
  | nil => simp [cover]
  | cons a bs ih => rw [cover_cons]; exact isClosed_Icc.union ih

theorem one_band {bs : List Band} {S : Set ℝ} (hS : S.Nonempty)
    (hc : IsPreconnected S) (hsep : bs.Pairwise fun a b => a.2 < b.1)
    (hin : S ⊆ cover bs) : ∃ b ∈ bs, S ⊆ band b := by
  induction bs with
  | nil =>
    obtain ⟨x,hx⟩ := hS
    simpa [cover] using hin hx
  | cons b bs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp hsep
    have empty : S ∩ (band b ∩ cover bs) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨_,hb,c,hc',hz⟩
      exact (head c hc').not_ge (hz.1.trans hb.2)
    rw [cover_cons] at hin
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hc _ _ isClosed_Icc
        (closed_cover bs) hin empty with first|rest
    · exact ⟨b,List.mem_cons_self,first⟩
    · obtain ⟨c,hc',hh⟩ := ih tail rest
      exact ⟨c,List.mem_cons_of_mem _ hc',hh⟩

theorem limits {l r : ℝ} (hl : l<r) {bs : List Band}
    (hsep : bs.Pairwise fun a b => a.2 < b.1) {v : ℝ → ℝ} (hv : Continuous v)
    (hin : ∀ x∈Ioo l r, v x∈cover bs) :
    ∃ b∈bs, v l∈band b ∧ v r∈band b := by
  obtain ⟨b,hb,hsub⟩ := one_band ((Set.nonempty_Ioo.mpr hl).image v)
    (isPreconnected_Ioo.image v hv.continuousOn) hsep (Set.image_subset_iff.mpr hin)
  have all := closure_minimal (Set.image_subset_iff.mp hsub) (isClosed_Icc.preimage hv)
  rw [closure_Ioo hl.ne] at all
  exact ⟨b,hb,all (Set.left_mem_Icc.mpr hl.le),all (Set.right_mem_Icc.mpr hl.le)⟩

def chart (swap : Bool) (u v : ℝ) : Point := if swap then (v,u) else (u,v)

noncomputable def height (wn wv gn gv x : ℝ) := wv+(x-wn)/(gn-wn)*(gv-wv)

theorem path {wn wv gn gv x : ℝ} (hs : wn ≠ gn) (hx : x∈uIcc wn gn) (swap : Bool) :
    chart swap x (height wn wv gn gv x) ∈
      ArtGallery.segment (chart swap wn wv) (chart swap gn gv) := by
  let t := (x-wn)/(gn-wn)
  have h₁ : 0≤t ∧ t≤1 := by
    rcases lt_or_gt_of_ne hs with h|h
    · rw [Set.uIcc_of_le h.le] at hx
      exact ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr h.le),
        (div_le_one (sub_pos.mpr h)).mpr (by linarith [hx.2])⟩
    · rw [Set.uIcc_of_ge h.le] at hx
      exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hx.2) (sub_nonpos.mpr h.le),
        (div_le_one_of_neg (sub_neg.mpr h)).mpr (by linarith [hx.1])⟩
  have h₂ : wn+t*(gn-wn)=x := by
    dsimp [t]; field_simp [sub_ne_zero.mpr hs.symm]; ring
  refine ⟨t,h₁.1,h₁.2,?_⟩
  cases swap <;> apply Prod.ext <;> simp [chart,height,t] at h₂ ⊢ <;> linarith

theorem sweep {P : Polygon} {wn wv gn gv l r : ℝ} (swap : Bool)
    (hs : wn≠gn) (hl : l<r) (inside : Ioo l r ⊆ uIcc wn gn)
    {bs : List Band} (hsep : bs.Pairwise fun a b => a.2<b.1)
    (free : ∀ x∈Ioo l r, ∀ y, chart swap x y ∈ P.filled → y∈cover bs)
    (hsight : P.Sees (chart swap wn wv) (chart swap gn gv)) :
    ∃ b∈bs, height wn wv gn gv l∈band b ∧ height wn wv gn gv r∈band b := by
  apply limits hl hsep (show Continuous (height wn wv gn gv) by unfold height; fun_prop)
  intro x hx
  exact free _ hx _ (hsight (path hs (inside hx) swap))

noncomputable def project (wn wv gn c h : ℝ) := wv+(gn-wn)*(h-wv)/(c-wn)

theorem projected_band {wn wv gn gv c : ℝ} {b : Band}
    (hd : 0 < (c-wn)/(gn-wn)) (hv : height wn wv gn gv c ∈ band b) :
    gv ∈ Icc (project wn wv gn c b.1) (project wn wv gn c b.2) := by
  let k := (c-wn)/(gn-wn)
  have hz : gn-wn≠0 := fun h => by simp [h] at hd
  have hc : c-wn≠0 := fun h => by simp [h] at hd
  have inv (a : ℝ) : project wn wv gn c a = wv+(a-wv)/k := by
    dsimp [project,k]; field_simp
  rw [inv,inv]
  change b.1 ≤ wv+k*(gv-wv) ∧ wv+k*(gv-wv)≤b.2 at hv
  constructor
  · apply (show (b.1-wv)/k≤gv-wv → wv+(b.1-wv)/k≤gv by intro h; linarith)
    apply (div_le_iff₀ hd).mpr
    linarith [mul_comm k (gv-wv),hv.1]
  · apply (show gv-wv≤(b.2-wv)/k → gv≤wv+(b.2-wv)/k by intro h; linarith)
    apply (le_div_iff₀ hd).mpr
    linarith [mul_comm k (gv-wv),hv.2]

end ArtGallery.Orthogonal.BoundaryPoint.SlabSight
end
