module

public import ArtGallery.Jordan.Jordan

/-! # Regions inside a simple polygon

A preconnected set that avoids the boundary and contains one filled point lies in the filled
region: the interior and the exterior are disjoint open sets covering it. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubRegion
open Set

theorem region_sub {P : Polygon} (hP : P.Simple) {U : Set Point} (hU : IsPreconnected U)
    (hb : ∀ q∈U, q∉P.boundary) {p : Point} (hp : p∈U) (hpf : p∈P.filled) : U⊆P.filled := by
  have oA := Jordan.isOpen_filled_sdiff_boundary hP
  have oB := Jordan.isOpen_filled_compl P
  have cover : U⊆(P.filled \ P.boundary)∪P.filledᶜ := by
    intro q hq
    by_cases h : q∈P.filled
    · exact Or.inl ⟨h,hb q hq⟩
    · exact Or.inr h
  have disj : Disjoint (P.filled \ P.boundary) P.filledᶜ :=
    Set.disjoint_left.mpr fun q h1 h2 => h2 h1.1
  rcases (isPreconnected_iff_subset_of_disjoint.mp hU) _ _ oA oB cover
      (by rw [Set.disjoint_iff_inter_eq_empty.mp disj]; exact Set.inter_empty U) with h|h
  · exact fun q hq => (h hq).1
  · exact absurd hpf (h hp)

/-- The closure of such a region also lies in the filled region (which is closed). -/
theorem closure_sub {P : Polygon} (hP : P.Simple) {U : Set Point} (hU : IsPreconnected U)
    (hb : ∀ q∈U, q∉P.boundary) {p : Point} (hp : p∈U) (hpf : p∈P.filled) : closure U⊆P.filled :=
  closure_minimal (region_sub hP hU hb hp hpf) (Jordan.isClosed_filled P)

/-- The exterior version: a preconnected set avoiding the boundary with one point outside the filled
region lies outside it. -/
theorem region_out {P : Polygon} (hP : P.Simple) {U : Set Point} (hU : IsPreconnected U)
    (hb : ∀ q∈U, q∉P.boundary) {p : Point} (hp : p∈U) (hpf : p∉P.filled) : ∀ q∈U, q∉P.filled := by
  have oA := Jordan.isOpen_filled_sdiff_boundary hP
  have oB := Jordan.isOpen_filled_compl P
  have cover : U⊆(P.filled \ P.boundary)∪P.filledᶜ := by
    intro q hq
    by_cases h : q∈P.filled
    · exact Or.inl ⟨h,hb q hq⟩
    · exact Or.inr h
  have disj : Disjoint (P.filled \ P.boundary) P.filledᶜ :=
    Set.disjoint_left.mpr fun q h1 h2 => h2 h1.1
  rcases (isPreconnected_iff_subset_of_disjoint.mp hU) _ _ oA oB cover
      (by rw [Set.disjoint_iff_inter_eq_empty.mp disj]; exact Set.inter_empty U) with h|h
  · exact absurd (h hp).1 hpf
  · exact fun q hq => h hq

/-- A region seeded by interior points near a boundary point: if every interior point within `r`
of the boundary point `b` lies in `U`, then `U` lies in the filled region. -/
theorem seed_in {P : Polygon} (hP : P.Simple) {U : Set Point} (hU : IsPreconnected U)
    (hb : ∀ q∈U, q∉P.boundary) {b : Point} (hbd : b∈P.boundary) {r : ℝ} (hr : 0<r)
    (near : ∀ q : Point, |q.1-b.1|<r → |q.2-b.2|<r → q∈P.filled → q∉P.boundary → q∈U) : U⊆P.filled := by
  have cl := Jordan.boundary_subset_closure_interior hP hbd
  obtain ⟨q,hq,hd⟩ := Metric.mem_closure_iff.mp cl r hr
  have d : max (dist b.1 q.1) (dist b.2 q.2)<r := by rwa [Prod.dist_eq] at hd
  have d1 : |q.1-b.1|<r := by
    rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) d
  have d2 : |q.2-b.2|<r := by
    rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_right _ _) d
  exact region_sub hP hU hb (near q d1 d2 hq.1 hq.2) hq.1

/-- A region seeded by exterior points near a boundary point. -/
theorem seed_out {P : Polygon} (hP : P.Simple) {U : Set Point} (hU : IsPreconnected U)
    (hb : ∀ q∈U, q∉P.boundary) {b : Point} (hbd : b∈P.boundary) {r : ℝ} (hr : 0<r)
    (near : ∀ q : Point, |q.1-b.1|<r → |q.2-b.2|<r → q∉P.filled → q∈U) : ∀ q∈U, q∉P.filled := by
  have cl := Jordan.boundary_subset_closure_compl hP hbd
  obtain ⟨q,hq,hd⟩ := Metric.mem_closure_iff.mp cl r hr
  have d : max (dist b.1 q.1) (dist b.2 q.2)<r := by rwa [Prod.dist_eq] at hd
  have d1 : |q.1-b.1|<r := by
    rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) d
  have d2 : |q.2-b.2|<r := by
    rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_right _ _) d
  exact region_out hP hU hb (near q d1 d2 hq) hq

/-- A point all of whose nearby points off its horizontal line are outside is outside. -/
theorem out_of_rows {P : Polygon} (hP : P.Simple) {z : Point} {r : ℝ} (hr : 0<r)
    (out : ∀ w : Point, |w.1-z.1|<r → |w.2-z.2|<r → w.2≠z.2 → w∉P.filled) : z∉P.filled := by
  have key : ∀ w∈P.filled \ P.boundary, |w.1-z.1|<r/2 → |w.2-z.2|<r/2 → False := by
    intro w hw d1 d2
    have op := Jordan.isOpen_filled_sdiff_boundary hP
    obtain ⟨ε,εp,ball⟩ := Metric.isOpen_iff.mp op w hw
    set δ := min ε (r/2)/2 with hδ
    have δp : 0<δ := by positivity
    have δε : δ<ε := by have := min_le_left ε (r/2); linarith
    have δr : δ<r/2 := by have := min_le_right ε (r/2); linarith
    -- move vertically by ±δ, avoiding the line of z
    have pick : ∃ s : ℝ, (s=δ ∨ s=-δ) ∧ w.2+s≠z.2 := by
      by_cases h : w.2+δ=z.2
      · exact ⟨-δ,Or.inr rfl,by intro h'; linarith⟩
      · exact ⟨δ,Or.inl rfl,h⟩
    obtain ⟨s,hs,ne⟩ := pick
    have sabs : |s|=δ := by rcases hs with rfl|rfl <;> simp [abs_of_pos δp]
    have inb : ((w.1,w.2+s):Point)∈Metric.ball w ε := by
      rw [Metric.mem_ball,Prod.dist_eq]
      simp only [Real.dist_eq,sub_self,abs_zero,add_sub_cancel_left]
      rw [sabs]; exact max_lt εp δε
    have wf := (ball inb).1
    refine out (w.1,w.2+s) (by simpa using d1.trans (by linarith)) ?_ ne wf
    have : |w.2+s-z.2|≤|w.2-z.2|+|s| := by
      calc |w.2+s-z.2|=|(w.2-z.2)+s| := by ring_nf
        _≤|w.2-z.2|+|s| := abs_add_le _ _
    rw [sabs] at this; dsimp only; linarith
  intro zf
  by_cases zb : z∈P.boundary
  · have cl := Jordan.boundary_subset_closure_interior hP zb
    obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp cl (r/2) (by linarith)
    have d : max (dist z.1 w.1) (dist z.2 w.2)<r/2 := by rwa [Prod.dist_eq] at hd
    exact key w hw (by rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) d)
      (by rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_right _ _) d)
  · exact key z ⟨zf,zb⟩ (by simpa using half_pos hr) (by simpa using half_pos hr)

/-- The column version: nearby points off the vertical line of `z` are outside. -/
theorem out_of_cols {P : Polygon} (hP : P.Simple) {z : Point} {r : ℝ} (hr : 0<r)
    (out : ∀ w : Point, |w.1-z.1|<r → |w.2-z.2|<r → w.1≠z.1 → w∉P.filled) : z∉P.filled := by
  have key : ∀ w∈P.filled \ P.boundary, |w.1-z.1|<r/2 → |w.2-z.2|<r/2 → False := by
    intro w hw d1 d2
    have op := Jordan.isOpen_filled_sdiff_boundary hP
    obtain ⟨ε,εp,ball⟩ := Metric.isOpen_iff.mp op w hw
    set δ := min ε (r/2)/2 with hδ
    have δp : 0<δ := by positivity
    have δε : δ<ε := by have := min_le_left ε (r/2); linarith
    have δr : δ<r/2 := by have := min_le_right ε (r/2); linarith
    have pick : ∃ s : ℝ, (s=δ ∨ s=-δ) ∧ w.1+s≠z.1 := by
      by_cases h : w.1+δ=z.1
      · exact ⟨-δ,Or.inr rfl,by intro h'; linarith⟩
      · exact ⟨δ,Or.inl rfl,h⟩
    obtain ⟨s,hs,ne⟩ := pick
    have sabs : |s|=δ := by rcases hs with rfl|rfl <;> simp [abs_of_pos δp]
    have inb : ((w.1+s,w.2):Point)∈Metric.ball w ε := by
      rw [Metric.mem_ball,Prod.dist_eq]
      simp only [Real.dist_eq,sub_self,abs_zero,add_sub_cancel_left]
      rw [sabs]; exact max_lt δε εp
    have wf := (ball inb).1
    refine out (w.1+s,w.2) ?_ (by simpa using d2.trans (by linarith)) ne wf
    have : |w.1+s-z.1|≤|w.1-z.1|+|s| := by
      calc |w.1+s-z.1|=|(w.1-z.1)+s| := by ring_nf
        _≤|w.1-z.1|+|s| := abs_add_le _ _
    rw [sabs] at this; dsimp only; linarith
  intro zf
  by_cases zb : z∈P.boundary
  · have cl := Jordan.boundary_subset_closure_interior hP zb
    obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp cl (r/2) (by linarith)
    have d : max (dist z.1 w.1) (dist z.2 w.2)<r/2 := by rwa [Prod.dist_eq] at hd
    exact key w hw (by rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) d)
      (by rw [abs_sub_comm,← Real.dist_eq]; exact lt_of_le_of_lt (le_max_right _ _) d)
  · exact key z ⟨zf,zb⟩ (by simpa using half_pos hr) (by simpa using half_pos hr)

/-- From a filled point a ray meets the boundary. -/
theorem ray_hits {P : Polygon} {q d : Point} (hd : d≠0) (hq : q∈P.filled) :
    ∃ t : ℝ,0≤t ∧ q+t • d∈P.boundary := by
  by_contra! no
  have outside : q∉P.boundary := by simpa using no 0 (le_refl _)
  exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray P (d:=d) hd
    (by rintro _ ⟨t,ht,rfl⟩; exact no t ht) ((Jordan.mem_filled_iff_bounded P outside).mp hq)

/-- An open box is preconnected and its closure is the closed box. -/
theorem box_preconnected (x₀ x₁ y₀ y₁ : ℝ) : IsPreconnected (Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁) :=
  (convex_Ioo x₀ x₁).prod (convex_Ioo y₀ y₁) |>.isPreconnected

theorem box_closure {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀<x₁) (hy : y₀<y₁) :
    closure (Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁)=Set.Icc x₀ x₁ ×ˢ Set.Icc y₀ y₁ := by
  rw [closure_prod_eq,closure_Ioo hx.ne,closure_Ioo hy.ne]

end ArtGallery.Orthogonal.BoundaryPoint.HubRegion
end
