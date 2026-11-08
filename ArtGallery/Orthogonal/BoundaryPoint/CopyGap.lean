module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import ArtGallery.Spec
public import ArtGallery.Geometry.Det

/-! # A strict gap between two sight lines near an axis

Two lines cross a horizontal axis at abscissae `αl < αh`. At every small offset
from the axis they still leave an open interval between them, and that interval
stays inside any open interval containing both axis abscissae. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyGap

theorem gap_point {αl αh βl βh ε x₀ x₁ : ℝ} (hα : αl<αh) (hε : 0<ε) (h₀ : x₀<αl) (h₁ : αh<x₁) :
    ∃ τ x : ℝ, 0<τ ∧ τ<ε ∧ x₀<x ∧ x<x₁ ∧ αl+βl*τ<x ∧ x<αh+βh*τ := by
  set L := |βl|+|βh|+1 with hL
  have Lpos : 0<L := by positivity
  set τ := min (ε/2) (min ((αh-αl)/(2*L)) (min ((αl-x₀)/(2*L)) ((x₁-αh)/(2*L)))) with hτ
  have p1 : 0<(αh-αl)/(2*L) := div_pos (by linarith) (by positivity)
  have p2 : 0<(αl-x₀)/(2*L) := div_pos (by linarith) (by positivity)
  have p3 : 0<(x₁-αh)/(2*L) := div_pos (by linarith) (by positivity)
  have τpos : 0<τ := by
    simp only [hτ]; exact lt_min (by linarith) (lt_min p1 (lt_min p2 p3))
  have τε : τ<ε := by
    have := min_le_left (ε/2) (min ((αh-αl)/(2*L)) (min ((αl-x₀)/(2*L)) ((x₁-αh)/(2*L)))); linarith
  have b1 : τ≤(αh-αl)/(2*L) := (min_le_right _ _).trans (min_le_left _ _)
  have b2 : τ≤(αl-x₀)/(2*L) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have b3 : τ≤(x₁-αh)/(2*L) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have m1 : 2*L*τ≤αh-αl := by rw [le_div_iff₀ (by positivity)] at b1; linarith
  have m2 : 2*L*τ≤αl-x₀ := by rw [le_div_iff₀ (by positivity)] at b2; linarith
  have m3 : 2*L*τ≤x₁-αh := by rw [le_div_iff₀ (by positivity)] at b3; linarith
  have al : |βl*τ|≤|βl| * τ := by rw [abs_mul,abs_of_pos τpos]
  have ah : |βh*τ|≤|βh| * τ := by rw [abs_mul,abs_of_pos τpos]
  have l1 := neg_abs_le (βl*τ)
  have l2 := le_abs_self (βl*τ)
  have l3 := neg_abs_le (βh*τ)
  have l4 := le_abs_self (βh*τ)
  have sum : (|βl|+|βh|)*τ<L*τ := by nlinarith
  have half : L*τ≤2*L*τ := by nlinarith
  refine ⟨τ,(αl+βl*τ+(αh+βh*τ))/2,τpos,τε,?_,?_,?_,?_⟩ <;> nlinarith

/-- Two guards cover a thin open box next to an axis, one only to the left of its sight
line and one only to the right of its own, and no other guard sees a point of the box
strictly between the two lines. Then the two lines do not leave a gap on the axis. The box lies above the axis if `up`, below otherwise. -/
theorem no_gap {P : Polygon} {G : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈G, P.Sees g z)
    {p q : Point} {a ε xa xb αp βp αq βq : ℝ} (up : Bool) (hε : 0<ε)
    (inside : ∀ x y : ℝ, xa<x → x<xb → (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) → (x,y)∈P.filled)
    (hp : ∀ x y : ℝ, xa<x → x<xb → (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) →
      αp+βp*(y-a)<x → ¬P.Sees p (x,y))
    (hq : ∀ x y : ℝ, xa<x → x<xb → (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) →
      x<αq+βq*(y-a) → ¬P.Sees q (x,y))
    (others : ∀ g∈G, g≠p → g≠q → ∀ x y : ℝ, xa<x → x<xb → (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) →
      αp+βp*(y-a)<x → x<αq+βq*(y-a) → ¬P.Sees g (x,y))
    (ha : xa<αp) (hb : αq<xb) : αq≤αp := by
  by_contra! gap
  have σ : ∃ σ : ℝ, (σ=1 ∨ σ=-1) ∧ (up=true → σ=1) ∧ (up=false → σ=-1) := by
    cases up
    · exact ⟨-1,Or.inr rfl,fun e => by simp at e,fun _ => rfl⟩
    · exact ⟨1,Or.inl rfl,fun _ => rfl,fun e => by simp at e⟩
  obtain ⟨σ,hσ,su,sd⟩ := σ
  obtain ⟨τ,x,τ0,τε,x0,x1,lo,hi⟩ := gap_point (βl:=βp*σ) (βh:=βq*σ) gap hε ha hb
  let y := a+σ*τ
  have yr : (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) := by
    cases up
    · have e := sd rfl
      simp only [Bool.false_eq_true,ite_false,y,e]; constructor <;> linarith
    · have e := su rfl
      simp only [ite_true,y,e]; constructor <;> linarith
  have ey : y-a=σ*τ := by simp only [y]; ring
  obtain ⟨g,hg,sees⟩ := cover (x,y) (inside x y x0 x1 yr)
  by_cases e1 : g=p
  · subst e1; exact hp x y x0 x1 yr (by rw [ey]; linarith) sees
  by_cases e2 : g=q
  · subst e2; exact hq x y x0 x1 yr (by rw [ey]; linarith) sees
  exact others g hg e1 e2 x y x0 x1 yr (by rw [ey]; linarith) (by rw [ey]; linarith) sees

/-- Three lines crossing an axis in strict order keep that order at a point close below or
above the axis, inside any open interval containing the outer crossings. -/
theorem mid_point {αl αm αh βl βm βh ε x₀ x₁ : ℝ} (hl : αl<αm) (hh : αm<αh) (hε : 0<ε)
    (h₀ : x₀<αl) (h₁ : αh<x₁) :
    ∃ τ : ℝ, 0<τ ∧ τ<ε ∧ x₀<αm+βm*τ ∧ αm+βm*τ<x₁ ∧ αl+βl*τ<αm+βm*τ ∧ αm+βm*τ<αh+βh*τ := by
  set L := |βl|+|βm|+|βh|+1 with hL
  have Lpos : 0<L := by positivity
  set δ := min (αm-αl) (min (αh-αm) (min (αl-x₀) (x₁-αh))) with hδ
  have δpos : 0<δ := lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  set τ := min (ε/2) (δ/(4*L)) with hτ
  have τpos : 0<τ := lt_min (by linarith) (div_pos δpos (by positivity))
  have τε : τ<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have τδ : 4*L*τ≤δ := by
    have := min_le_right (ε/2) (δ/(4*L)); rw [le_div_iff₀ (by positivity)] at this; linarith
  have d1 : δ≤αm-αl := min_le_left _ _
  have d2 : δ≤αh-αm := (min_le_right _ _).trans (min_le_left _ _)
  have d3 : δ≤αl-x₀ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have d4 : δ≤x₁-αh := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have bl : |βl*τ|≤L*τ := by rw [abs_mul,abs_of_pos τpos]; nlinarith [abs_nonneg βm,abs_nonneg βh,abs_nonneg βl]
  have bm : |βm*τ|≤L*τ := by rw [abs_mul,abs_of_pos τpos]; nlinarith [abs_nonneg βm,abs_nonneg βh,abs_nonneg βl]
  have bh : |βh*τ|≤L*τ := by rw [abs_mul,abs_of_pos τpos]; nlinarith [abs_nonneg βm,abs_nonneg βh,abs_nonneg βl]
  have Lτ : 0<L*τ := mul_pos Lpos τpos
  refine ⟨τ,τpos,τε,?_,?_,?_,?_⟩
  · linarith [neg_abs_le (βm*τ)]
  · linarith [le_abs_self (βm*τ)]
  · linarith [le_abs_self (βl*τ),neg_abs_le (βm*τ)]
  · linarith [le_abs_self (βm*τ),neg_abs_le (βh*τ)]

/-- The gap argument with the witness point on a prescribed middle line: other guards need
only be excluded on that line. -/
theorem no_gap_mid {P : Polygon} {G : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈G, P.Sees g z)
    {p q : Point} {a ε xa xb αp βp αq βq : ℝ} (up : Bool) (hε : 0<ε)
    (inside : ∀ x y : ℝ, xa<x → x<xb → (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) → (x,y)∈P.filled)
    (hp : ∀ x y : ℝ, xa<x → x<xb → (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) →
      αp+βp*(y-a)<x → ¬P.Sees p (x,y))
    (hq : ∀ x y : ℝ, xa<x → x<xb → (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) →
      x<αq+βq*(y-a) → ¬P.Sees q (x,y))
    (mid : αp<αq → ∃ αm βm : ℝ, αp<αm ∧ αm<αq ∧ ∀ g∈G, g≠p → g≠q → ∀ y : ℝ, xa<αm+βm*(y-a) → αm+βm*(y-a)<xb →
      (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) → ¬P.Sees g (αm+βm*(y-a),y))
    (ha : xa<αp) (hb : αq<xb) : αq≤αp := by
  by_contra! gap
  obtain ⟨αm,βm,lo,hi,others⟩ := mid gap
  have σ : ∃ σ : ℝ, (σ=1 ∨ σ=-1) ∧ (up=true → σ=1) ∧ (up=false → σ=-1) := by
    cases up
    · exact ⟨-1,Or.inr rfl,fun e => by simp at e,fun _ => rfl⟩
    · exact ⟨1,Or.inl rfl,fun _ => rfl,fun e => by simp at e⟩
  obtain ⟨σ,hσ,su,sd⟩ := σ
  obtain ⟨τ,τ0,τε,x0,x1,l1,l2⟩ := mid_point (βl:=βp*σ) (βm:=βm*σ) (βh:=βq*σ) lo hi hε ha hb
  let y := a+σ*τ
  have yr : (if up then a<y ∧ y<a+ε else a-ε<y ∧ y<a) := by
    cases up
    · have e := sd rfl
      simp only [Bool.false_eq_true,ite_false,y,e]; constructor <;> linarith
    · have e := su rfl
      simp only [ite_true,y,e]; constructor <;> linarith
  have ey : y-a=σ*τ := by simp only [y]; ring
  have em : αm+βm*(y-a)=αm+βm*σ*τ := by rw [ey]; ring
  obtain ⟨g,hg,sees⟩ := cover (αm+βm*(y-a),y) (inside _ y (by rw [em]; exact x0) (by rw [em]; exact x1) yr)
  by_cases e1 : g=p
  · subst e1; exact hp _ y (by rw [em]; exact x0) (by rw [em]; exact x1) yr (by rw [em,ey]; linarith) sees
  by_cases e2 : g=q
  · subst e2; exact hq _ y (by rw [em]; exact x0) (by rw [em]; exact x1) yr (by rw [em,ey]; linarith) sees
  exact others g hg e1 e2 y (by rw [em]; exact x0) (by rw [em]; exact x1) yr sees

end ArtGallery.Orthogonal.BoundaryPoint.CopyGap
end
