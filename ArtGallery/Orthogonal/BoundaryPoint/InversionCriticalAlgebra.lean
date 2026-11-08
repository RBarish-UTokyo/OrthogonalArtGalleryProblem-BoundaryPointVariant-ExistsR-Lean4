module

public import ArtGallery.Orthogonal.BoundaryPoint.DerivedAlgebra
public import Mathlib.Tactic.FieldSimp

/-!
# Critical rays of the one-window inversion rooms

The pinned rooms use `E = 100`. The arithmetic statements below also apply to
larger separations. The axis is `X = 0` and the room's critical box is on its
left. The separate geometric certificates identify the visible sides of these
lines and the positions of that box.
-/

@[expose] public section

namespace ArtGallery.Orthogonal.BoundaryPoint.InversionCriticalAlgebra

open ArtGallery.Orthogonal.BoundaryPoint.DerivedAlgebra

noncomputable def revA (E x X : ℝ) : ℝ := 2 * (X + 2*E - x) / (E - x)
noncomputable def revB (E v X : ℝ) : ℝ := 4 * (X + v - 1 / (2*E)) / (v - 1 / E)
noncomputable def upperA (E x X : ℝ) : ℝ := (X + 2*E - x) / (2 * (E - x))
noncomputable def upperB (E y X : ℝ) : ℝ := (y - 1 / (2*E) - X) / (y - 1 / E)

theorem denominators_pos {E x y : ℝ} (hE : 100 ≤ E) (hx : InRange x) (hy : InRange y) :
    0 < E - x ∧ 0 < y - 1 / E := by
  have hp : 0 < E := by linarith
  have hr : 1 / E ≤ (1 / 100 : ℝ) := (div_le_div_iff₀ hp (by linarith)).2 (by linarith)
  constructor <;> linarith [hx.2, hy.1]

theorem rev_axis_difference {E x v : ℝ} (hE : 100 ≤ E) (hx : InRange x) (hv : InRange v) :
    revA E x 0 - revB E v 0 = 2 * (x * v - 1) / ((E - x) * (v - 1 / E)) := by
  obtain ⟨ha,hb⟩ := denominators_pos hE hx hv
  have hn : E ≠ 0 := by linarith
  dsimp [revA,revB]
  rw [div_sub_div _ _ (ne_of_gt ha) (ne_of_gt hb)]
  congr 1
  field_simp [hn]
  ring

theorem upper_axis_difference {E x y : ℝ} (hE : 100 ≤ E) (hx : InRange x) (hy : InRange y) :
    upperA E x 0 - upperB E y 0 = (x * y - 1) / (2 * (E-x) * (y-1/E)) := by
  obtain ⟨ha,hb⟩ := denominators_pos hE hx hy
  have hn : E ≠ 0 := by linarith
  have hd : 2 * (E-x) ≠ 0 := mul_ne_zero (by linarith) (ne_of_gt ha)
  dsimp [upperA,upperB]
  rw [div_sub_div _ _ hd (ne_of_gt hb)]
  congr 1
  field_simp [hn]
  ring

theorem rev_axis_iff {E x v : ℝ} (hE : 100 ≤ E) (hx : InRange x) (hv : InRange v) :
    revB E v 0 ≤ revA E x 0 ↔ 1 ≤ x * v := by
  obtain ⟨ha,hb⟩ := denominators_pos hE hx hv
  rw [← sub_nonneg, rev_axis_difference hE hx hv, le_div_iff₀ (mul_pos ha hb), zero_mul]
  constructor <;> intro h <;> linarith

theorem upper_axis_iff {E x y : ℝ} (hE : 100 ≤ E) (hx : InRange x) (hy : InRange y) :
    upperA E x 0 ≤ upperB E y 0 ↔ x * y ≤ 1 := by
  obtain ⟨ha,hb⟩ := denominators_pos hE hx hy
  have hd : 0 < 2 * (E-x) * (y-1/E) := mul_pos (mul_pos (by linarith) ha) hb
  rw [← sub_nonpos, upper_axis_difference hE hx hy, div_le_iff₀ hd, zero_mul]
  constructor <;> intro h <;> linarith

/-- A's axis height is strictly in the scaled reversed-inversion box. -/
theorem revA_box {E x : ℝ} (hE : 100 ≤ E) (hx : InRange x) :
    4 + 3/(5*E) < revA E x 0 ∧ revA E x 0 < 4 + 5/E := by
  have hp : 0 < E := by linarith
  have hd : 0 < E-x := by linarith [hx.2]
  have heq : revA E x 0 = 4 + 2*x/(E-x) := by
    dsimp [revA]
    rw [add_div_eq_mul_add_div _ _ (ne_of_gt hd)]
    congr 1
    ring
  rw [heq]
  constructor
  · apply add_lt_add_right
    apply (div_lt_div_iff₀ (mul_pos (by linarith) hp) hd).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) hp.le, hx.1]
  · apply add_lt_add_right
    apply (div_lt_div_iff₀ hd hp).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hp.le, hx.2]

/-- B's axis height is strictly in the same scaled reversed-inversion box. -/
theorem revB_box {E v : ℝ} (hE : 100 ≤ E) (hv : InRange v) :
    4 + 3/(5*E) < revB E v 0 ∧ revB E v 0 < 4 + 5/E := by
  have hp : 0 < E := by linarith
  have hr : 1/E ≤ (1/100 : ℝ) := (div_le_div_iff₀ hp (by linarith)).2 (by linarith)
  have hb : 0 < v-1/E := by linarith [hv.1]
  have hn := ne_of_gt hp
  have heq : revB E v 0 = 4 + (2/E)/(v-1/E) := by
    dsimp [revB]
    rw [add_div_eq_mul_add_div _ _ (ne_of_gt hb)]
    congr 1
    field_simp [hn]
    ring
  rw [heq]
  constructor
  · apply add_lt_add_right
    apply (div_lt_div_iff₀ (mul_pos (by linarith) hp) hb).2
    have hcancel : (2/E)*(5*E) = 10 := by field_simp [hn]; ring
    rw [hcancel]
    linarith [hv.2, one_div_pos.mpr hp]
  · apply add_lt_add_right
    apply (div_lt_div_iff₀ hb hp).2
    rw [div_mul_cancel₀ _ hn]
    linarith [hv.1]

/-- A's height is strictly between the upper-inversion box bounds. -/
theorem upperA_box {E x : ℝ} (hE : 100 ≤ E) (hx : InRange x) :
    1 < upperA E x 0 ∧ upperA E x 0 < 1+2/E := by
  have hp : 0 < E := by linarith
  have hd : 0 < 2*(E-x) := by linarith [hx.2]
  have heq : upperA E x 0 = 1 + x/(2*(E-x)) := by
    dsimp [upperA]
    rw [add_div_eq_mul_add_div _ _ (ne_of_gt hd)]
    congr 1
    ring
  rw [heq]
  constructor
  · linarith [div_pos (positive_of_inRange hx) hd]
  · apply add_lt_add_right
    apply (div_lt_div_iff₀ hd hp).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hp.le, hx.2]

/-- B's height is strictly between the upper-inversion box bounds. -/
theorem upperB_box {E y : ℝ} (hE : 100 ≤ E) (hy : InRange y) :
    1 < upperB E y 0 ∧ upperB E y 0 < 1+2/E := by
  have hp : 0 < E := by linarith
  have hn := ne_of_gt hp
  have hr : 1/E ≤ (1/100 : ℝ) := (div_le_div_iff₀ hp (by linarith)).2 (by linarith)
  have hb : 0 < y-1/E := by linarith [hy.1]
  have heq : upperB E y 0 = 1 + (1/(2*E))/(y-1/E) := by
    dsimp [upperB]
    rw [add_div_eq_mul_add_div _ _ (ne_of_gt hb)]
    congr 1
    field_simp [hn]
    ring
  rw [heq]
  constructor
  · linarith [div_pos (one_div_pos.mpr (mul_pos (by linarith : (0:ℝ)<2) hp)) hb]
  · apply add_lt_add_right
    apply (div_lt_div_iff₀ hb hp).2
    have hcancel : (1/(2*E))*E = (1/2 : ℝ) := by field_simp [hn]
    rw [hcancel]
    linarith [hy.1]

theorem rev_left_overlap {E x v X : ℝ} (hE : 100 ≤ E) (hx : InRange x) (hv : InRange v)
    (hX : X ≤ 0) (hs : 1 ≤ x * v) : revB E v X ≤ revA E x X := by
  obtain ⟨ha,hb⟩ := denominators_pos hE hx hv
  have hpos : 0 < 1 / E := one_div_pos.mpr (by linarith)
  have hsl : 2/(E-x) ≤ 4/(v-1/E) := by
    apply (div_le_div_iff₀ ha hb).2
    linarith [hx.2, hv.2]
  have hm := mul_le_mul_of_nonpos_right hsl hX
  have h0 := (rev_axis_iff hE hx hv).2 hs
  calc
    revB E v X = revB E v 0 + (4/(v-1/E))*X := by dsimp [revB]; ring
    _ ≤ revA E x 0 + (2/(E-x))*X := add_le_add h0 hm
    _ = revA E x X := by dsimp [revA]; ring

theorem upper_left_overlap {E x y X : ℝ} (hE : 100 ≤ E) (hx : InRange x) (hy : InRange y)
    (hX : X ≤ 0) (hs : x*y ≤ 1) : upperA E x X ≤ upperB E y X := by
  obtain ⟨ha,hb⟩ := denominators_pos hE hx hy
  have h0 := (upper_axis_iff hE hx hy).2 hs
  have hA : upperA E x X ≤ upperA E x 0 := by
    dsimp [upperA]
    apply div_le_div_of_nonneg_right _ (mul_nonneg (by linarith) ha.le)
    linarith
  have hB : upperB E y 0 ≤ upperB E y X := by
    dsimp [upperB]
    apply div_le_div_of_nonneg_right _ hb.le
    linarith
  exact le_trans hA (le_trans h0 hB)

end ArtGallery.Orthogonal.BoundaryPoint.InversionCriticalAlgebra

end
