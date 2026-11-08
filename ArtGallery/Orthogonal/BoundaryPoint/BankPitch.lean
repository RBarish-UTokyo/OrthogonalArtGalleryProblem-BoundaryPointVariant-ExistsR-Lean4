module

public import ArtGallery.Orthogonal.BoundaryPoint.DoorSeparation

/-!
# Uniform margins for the generated slot banks

The abscissa of the base of a slot is W + k (bank - 1/5) + rank * pitch.
These estimates are independent of the input size and of the within-bank
ranks. The copy-axis estimate uses the normalized receiver horizontal offset.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.BankPitch

def scale (n : ℝ) := 50 * n^2
def depth (n : ℝ) := 50050 * n^2
def pitch (n : ℝ) := 125 * n
noncomputable def width (n : ℝ) := 1 / (320*n)
noncomputable def slot (n bank rank : ℝ) := width n + scale n * (bank - 1/5) + rank * pitch n

theorem same_bank {n b i j : ℝ} (hn : 1 ≤ n) (hi : i+1 ≤ j) :
    slot n b i + pitch n ≤ slot n b j := by
  have h := mul_le_mul_of_nonneg_right hi (show 0 ≤ pitch n by unfold pitch; linarith)
  unfold slot
  linarith

theorem different_banks {n a b i j : ℝ} (hn : 1 ≤ n) (hab : a+9 ≤ b)
    (hi : i ≤ n) (hj : 0 ≤ j) : slot n a i + pitch n ≤ slot n b j := by
  have h₁ := mul_le_mul_of_nonneg_left hab (show 0 ≤ scale n by unfold scale; positivity)
  have h₂ := mul_le_mul_of_nonneg_right hi (show 0 ≤ pitch n by unfold pitch; linarith)
  have h₃ := mul_nonneg hj (show 0 ≤ pitch n by unfold pitch; linarith)
  unfold slot scale pitch at *
  nlinarith [mul_nonneg (show 0 ≤ n-1 by linarith) (show 0 ≤ n by linarith)]

theorem width_le_half {n : ℝ} (hn : 1 ≤ n) : width n ≤ 1/2 := by
  unfold width
  apply (div_le_iff₀ (show 0 < 320*n by linarith)).2
  linarith

/-- For the umbra axis, h is Y-1 and base is the normalized slot abscissa.
The horizontal separation of the window and door is 301/2-W. -/
theorem height_of_axis {n h receiver base : ℝ} (hn : 1 ≤ n)
    (hr : receiver ≤ 110) (hb : 0 ≤ base) (hs : 0 < receiver-base)
    (he : h*(receiver-base) = 301/2-width n) : 4/3 < h := by
  have hw := width_le_half hn
  have hpos : 0 < h := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hs.le
    linarith
  have bound := mul_le_mul_of_nonneg_left (show receiver-base ≤ 110 by linarith) hpos.le
  linarith

/-- At the umbra axis or any higher locus, the projected separation beats
the full closed door width, including the two variable slot offsets. -/
theorem projected_margin {n h : ℝ} (hn : 1 ≤ n) (hh : 4/3 ≤ h) :
    width n * (depth n + h) < (pitch n - 3/2)*h := by
  have hnsq : n ≤ n^2 := by nlinarith [mul_nonneg (show 0 ≤ n-1 by linarith) (show 0 ≤ n by linarith)]
  have hcoef : 0 ≤ 40000*n^2-480*n-1 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hh hcoef
  unfold width depth pitch
  rw [one_div_mul_eq_div, div_lt_iff₀ (show 0 < 320*n by linarith)]
  nlinarith

/-- At the emitted door offset the normalized horizontal rate of any
base is below two, even at bank 1000, the last rank, and the last door. -/
theorem base_rate_bound {n bank rank row : ℝ} (hn : 1 ≤ n)
    (hbank : 1 ≤ bank ∧ bank ≤ 1000) (hrank : 0 ≤ rank ∧ rank ≤ n)
    (hrow : 0 ≤ row ∧ row ≤ n) :
    0 ≤ (slot n bank rank + 2000*row - width n) / depth n ∧
    (slot n bank rank + 2000*row - width n) / depth n ≤ 2 := by
  have hd : 0 < depth n := by unfold depth; positivity
  have hk : 0 ≤ scale n := by unfold scale; positivity
  have hp : 0 ≤ pitch n := by unfold pitch; linarith
  have hlow := mul_nonneg hk (show 0 ≤ bank - 1/5 by linarith [hbank.1])
  have hlow' := mul_nonneg hrank.1 hp
  have hhi := mul_le_mul_of_nonneg_left (show bank - 1/5 ≤ 1000 by linarith [hbank.2]) hk
  have hhi' := mul_le_mul_of_nonneg_right hrank.2 hp
  constructor
  · apply div_nonneg _ hd.le
    unfold slot
    linarith [hrow.1]
  · rw [div_le_iff₀ hd]
    unfold slot scale pitch depth at *
    nlinarith [hrow.2, mul_nonneg (show 0 ≤ n by linarith) (show 0 ≤ n-1 by linarith)]

/-- The three addition and two inversion port formulas have a main term
in [19,109] and a bounded slot-offset correction divided by D. -/
theorem receiver_rate_bound {n main correction : ℝ} (hn : 1 ≤ n)
    (hm : 19 ≤ main ∧ main ≤ 109) (hc : -3 ≤ correction ∧ correction ≤ 2) :
    18 ≤ main + correction / depth n ∧ main + correction / depth n ≤ 110 := by
  have hd : 3 ≤ depth n := by
    unfold depth
    nlinarith [mul_nonneg (show 0 ≤ n-1 by linarith) (show 0 ≤ n by linarith)]
  have hd' : 0 < depth n := by linarith
  have hl : -1 ≤ correction / depth n := (le_div_iff₀ hd').2 (by linarith [hc.1])
  have hu : correction / depth n ≤ 1 := (div_le_iff₀ hd').2 (by linarith [hc.2])
  constructor <;> linarith [hm.1,hm.2]

/-- Equality of the two binding ray intercepts on the umbra axis gives a
uniform margin there and at every higher nook locus. -/
theorem margin_from_rays {n base receiver h y : ℝ} (hn : 1 ≤ n)
    (hb : 0 ≤ base ∧ base ≤ 2) (hr : 18 ≤ receiver ∧ receiver ≤ 110)
    (he : width n - base*h = 301/2 - receiver*h) (hy : h ≤ y) :
    width n * (depth n + y) < (pitch n - 3/2)*y := by
  apply projected_margin hn
  have hh := height_of_axis hn hr.2 hb.1 (show 0 < receiver-base by linarith [hr.1,hb.2])
    (show h * (receiver-base) = 301/2-width n by nlinarith only [he])
  exact (hh.le.trans hy)

end ArtGallery.Orthogonal.BoundaryPoint.BankPitch
end
