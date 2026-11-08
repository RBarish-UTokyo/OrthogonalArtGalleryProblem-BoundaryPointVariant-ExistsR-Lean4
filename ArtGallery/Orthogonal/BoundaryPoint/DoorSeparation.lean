module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Door separation for a shared hub

A line joining a base at height `-S` to a target at height `Y` crosses
the interface at height `H`. Only the horizontal coordinate varies with
the base slot. The bounds here include variation within both closed slots.
-/

@[expose] public section

namespace ArtGallery.Orthogonal.BoundaryPoint.DoorSeparation

def crossingX (alpha base target : ℝ) : ℝ :=
  alpha * base + (1 - alpha) * target

theorem crossing_height {S Y H : ℝ} (h : 0 < S + Y) :
    (Y - H) / (S + Y) * (-S) + (1 - (Y - H) / (S + Y)) * Y = H := by
  field_simp [ne_of_gt h]
  ring

theorem crossing_shift (alpha x z target : ℝ) :
    crossingX alpha z target - crossingX alpha x target = alpha * (z - x) := by
  unfold crossingX
  ring

theorem sufficient_pitch {S Y H pitch length width : ℝ}
    (h : 0 < S + Y) (hp : width * (S + Y) < (pitch - length) * (Y - H)) :
    width < (Y - H) / (S + Y) * (pitch - length) := by
  rw [div_mul_eq_mul_div, lt_div_iff₀ h]
  simpa only [mul_comm (Y - H)] using hp

/-- The target has a matched ray through the door. A second base interval
starting at least one pitch to the right misses its closed right edge. -/
theorem misses_right {alpha pitch length width P Q t u target door : ℝ}
    (ha : 0 ≤ alpha) (hp : width < alpha * (pitch - length))
    (hQ : P + pitch ≤ Q) (ht : t ≤ length) (hu : 0 ≤ u)
    (hmatch : door ≤ crossingX alpha (P + t) target) :
    door + width < crossingX alpha (Q + u) target := by
  have h := mul_le_mul_of_nonneg_left (show pitch - length ≤ Q + u - (P + t) by linarith) ha
  rw [← crossing_shift alpha (P + t) (Q + u) target] at h
  linarith

/-- The symmetric exclusion uses the right endpoint of the matched door. -/
theorem misses_left {alpha pitch length width P Q t u target door : ℝ}
    (ha : 0 ≤ alpha) (hp : width < alpha * (pitch - length))
    (hQ : Q + pitch ≤ P) (ht : 0 ≤ t) (hu : u ≤ length)
    (hmatch : crossingX alpha (P + t) target ≤ door + width) :
    crossingX alpha (Q + u) target < door := by
  have h := mul_le_mul_of_nonneg_left (show pitch - length ≤ P + t - (Q + u) by linarith) ha
  rw [← crossing_shift alpha (Q + u) (P + t) target] at h
  linarith

/-- A nonhorizontal segment has at most one parameter on the interface. -/
theorem unique_interface_parameter {a b s t : ℝ} (hab : b ≠ a)
    (h : (1-s)*a + s*b = (1-t)*a + t*b) : s = t := by
  have hprod : (s-t)*(b-a) = 0 := by nlinarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hab))

end ArtGallery.Orthogonal.BoundaryPoint.DoorSeparation

end
