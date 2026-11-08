module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Algebra of the proposed orthogonal boundary-point derived gadgets

These results concern real inequalities only. They do not assert that any
polygon realizes the predicates, that pins work, or that a reduction exists.
The interval is `[1/2, 2]`. The primitive relations are the two one-window
inversion inequalities, a lower complement inequality, and shifted addition.
-/

@[expose] public section

namespace ArtGallery.Orthogonal.BoundaryPoint.DerivedAlgebra

/-- The permitted value interval. -/
def InRange (x : ℝ) : Prop := 1 / 2 ≤ x ∧ x ≤ 2

/-- The arithmetic complement preserving the value interval. -/
noncomputable def complement (x : ℝ) : ℝ := 5 / 2 - x

/-- The reversed inversion inequality supplied by one proposed room. -/
def InvRevGe (x y : ℝ) : Prop := 1 ≤ x * (5 / 2 - y)

/-- The inversion upper inequality supplied by the other proposed room. -/
def InvLe (x y : ℝ) : Prop := x * y ≤ 1

/-- The lower complement relation, required as a separate primitive. -/
def LowerComplement (x y : ℝ) : Prop := 5 / 2 ≤ x + y

/-- Upper complement obtained existentially from the two inversion relations. -/
def UpperComplement (x y : ℝ) : Prop :=
  ∃ m : ℝ, InRange m ∧ InvRevGe m x ∧ InvLe m y

/-- Both directions of the complement relation. -/
def Complement (x y : ℝ) : Prop := LowerComplement x y ∧ UpperComplement x y

/-- Shifted addition lower inequality. Its constant shift is essential. -/
def ShiftedAddGe (x y z : ℝ) : Prop := z + 5 / 2 ≤ x + y

theorem positive_of_inRange {x : ℝ} (hx : InRange x) : 0 < x := by
  rcases hx with ⟨hlo, hhi⟩
  linarith

theorem reciprocal_inRange {x : ℝ} (hx : InRange x) : InRange (1 / x) := by
  have hp := positive_of_inRange hx
  rcases hx with ⟨hlo, hhi⟩
  constructor
  · apply (le_div_iff₀ hp).2
    linarith
  · apply (div_le_iff₀ hp).2
    linarith

theorem complement_inRange {x : ℝ} (hx : InRange x) : InRange (complement x) := by
  dsimp [InRange, complement] at *
  constructor <;> linarith

theorem complement_complement (x : ℝ) : complement (complement x) = x := by
  dsimp [complement]
  ring

/-- The upper-complement construction, with its auxiliary value explicitly bounded. -/
theorem upperComplement_iff {x y : ℝ} (hy : InRange y) :
    UpperComplement x y ↔ x + y ≤ 5 / 2 := by
  constructor
  · rintro ⟨m, hm, hr, hl⟩
    have hp := positive_of_inRange hm
    have hmul : m * y ≤ m * (5 / 2 - x) := le_trans hl hr
    have hxy := le_of_mul_le_mul_left hmul hp
    linarith
  · intro hxy
    have hp := positive_of_inRange hy
    have hrec : (1 / y) * y = 1 := one_div_mul_cancel (ne_of_gt hp)
    refine ⟨1 / y, reciprocal_inRange hy, ?_, ?_⟩
    · dsimp [InvRevGe]
      have hdiff : y ≤ 5 / 2 - x := by linarith
      have hmul := mul_le_mul_of_nonneg_left hdiff (le_of_lt (one_div_pos.mpr hp))
      linarith
    · dsimp [InvLe]
      exact le_of_eq hrec

/-- Lower and upper complement together force exactly the arithmetic complement. -/
theorem complement_iff {x y : ℝ} (hy : InRange y) :
    Complement x y ↔ y = complement x := by
  rw [Complement, upperComplement_iff hy]
  dsimp [LowerComplement, complement]
  constructor
  · intro h
    linarith [h.1, h.2]
  · intro h
    constructor <;> linarith

theorem complement_self {x : ℝ} (hx : InRange x) : Complement x (complement x) :=
  (complement_iff (complement_inRange hx)).2 rfl

/-- Complementing all three variables converts shifted addition to ordinary addLe. -/
theorem shiftedAddGe_complements_iff (x y z : ℝ) :
    ShiftedAddGe (complement x) (complement y) (complement z) ↔ x + y ≤ z := by
  dsimp [ShiftedAddGe, complement]
  constructor <;> intro h <;> linarith

/-- The same conversion with explicit existential complement gadgets. -/
theorem derived_addLe_iff {x y z : ℝ} (hx : InRange x) (hy : InRange y) (hz : InRange z) :
    (∃ x' y' z' : ℝ, InRange x' ∧ InRange y' ∧ InRange z' ∧
      Complement x x' ∧ Complement y y' ∧ Complement z z' ∧ ShiftedAddGe x' y' z') ↔
      x + y ≤ z := by
  constructor
  · rintro ⟨x', y', z', hx', hy', hz', hcx, hcy, hcz, hs⟩
    have ex := (complement_iff hx').mp hcx
    have ey := (complement_iff hy').mp hcy
    have ez := (complement_iff hz').mp hcz
    rw [ex, ey, ez] at hs
    exact (shiftedAddGe_complements_iff x y z).mp hs
  · intro h
    exact ⟨complement x, complement y, complement z, complement_inRange hx,
      complement_inRange hy, complement_inRange hz, complement_self hx,
      complement_self hy, complement_self hz, (shiftedAddGe_complements_iff x y z).mpr h⟩

/-- Complementing the second input of reversed inversion gives ordinary invGe. -/
theorem invRevGe_complement_iff (x y : ℝ) : InvRevGe x (complement y) ↔ 1 ≤ x * y := by
  have e : 5 / 2 - complement y = y := by dsimp [complement]; ring
  simp only [InvRevGe, e]

/-- Complementing the second input of invLe gives reversed invLe. -/
theorem invLe_complement_iff (x y : ℝ) :
    InvLe x (complement y) ↔ x * (5 / 2 - y) ≤ 1 := Iff.rfl

theorem derived_invGe_iff {x y : ℝ} (hy : InRange y) :
    (∃ y' : ℝ, InRange y' ∧ Complement y y' ∧ InvRevGe x y') ↔ 1 ≤ x * y := by
  constructor
  · rintro ⟨y', hy', hc, hr⟩
    rw [(complement_iff hy').mp hc] at hr
    exact (invRevGe_complement_iff x y).mp hr
  · intro h
    exact ⟨complement y, complement_inRange hy, complement_self hy,
      (invRevGe_complement_iff x y).mpr h⟩

theorem derived_invRevLe_iff {x y : ℝ} (hy : InRange y) :
    (∃ y' : ℝ, InRange y' ∧ Complement y y' ∧ InvLe x y') ↔
      x * (5 / 2 - y) ≤ 1 := by
  constructor
  · rintro ⟨y', hy', hc, hr⟩
    rw [(complement_iff hy').mp hc] at hr
    exact (invLe_complement_iff x y).mp hr
  · intro h
    exact ⟨complement y, complement_inRange hy, complement_self hy,
      (invLe_complement_iff x y).mpr h⟩

/-- Two inputs with a common complement are equal. -/
theorem derived_equality_iff {x y : ℝ} (hx : InRange x) :
    (∃ u : ℝ, InRange u ∧ Complement x u ∧ Complement y u) ↔ x = y := by
  constructor
  · rintro ⟨u, hu, hxu, hyu⟩
    have ex := (complement_iff hu).mp hxu
    have ey := (complement_iff hu).mp hyu
    dsimp [complement] at ex ey
    linarith
  · intro h
    subst y
    exact ⟨complement x, complement_inRange hx, complement_self hx, complement_self hx⟩

/-- Comparing an input with the complement of the other input. -/
theorem derived_comparisonLe_iff {x y : ℝ} (hy : InRange y) :
    (∃ u : ℝ, InRange u ∧ Complement y u ∧ UpperComplement x u) ↔ x ≤ y := by
  constructor
  · rintro ⟨u, hu, hcu, hxu⟩
    have eu := (complement_iff hu).mp hcu
    have hsum := (upperComplement_iff hu).mp hxu
    dsimp [complement] at eu
    linarith
  · intro h
    refine ⟨complement y, complement_inRange hy, complement_self hy, ?_⟩
    apply (upperComplement_iff (complement_inRange hy)).mpr
    dsimp [complement]
    linarith

end ArtGallery.Orthogonal.BoundaryPoint.DerivedAlgebra

end
