module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterProduct
public import Mathlib.Data.Nat.Pairing

/-! # Products of register forms as forms over product atoms

A product of two register forms is a form whose atoms are unordered pairs of
registers. Its value at a pair is the product of the two register values, and
its box is the product box (the square box for a repeated register). Equal
monomials of the two products in a determinant cancel exactly, so a single
interval bound of the expanded difference is much sharper than separate bounds
of the two products. Soundness reuses `RegisterForm.positive_value`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterPoly
open RegisterForm MarginCert

/-- The product atom of the registers `i` and `j`. -/
def key (i j : Nat) : Nat := Nat.pair (min i j) (max i j)

/-- Values of product atoms. -/
def A2 (A : Nat → ℚ) (k : Nat) : ℚ := A (Nat.unpair k).1 * A (Nat.unpair k).2

def sqBox (b : Box) : Box :=
  ⟨if b.lo≤0 ∧ 0≤b.hi then 0 else min (b.lo*b.lo) (b.hi*b.hi),max (b.lo*b.lo) (b.hi*b.hi)⟩

/-- Boxes of product atoms. -/
def B2 (B : Nat → Box) (k : Nat) : Box :=
  if (Nat.unpair k).1=(Nat.unpair k).2 then sqBox (B (Nat.unpair k).1)
  else RegisterProduct.productBox (B (Nat.unpair k).1) (B (Nat.unpair k).2)

theorem key_value (A : Nat → ℚ) (i j : Nat) : A2 A (key i j)=A i*A j := by
  unfold A2 key
  rw [Nat.unpair_pair]
  rcases le_total i j with h|h
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right h,max_eq_left h,mul_comm]

private theorem square_bound {l h a : ℚ} (hl : l≤a) (hh : a≤h) :
    (sqBox ⟨l,h⟩).lo≤a*a ∧ a*a≤(sqBox ⟨l,h⟩).hi := by
  simp only [sqBox]
  constructor
  · split
    · exact mul_self_nonneg a
    · next hz =>
      rcases le_or_gt 0 l with pl|nl
      · exact (min_le_left ..).trans (mul_le_mul hl hl pl (pl.trans hl))
      · have nh : h<0 := by
          by_contra c; exact hz ⟨nl.le,le_of_not_gt c⟩
        have ha : a≤0 := hh.trans nh.le
        exact (min_le_right ..).trans (by nlinarith)
  · rcases le_total 0 a with pa|na
    · exact (mul_le_mul hh hh pa (pa.trans hh)).trans (le_max_right ..)
    · exact (by nlinarith : a*a≤l*l).trans (le_max_left ..)

theorem bounds2 {B : Nat → Box} {A : Nat → ℚ} (h : Bounds B A) : Bounds (B2 B) (A2 A) := by
  intro k
  unfold B2 A2
  split
  · next e =>
    rw [←e]
    have b := h (Nat.unpair k).1
    exact square_bound (l:=(B (Nat.unpair k).1).lo) (h:=(B (Nat.unpair k).1).hi) b.1 b.2
  · exact RegisterProduct.product_bound (h _) (h _)

/-- The product of one term with a form. -/
def mulTerm (t : Term) (b : Form) : Form :=
  b.foldr (fun u acc => insert (t.1.1+u.1.1,key t.1.2 u.1.2) (t.2*u.2) acc) []

/-- The expanded product of two forms over product atoms. -/
def mul (a b : Form) : Form := a.foldr (fun t acc => plus (mulTerm t b) acc) []

theorem mulTerm_value (s : ℚ) (A : Nat → ℚ) (t : Term) (b : Form) :
    value s (A2 A) (mulTerm t b)=valTerm s A t*value s A b := by
  induction b with
  | nil => simp [mulTerm,value]
  | cons u b ih =>
    simp only [mulTerm,List.foldr_cons] at ih ⊢
    rw [insert_value,ih,key_value]
    simp only [value,valTerm,pow_add]; ring

theorem mul_value (s : ℚ) (A : Nat → ℚ) (a b : Form) :
    value s (A2 A) (mul a b)=value s A a*value s A b := by
  induction a with
  | nil => simp [mul,value]
  | cons t a ih =>
    simp only [mul,List.foldr_cons] at ih ⊢
    rw [plus_value,mulTerm_value,ih]
    simp only [value]; ring

/-- `det w g c` from coordinate forms: `(gx-wx)(cy-wy) - (gy-wy)(cx-wx)`. -/
def det (wx wy gx gy cx cy : Form) : Form :=
  diff (mul (diff gx wx) (diff cy wy)) (mul (diff gy wy) (diff cx wx))

theorem det_value (s : ℚ) (A : Nat → ℚ) (wx wy gx gy cx cy : Form) :
    value s (A2 A) (det wx wy gx gy cx cy)=
      (value s A gx-value s A wx)*(value s A cy-value s A wy)-
        (value s A gy-value s A wy)*(value s A cx-value s A wx) := by
  simp only [det,diff_value,mul_value]

/-- A certified strict sign of an expanded product form. -/
theorem positive {B : Nat → Box} {A : Nat → ℚ} (h : Bounds B A) {s : ℚ} (hs : 0<s) (hu : s≤cap)
    {f : Form} {k : Nat} (pass : RegisterForm.positive (B2 B) f k=true) : 0<value s (A2 A) f :=
  positive_value (bounds2 h) hs hu pass

/-- A certified weak sign of an expanded product form. -/
theorem nonneg {B : Nat → Box} {A : Nat → ℚ} (h : Bounds B A) {s : ℚ} (hs : 0<s) (hu : s≤cap)
    {f : Form} {k : Nat} (pass : RegisterForm.nonneg (B2 B) f k=true) : 0≤value s (A2 A) f :=
  nonneg_value (bounds2 h) hs hu pass

end ArtGallery.Orthogonal.BoundaryPoint.RegisterPoly
end
