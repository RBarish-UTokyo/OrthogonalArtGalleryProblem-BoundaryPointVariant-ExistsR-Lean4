module

public import ArtGallery.Stade.PTimeRat
public import ArtGallery.Orthogonal.BoundaryPoint.BankPitch

/-! # Executable rational coordinates and PT proofs for the bank/door layout

These are the parameters used by the staircase generator. The upper copy axis
is computed directly from the intersecting rays, without a search. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.BankCoordinates

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

def k (n : ℕ) : ℚ := 50*(n:ℚ)*(n:ℚ)
def D (n : ℕ) : ℚ := 1001*k n
def W (n : ℕ) : ℚ := 1/(320*(n:ℚ))
def delta (n : ℕ) : ℚ := 125*(n:ℚ)
def door (j : ℕ) : ℚ := -2000*(j:ℚ)
def slotX (n bank rank : ℕ) : ℚ := W n + k n*((bank:ℚ)-1/5) + (rank:ℚ)*delta n
def baseRate (n bank rank row : ℕ) : ℚ := (slotX n bank rank-door row-W n)/D n

def E (n : ℕ) : ℚ := 2*D n/5
def epsilon (n : ℕ) : ℚ := 1/(2*E n)
def qRate : ℚ := 45
def xRate : ℚ := 415/6
def zRate (n : ℕ) (offset : ℚ) : ℚ := 217/2 + (offset-1/2)/D n
def aRate (n : ℕ) : ℚ := 96/5 + (1/2)/D n
def bRate (n : ℕ) (reversed : Bool) : ℚ :=
  20 + (if reversed then epsilon n-2 else 1/2-epsilon n)/D n

def upperHeight (n : ℕ) (base receiver : ℚ) : ℚ :=
  1+(301/2-W n)/(receiver-base)

section Computation
variable {α : Type} [Code α]

@[fun_prop] theorem k_pt {n : α → ℕ} (hn : PT n) : PT (fun a => k (n a)) := by unfold k; fun_prop
@[fun_prop] theorem D_pt {n : α → ℕ} (hn : PT n) : PT (fun a => D (n a)) := by unfold D; fun_prop
@[fun_prop] theorem W_pt {n : α → ℕ} (hn : PT n) : PT (fun a => W (n a)) := by unfold W; fun_prop
@[fun_prop] theorem delta_pt {n : α → ℕ} (hn : PT n) : PT (fun a => delta (n a)) := by unfold delta; fun_prop
@[fun_prop] theorem door_pt {j : α → ℕ} (hj : PT j) : PT (fun a => door (j a)) := by unfold door; fun_prop
@[fun_prop] theorem slotX_pt {n b i : α → ℕ} (hn : PT n) (hb : PT b) (hi : PT i) :
    PT (fun a => slotX (n a) (b a) (i a)) := by unfold slotX; fun_prop
@[fun_prop] theorem baseRate_pt {n b i j : α → ℕ} (hn : PT n) (hb : PT b) (hi : PT i) (hj : PT j) :
    PT (fun a => baseRate (n a) (b a) (i a) (j a)) := by unfold baseRate; fun_prop
@[fun_prop] theorem E_pt {n : α → ℕ} (hn : PT n) : PT (fun a => E (n a)) := by unfold E; fun_prop
@[fun_prop] theorem epsilon_pt {n : α → ℕ} (hn : PT n) : PT (fun a => epsilon (n a)) := by unfold epsilon; fun_prop
@[fun_prop] theorem zRate_pt {n : α → ℕ} {offset : α → ℚ} (hn : PT n) (ho : PT offset) :
    PT (fun a => zRate (n a) (offset a)) := by unfold zRate; fun_prop
@[fun_prop] theorem aRate_pt {n : α → ℕ} (hn : PT n) :
    PT (fun a => aRate (n a)) := by unfold aRate; fun_prop
@[fun_prop] theorem bRate_pt {n : α → ℕ} {rev : α → Bool} (hn : PT n) (hr : PT rev) :
    PT (fun a => bRate (n a) (rev a)) := by unfold bRate; fun_prop
@[fun_prop] theorem upperHeight_pt {n : α → ℕ} {b r : α → ℚ} (hn : PT n) (hb : PT b) (hr : PT r) :
    PT (fun a => upperHeight (n a) (b a) (r a)) := by unfold upperHeight; fun_prop
end Computation

theorem cast_D (n : ℕ) : (D n : ℝ) = BankPitch.depth n := by
  unfold D k BankPitch.depth
  push_cast
  ring
theorem cast_W (n : ℕ) : (W n : ℝ) = BankPitch.width n := by
  unfold W BankPitch.width
  push_cast
  rfl
theorem cast_slotX (n b i : ℕ) : (slotX n b i : ℝ) = BankPitch.slot n b i := by
  unfold slotX BankPitch.slot BankPitch.scale BankPitch.pitch delta k
  push_cast
  rw [cast_W]
  ring

theorem actual_pitch_margin {n bank rank row : ℕ} {rate : ℚ} {y : ℝ}
    (hn : 1 ≤ n) (hb : 1 ≤ bank ∧ bank ≤ 1000) (hi : rank ≤ n) (hj : row ≤ n)
    (hr : 18 ≤ (rate:ℝ) ∧ (rate:ℝ) ≤ 110)
    (hy : (upperHeight n (baseRate n bank rank row) rate : ℝ) ≤ y) :
    (W n : ℝ) * ((D n : ℝ) + (y-1)) < ((delta n : ℝ)-3/2)*(y-1) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hb' : (1:ℝ) ≤ bank ∧ (bank:ℝ) ≤ 1000 := by exact_mod_cast hb
  have hi' : (0:ℝ) ≤ rank ∧ (rank:ℝ) ≤ n := ⟨by positivity, by exact_mod_cast hi⟩
  have hj' : (0:ℝ) ≤ row ∧ (row:ℝ) ≤ n := ⟨by positivity, by exact_mod_cast hj⟩
  have br := BankPitch.base_rate_bound hn' hb' hi' hj'
  have eqb : (baseRate n bank rank row : ℝ) =
      (BankPitch.slot n bank rank + 2000*row - BankPitch.width n)/BankPitch.depth n := by
    unfold baseRate door
    push_cast
    rw [cast_D, cast_slotX, cast_W]
    ring
  rw [← eqb] at br
  have hne : (rate:ℝ) - (baseRate n bank rank row:ℝ) ≠ 0 := by linarith [br.2,hr.1]
  let h := ((301/2:ℝ)-BankPitch.width n) / ((rate:ℝ)-(baseRate n bank rank row:ℝ))
  have eqh : h*((rate:ℝ)-(baseRate n bank rank row:ℝ)) = 301/2-BankPitch.width n :=
    div_mul_cancel₀ _ hne
  have hmin := BankPitch.height_of_axis hn' hr.2 br.1 (lt_of_le_of_ne (by linarith [br.2,hr.1]) (Ne.symm hne)) eqh
  have ha : (upperHeight n (baseRate n bank rank row) rate : ℝ) = 1+h := by
    unfold upperHeight h
    push_cast
    rw [cast_W]
  rw [ha] at hy
  have result := BankPitch.projected_margin hn' (show 4/3 ≤ y-1 by linarith)
  rw [cast_W,cast_D]
  simpa [delta,BankPitch.pitch] using result

/-- The receiver positions exhaust these three addition and three inversion
formulas. The addition shift is 0, 2 or 5/2 in the generator. -/
def GeneratedRate (n : ℕ) (r : ℚ) : Prop :=
  r = qRate ∨ r = xRate ∨ (∃ o : ℚ, 0 ≤ o ∧ o ≤ 5/2 ∧ r = zRate n o) ∨
  r = aRate n ∨ ∃ rev : Bool, r = bRate n rev

theorem generated_rate_bounds {n : ℕ} {r : ℚ} (hn : 1 ≤ n) (hr : GeneratedRate n r) :
    18 ≤ (r : ℝ) ∧ (r : ℝ) ≤ 110 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have he : 1 ≤ E n := by
    unfold E D k
    have hnq : (1:ℚ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonneg (show 0 ≤ (n:ℚ) by positivity) (show 0 ≤ (n:ℚ)-1 by linarith)]
  have eps : 0 ≤ epsilon n ∧ epsilon n ≤ 1 := by
    unfold epsilon
    constructor
    · positivity
    · apply (div_le_iff₀ (show 0 < 2*E n by linarith)).2
      linarith
  rcases hr with h | h | ⟨o,ho,ho',h⟩ | h | ⟨rev,h⟩
  · subst r; norm_num [qRate]
  · subst r; norm_num [xRate]
  · subst r
    have h₁ : (0:ℝ) ≤ o := by exact_mod_cast ho
    have h₂ := (Rat.cast_le (K := ℝ)).2 ho'
    norm_num at h₂
    unfold zRate
    push_cast
    rw [cast_D]
    apply BankPitch.receiver_rate_bound hn' <;> constructor <;> linarith
  · subst r
    unfold aRate
    push_cast
    rw [cast_D]
    apply BankPitch.receiver_rate_bound hn' <;> norm_num
  · subst r
    have h₁ : (0:ℝ) ≤ epsilon n := by exact_mod_cast eps.1
    have h₂ : (epsilon n:ℝ) ≤ 1 := by exact_mod_cast eps.2
    cases rev <;> simp only [bRate, Bool.false_eq_true, ite_false, ite_true] <;>
      push_cast <;> rw [cast_D] <;>
      apply BankPitch.receiver_rate_bound hn' <;> constructor <;> linarith

theorem generated_pitch_margin {n bank rank row : ℕ} {r : ℚ} {y : ℝ}
    (hn : 1 ≤ n) (hb : 1 ≤ bank ∧ bank ≤ 1000) (hi : rank ≤ n) (hj : row ≤ n)
    (hr : GeneratedRate n r)
    (hy : (upperHeight n (baseRate n bank rank row) r : ℝ) ≤ y) :
    (W n : ℝ) * ((D n : ℝ) + (y-1)) < ((delta n : ℝ)-3/2)*(y-1) :=
  actual_pitch_margin hn hb hi hj (generated_rate_bounds hn hr) hy

end ArtGallery.Orthogonal.BoundaryPoint.BankCoordinates
end
