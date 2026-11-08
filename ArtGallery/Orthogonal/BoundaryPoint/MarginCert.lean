module

public import ArtGallery.Orthogonal.Hard.RatEq
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! # Rational certificates for parameter-dependent construction margins

Rows contain fixed rational outer bounds. A backwards reference of 0 denotes
the most recent row. Only endpoint arithmetic is performed by the checker.
The soundness theorem interprets parameters and arithmetic over the reals.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.MarginCert

structure Box where
  lo : ℚ
  hi : ℚ

def Box.Mem (b : Box) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)
def Box.test (b : Box) (x : ℚ) : Bool := decide (b.lo ≤ x ∧ x ≤ b.hi)

theorem Box.of_test {b : Box} {x : ℚ} (h : b.test x = true) : b.Mem (x : ℝ) := by
  have h' := of_decide_eq_true h
  exact ⟨Rat.cast_le.mpr h'.1,Rat.cast_le.mpr h'.2⟩

/-- A linear function of one coordinate is bounded by its two endpoints. -/
private theorem between_mul {L H a b x m : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (h₁ : L ≤ a*m ∧ a*m ≤ H) (h₂ : L ≤ b*m ∧ b*m ≤ H) :
    L ≤ x*m ∧ x*m ≤ H := by
  rcases le_total 0 m with hm | hm
  · exact ⟨h₁.1.trans (mul_le_mul_of_nonneg_right ha hm),
           (mul_le_mul_of_nonneg_right hb hm).trans h₂.2⟩
  · exact ⟨h₂.1.trans (mul_le_mul_of_nonpos_right hb hm),
           (mul_le_mul_of_nonpos_right ha hm).trans h₁.2⟩

inductive Op
  | input (i : Nat)
  | lit (q : ℚ)
  | neg (a : Nat)
  | plus (a b : Nat)
  | times (a b : Nat)
  | recip (a : Nat)
  | absVal (a : Nat)
  | larger (a b : Nat)

def zeroBox : Box := ⟨0,0⟩
def getBox (bs : List Box) (i : Nat) : Box := bs[i]?.getD zeroBox
noncomputable def getReal (vs : List ℝ) (i : Nat) : ℝ := vs[i]?.getD 0

noncomputable def Op.val (args vs : List ℝ) : Op → ℝ
  | .input i => getReal args i
  | .lit q => q
  | .neg i => -getReal vs i
  | .plus i j => getReal vs i + getReal vs j
  | .times i j => getReal vs i * getReal vs j
  | .recip i => (getReal vs i)⁻¹
  | .absVal i => |getReal vs i|
  | .larger i j => max (getReal vs i) (getReal vs j)

def Op.ok (args bs : List Box) (r : Box) : Op → Bool
  | .input i => let b := getBox args i; r.test b.lo && r.test b.hi
  | .lit q => r.test q
  | .neg i => let a := getBox bs i; r.test (-a.hi) && r.test (-a.lo)
  | .plus i j => let a := getBox bs i; let b := getBox bs j
                 r.test (a.lo+b.lo) && r.test (a.hi+b.hi)
  | .times i j => let a := getBox bs i; let b := getBox bs j
                  (r.test (a.lo*b.lo) && r.test (a.lo*b.hi)) &&
                  (r.test (a.hi*b.lo) && r.test (a.hi*b.hi))
  | .recip i => let a := getBox bs i
                (decide (0 < a.lo) || decide (a.hi < 0)) && (r.test a.hi⁻¹ && r.test a.lo⁻¹)
  | .absVal i => let a := getBox bs i
                 r.test 0 && (r.test |a.lo| && r.test |a.hi|)
  | .larger i j => let a := getBox bs i; let b := getBox bs j
                   r.test (max a.lo b.lo) && r.test (max a.hi b.hi)

def Encloses (bs : List Box) (vs : List ℝ) : Prop := ∀ i, (getBox bs i).Mem (getReal vs i)

private theorem andParts {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using h

private theorem orParts {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  simpa only [Bool.or_eq_true] using h

theorem Op.sound {args bs : List Box} {v xs : List ℝ} {r : Box} {op : Op}
    (hv : Encloses args v) (hx : Encloses bs xs) (h : op.ok args bs r = true) :
    r.Mem (op.val v xs) := by
  cases op with
  | lit q => exact Box.of_test h
  | input i =>
    obtain ⟨h₁,h₂⟩ := andParts h
    exact ⟨(Box.of_test h₁).1.trans (hv i).1,(hv i).2.trans (Box.of_test h₂).2⟩
  | neg i =>
    obtain ⟨h₁,h₂⟩ := andParts h
    have l := (Box.of_test h₁).1
    have u := (Box.of_test h₂).2
    dsimp only [Op.val, Box.Mem]
    push_cast at l u
    exact ⟨l.trans (neg_le_neg (hx i).2),(neg_le_neg (hx i).1).trans u⟩
  | plus i j =>
    obtain ⟨h₁,h₂⟩ := andParts h
    have l := (Box.of_test h₁).1
    have u := (Box.of_test h₂).2
    push_cast at l u
    exact ⟨l.trans (add_le_add (hx i).1 (hx j).1),(add_le_add (hx i).2 (hx j).2).trans u⟩
  | times i j =>
    obtain ⟨hl,hu⟩ := andParts h
    obtain ⟨h₁,h₂⟩ := andParts hl
    obtain ⟨h₃,h₄⟩ := andParts hu
    have A := Box.of_test h₁; have B := Box.of_test h₂
    have C := Box.of_test h₃; have D := Box.of_test h₄
    dsimp only [Box.Mem] at A B C D
    push_cast at A B C D
    apply between_mul (hx i).1 (hx i).2
    · rw [mul_comm]
      apply between_mul (hx j).1 (hx j).2
      · simpa only [mul_comm] using A
      · simpa only [mul_comm] using B
    · rw [mul_comm]
      apply between_mul (hx j).1 (hx j).2
      · simpa only [mul_comm] using C
      · simpa only [mul_comm] using D
  | recip i =>
    obtain ⟨hne,hh⟩ := andParts h
    obtain ⟨h₁,h₂⟩ := andParts hh
    have l := (Box.of_test h₁).1; have u := (Box.of_test h₂).2
    push_cast at l u
    rcases orParts hne with hp | hn
    · have ha : (0:ℝ) < (getBox bs i).lo := by exact_mod_cast of_decide_eq_true hp
      have hb := lt_of_lt_of_le ha (hx i).1
      exact ⟨l.trans ((inv_le_inv₀ (hb.trans_le (hx i).2) hb).2 (hx i).2),
             ((inv_le_inv₀ hb ha).2 (hx i).1).trans u⟩
    · have ha : ((getBox bs i).hi:ℝ) < 0 := by exact_mod_cast of_decide_eq_true hn
      have hb := lt_of_le_of_lt (hx i).2 ha
      exact ⟨l.trans ((inv_le_inv_of_neg ha hb).2 (hx i).2),
             ((inv_le_inv_of_neg hb ((hx i).1.trans_lt hb)).2 (hx i).1).trans u⟩
  | absVal i =>
    obtain ⟨hz,hh⟩ := andParts h
    obtain ⟨h₁,h₂⟩ := andParts hh
    have l := (Box.of_test hz).1; have u₁ := (Box.of_test h₁).2; have u₂ := (Box.of_test h₂).2
    push_cast at l u₁ u₂
    refine ⟨l.trans (abs_nonneg _),abs_le.mpr ⟨?_,?_⟩⟩
    · have := neg_le_abs (((getBox bs i).lo):ℝ)
      linarith [(hx i).1]
    · exact (hx i).2.trans ((le_abs_self _).trans u₂)
  | larger i j =>
    obtain ⟨h₁,h₂⟩ := andParts h
    have l := (Box.of_test h₁).1; have u := (Box.of_test h₂).2
    push_cast at l u
    exact ⟨l.trans (max_le_max (hx i).1 (hx j).1),(max_le_max (hx i).2 (hx j).2).trans u⟩

structure Row where
  op : Op
  bound : Box
  positive : Bool

def ok (args : List Box) : List Box → List Row → Bool
  | _, [] => true
  | bs, r :: rest => (r.op.ok args bs r.bound && (!r.positive || decide (0 < r.bound.lo))) &&
                      ok args (r.bound :: bs) rest

def Margins (args : List ℝ) : List ℝ → List Row → Prop
  | _, [] => True
  | vs, r :: rest => (r.positive = true → 0 < r.op.val args vs) ∧
                      Margins args (r.op.val args vs :: vs) rest

theorem Encloses.cons {b bs v vs} (h : Box.Mem b v) (hs : Encloses bs vs) :
    Encloses (b :: bs) (v :: vs) := by
  intro i
  cases i with
  | zero => exact h
  | succ j => simpa only [getBox,getReal,List.getElem?_cons_succ] using hs j

theorem certified {args v} (hv : Encloses args v) (rs : List Row)
    {bs vs} (hs : Encloses bs vs) (h : ok args bs rs = true) : Margins v vs rs := by
  induction rs generalizing bs vs with
  | nil => trivial
  | cons r rest ih =>
    obtain ⟨hr,hrest⟩ := andParts h
    obtain ⟨hop,hpos⟩ := andParts hr
    have hb := Op.sound hv hs hop
    constructor
    · intro htag
      have hp : 0 < r.bound.lo := by simpa [htag] using hpos
      exact lt_of_lt_of_le (Rat.cast_pos.mpr hp) hb.1
    · exact ih (hs.cons hb) hrest

/-- Final interval stack after a checked straight-line block. -/
def stack (bs : List Box) : List Row → List Box
  | [] => bs
  | r :: rs => stack (r.bound :: bs) rs

theorem ok_join {args bs first rest} (h₁ : ok args bs first = true)
    (h₂ : ok args (stack bs first) rest = true) : ok args bs (first ++ rest) = true := by
  induction first generalizing bs with
  | nil => exact h₂
  | cons r rs ih =>
    obtain ⟨h,h'⟩ := andParts h₁
    simpa only [List.cons_append, ok, h, Bool.true_and] using ih h' h₂

theorem empty_encloses : Encloses [] [] := by
  intro i
  simp [Box.Mem,getBox,getReal,zeroBox]

theorem reciprocal_size {n : Nat} (hn : 65 ≤ n) : Box.Mem ⟨0,1/65⟩ (1/(n:ℝ)) := by
  have h : (65:ℝ) ≤ n := by exact_mod_cast hn
  dsimp only [Box.Mem]
  push_cast
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) h⟩

theorem normalized_index {n i : Nat} (hn : 65 ≤ n) (hi : i ≤ n) :
    Box.Mem ⟨0,1⟩ ((i:ℝ)/n) := by
  have ht : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  dsimp only [Box.Mem]
  push_cast
  refine ⟨by positivity, (div_le_iff₀ ht).2 ?_⟩
  simpa only [one_mul] using (show (i:ℝ) ≤ n by exact_mod_cast hi)

theorem from_empty {args v} (hv : Encloses args v) (rs : List Row) (h : ok args [] rs = true) :
    Margins v [] rs := by
  apply certified hv rs (h := h)
  intro i
  simp [Box.Mem,getBox,getReal,zeroBox]

end ArtGallery.Orthogonal.BoundaryPoint.MarginCert
end
