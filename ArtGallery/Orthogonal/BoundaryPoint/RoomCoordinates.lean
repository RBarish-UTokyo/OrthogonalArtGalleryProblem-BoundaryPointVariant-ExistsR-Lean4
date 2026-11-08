module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomGrid
public import ArtGallery.Orthogonal.BoundaryPoint.MarginEval

/-! # Polynomial coordinate lines for the arithmetic rooms

At inverse size s, a certified gap has the form s^k times a polynomial
bounded below by a positive rational on [0,1/65]. Thus the grid is strictly
increasing even when some of its coordinate lines coalesce in the limit. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCoordinates

open Set RoomGrid Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

def evalQ (s : ℚ) : List ℚ → ℚ
  | [] => 0
  | a::p => a+s*evalQ s p

noncomputable def evalR (s : ℝ) : List ℚ → ℝ
  | [] => 0
  | a::p => (a:ℝ)+s*evalR s p

def lower : List ℚ → ℚ
  | [] => 0
  | a::p => a+min 0 (lower p/65)

theorem lower_le (p : List ℚ) {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ 1/65) :
    (lower p : ℝ) ≤ evalR s p := by
  induction p with
  | nil => simp [lower,evalR]
  | cons a p ih =>
    simp only [lower,evalR,Rat.cast_add,Rat.cast_min,Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat]
    apply add_le_add le_rfl
    apply le_trans _ (mul_le_mul_of_nonneg_left ih hs)
    by_cases h : 0 ≤ (lower p : ℝ)
    · exact (min_le_left _ _).trans (mul_nonneg hs h)
    · apply (min_le_right _ _).trans
      have hm := mul_le_mul_of_nonpos_right hu (le_of_not_ge h)
      linarith

structure Gap where
  order : Nat
  coefficients : List ℚ

structure Axis where
  initial : List ℚ
  gaps : List Gap

def Axis.ok (a : Axis) := a.gaps.all (fun g => decide (0 < lower g.coefficients))

def Gap.valQ (g : Gap) (s : ℚ) := s^g.order * evalQ s g.coefficients
noncomputable def Gap.valR (g : Gap) (s : ℝ) := s^g.order * evalR s g.coefficients

def positions {α : Type} [Add α] (f : Gap → α) (z : α) : List Gap → List α
  | [] => [z]
  | g::gs => z :: positions f (z+f g) gs

theorem length_positions {α : Type} [Add α] (f : Gap → α) (gs : List Gap) (z : α) :
    (positions f z gs).length=gs.length+1 := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih => simp [positions,ih]

def Axis.coordsQ (a : Axis) (s : ℚ) : List ℚ :=
  positions (fun g => g.valQ s) (evalQ s a.initial) a.gaps
noncomputable def Axis.coordsR (a : Axis) (s : ℝ) : List ℝ :=
  positions (fun g => g.valR s) (evalR s a.initial) a.gaps

theorem cast_eval (s : ℚ) (p : List ℚ) : (evalQ s p : ℝ) = evalR s p := by
  induction p with
  | nil => simp [evalQ,evalR]
  | cons a p ih => simp [evalQ,evalR,ih]

theorem cast_coords (a : Axis) (s : ℚ) :
    (a.coordsQ s).map (fun q : ℚ => (q:ℝ)) = a.coordsR s := by
  have scan (gs : List Gap) (q : ℚ) :
      (positions (fun g => g.valQ s) q gs).map (fun t : ℚ => (t:ℝ)) =
      positions (fun g => g.valR (s:ℝ)) (q:ℝ) gs := by
    induction gs generalizing q with
    | nil => rfl
    | cons g gs ih =>
      simp only [positions,List.map_cons]
      rw [ih]
      simp only [Rat.cast_add,Gap.valQ,Gap.valR,Rat.cast_mul,Rat.cast_pow,cast_eval]
  simpa only [Axis.coordsQ,Axis.coordsR,cast_eval] using scan a.gaps (evalQ s a.initial)

theorem Axis.increasing {a : Axis} (ha : a.ok = true) {s : ℝ} (hs : 0<s) (hu : s≤1/65) :
    (a.coordsR s).IsChain (· < ·) := by
  have pos (g) (hg : g ∈ a.gaps) : 0 < g.valR s := by
    have hl : 0 < lower g.coefficients := of_decide_eq_true (List.all_eq_true.mp ha g hg)
    exact mul_pos (pow_pos hs _) ((Rat.cast_pos.mpr hl).trans_le (lower_le _ hs.le hu))
  have scan (gs : List Gap) (z : ℝ) (h : ∀ g ∈ gs, 0 < g.valR s) :
      (positions (fun g => g.valR s) z gs).IsChain (· < ·) := by
    induction gs generalizing z with
    | nil => simp [positions]
    | cons g gs ih =>
      have step := h g (by simp)
      have tail := ih (z+g.valR s) (fun t ht => h t (List.mem_cons_of_mem _ ht))
      cases gs with
      | nil => simpa [positions] using step
      | cons b gs =>
        apply List.isChain_cons_cons.mpr
        exact ⟨by linarith,tail⟩
  apply scan _ _ pos

theorem Axis.for_size {a : Axis} (ha : a.ok = true) {n : Nat} (hn : 65 ≤ n) :
    (a.coordsR (1/(n:ℝ))).IsChain (· < ·) := by
  apply a.increasing ha
  · have : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  · have h : (65:ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by norm_num) h

theorem length_coords (a : Axis) (s : ℝ) : (a.coordsR s).length=a.gaps.length+1 := by
  simp [Axis.coordsR,length_positions]

section Computation
variable {α : Type} [Code α]
theorem eval_pt (p : List ℚ) {s : α → ℚ} (hs : PT s) : PT (fun a => evalQ (s a) p) := by
  induction p with
  | nil => exact PT.const 0
  | cons c p ih => exact PT.ratAdd (PT.const _) (PT.ratMul hs ih)

private theorem power_pt (k : Nat) {s : α → ℚ} (hs : PT s) : PT (fun a => (s a)^k) := by
  induction k with
  | zero => simpa using (PT.const (α := α) (1:ℚ))
  | succ k ih => simpa only [pow_succ] using PT.ratMul ih hs

theorem coords_pt (x : Axis) {s : α → ℚ} (hs : PT s) : PT (fun a => x.coordsQ (s a)) := by
  have scan (gs : List Gap) {z : α → ℚ} (hz : PT z) :
      PT (fun a => positions (fun g => g.valQ (s a)) (z a) gs) := by
    induction gs generalizing z with
    | nil => exact PT.cons hz (PT.const [])
    | cons g gs ih =>
      apply PT.cons hz
      exact ih (PT.ratAdd hz (PT.ratMul (power_pt g.order hs) (eval_pt g.coefficients hs)))
  exact scan x.gaps (eval_pt x.initial hs)
end Computation
end ArtGallery.Orthogonal.BoundaryPoint.RoomCoordinates
end
