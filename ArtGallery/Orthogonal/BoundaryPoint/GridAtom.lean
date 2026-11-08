module

public import ArtGallery.Orthogonal.BoundaryPoint.GridPins
public import ArtGallery.Jordan.Jordan

/-! # Point classification in an ordered real coordinate grid

Odd codes are coordinate lines. Even codes are the intervening open
intervals, including the unbounded intervals at both ends. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GridAtom
open RoomGrid ArtGallery.Orthogonal.Hard

noncomputable def atom (z : ℝ) : List ℝ → Nat
  | [] => 0
  | a::as => if z<a then 0 else if z=a then 1 else 2+atom z as

def line (i : Nat) := 2*i+1

theorem atom_bound (z : ℝ) (xs : List ℝ) : atom z xs ≤ 2*xs.length := by
  induction xs with
  | nil => simp [atom]
  | cons a xs ih => simp only [atom,List.length_cons]; split <;> first | omega | split <;> omega

theorem compare_line {xs : List ℝ} (hx : xs.IsChain (· < ·)) {i : Nat} (hi : i<xs.length) (z : ℝ) :
    (z < xs.getD i 0 ↔ atom z xs < line i) ∧ (z = xs.getD i 0 ↔ atom z xs = line i) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      by_cases h : z<a
      · simp [atom,line,h,ne_of_lt h]
      · by_cases he : z=a
        · simp [atom,line,h,he]
        · simp [atom,line,h,he]
          omega
    | succ j =>
      have hj : j<xs.length := by simpa using hi
      have so : xs.IsChain (· < ·) := hx.tail
      have ord : a<xs.getD j 0 := by
        rw [List.getD_eq_getElem (l := xs) (d := 0) hj]
        exact (List.pairwise_cons.mp (List.isChain_iff_pairwise.mp hx)).1 _ (List.getElem_mem hj)
      simp only [List.getD_cons_succ]
      by_cases h : z<a
      · have hz := h.trans ord
        simp only [atom,h,ite_true]
        have hl : 0<line (j+1) := by unfold line; omega
        exact ⟨iff_of_true hz hl,iff_of_false hz.ne hl.ne⟩
      · by_cases he : z=a
        · subst z
          simp only [atom,lt_irrefl,ite_false,ite_true]
          have hl : 1<line (j+1) := by unfold line; omega
          exact ⟨iff_of_true ord hl,iff_of_false ord.ne hl.ne⟩
        · have hc := ih so hj
          simp only [atom,h,ite_false,he]
          rw [hc.1,hc.2]
          unfold line
          omega

theorem line_le {xs : List ℝ} (hx : xs.IsChain (· < ·)) {i : Nat} (hi : i<xs.length) (z : ℝ) :
    xs.getD i 0 ≤ z ↔ line i ≤ atom z xs := by
  exact le_iff_le_iff_lt_iff_lt.mpr (compare_line hx hi z).1

theorem le_line {xs : List ℝ} (hx : xs.IsChain (· < ·)) {i : Nat} (hi : i<xs.length) (z : ℝ) :
    z ≤ xs.getD i 0 ↔ atom z xs ≤ line i := by
  have h := compare_line hx hi z
  rw [le_iff_lt_or_eq,le_iff_lt_or_eq,h.1,h.2]

end ArtGallery.Orthogonal.BoundaryPoint.GridAtom
end
