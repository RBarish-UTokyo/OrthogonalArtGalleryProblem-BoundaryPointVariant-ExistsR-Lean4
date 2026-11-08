module

public import ArtGallery.Orthogonal.BoundaryPoint.SpanCells
public import ArtGallery.Vis.API
public import ArtGallery.Vis.Cones

/-! # Index-level orientation tests on an ordered grid

For an axis-parallel segment between two grid nodes `a → b` and any point `z`
whose atom codes are known, the sign of `det a b z` is a product of two index
comparisons. These tests need only that both grid axes are strictly increasing,
so they hold for every admissible parameter of a wing chart. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SepGeom
open Set GridAtom GridParity RoomGrid SpanCells ArtGallery.Orthogonal.Hard

/-- Sign of a natural-number difference. -/
def cmp (i j : Nat) : Int := if i<j then -1 else if i=j then 0 else 1

/-- Sign of `det (gridPt a) (gridPt b) z` for a point `z` with atom codes `c`. -/
def side (a b : Index) (c : Nat × Nat) : Int :=
  if a.1=b.1 then -(cmp b.2 a.2)*cmp c.1 (line a.1) else cmp b.1 a.1*cmp c.2 (line a.2)

theorem level_lt {xs : List ℝ} (hx : xs.IsChain (·<·)) {i j : Nat} (hj : j<xs.length) (h : i<j) :
    xs.getD i 0<xs.getD j 0 :=
  strictMonoOn_getD hx (show i<xs.length by omega) hj h

/-- Real sign of a grid-level difference. -/
theorem level_sign {xs : List ℝ} (hx : xs.IsChain (·<·)) {i j : Nat} (hi : i<xs.length) (hj : j<xs.length) :
    (cmp i j=-1 → xs.getD i 0-xs.getD j 0<0) ∧ (cmp i j=1 → 0<xs.getD i 0-xs.getD j 0) := by
  unfold cmp
  constructor
  · intro h; split at h
    · next lt => linarith [level_lt hx hj lt]
    · split at h <;> simp at h
  · intro h; split at h
    · simp at h
    · split at h
      · simp at h
      · next n1 n2 =>
        have ji : j < i := by omega
        linarith [level_lt hx hi ji]

/-- Real sign of a coordinate against a grid line, from its atom code. -/
theorem code_sign {xs : List ℝ} (hx : xs.IsChain (·<·)) {i : Nat} (hi : i<xs.length) {z : ℝ} {c : Nat}
    (hz : atom z xs=c) :
    (cmp c (line i)=-1 → z-xs.getD i 0<0) ∧ (cmp c (line i)=1 → 0<z-xs.getD i 0) := by
  have h := compare_line hx hi z
  unfold cmp
  constructor
  · intro e; split at e
    · next lt => have := h.1.mpr (hz ▸ lt); linarith
    · split at e <;> simp at e
  · intro e; split at e
    · simp at e
    · split at e
      · simp at e
      · next n1 n2 =>
        have nlt : ¬z<xs.getD i 0 := fun k => n1 (hz ▸ h.1.mp k)
        have ne : z≠xs.getD i 0 := fun k => n2 (hz ▸ h.2.mp k)
        have : xs.getD i 0<z := lt_of_le_of_ne (not_lt.mp nlt) (Ne.symm ne)
        linarith

private theorem mul_sign {u v : ℝ} {p q : Int}
    (hu : (p=-1 → u<0) ∧ (p=1 → 0<u)) (hv : (q=-1 → v<0) ∧ (q=1 → 0<v))
    (hp : p=-1 ∨ p=0 ∨ p=1) (hq : q=-1 ∨ q=0 ∨ q=1) :
    (p*q<0 → u*v<0) ∧ (0<p*q → 0<u*v) := by
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> norm_num
  all_goals first
    | exact mul_pos_of_neg_of_neg (hu.1 rfl) (hv.1 rfl)
    | exact mul_neg_of_neg_of_pos (hu.1 rfl) (hv.2 rfl)
    | exact mul_neg_of_pos_of_neg (hu.2 rfl) (hv.1 rfl)
    | exact mul_pos (hu.2 rfl) (hv.2 rfl)

theorem cmp_cases (i j : Nat) : cmp i j=-1 ∨ cmp i j=0 ∨ cmp i j=1 := by
  unfold cmp; split
  · simp
  · split <;> simp

/-- Soundness of `side` for an axis-parallel pair of grid nodes and any point with codes `c`. -/
theorem side_sound {xs ys : List ℝ} (hx : xs.IsChain (·<·)) (hy : ys.IsChain (·<·)) {a b : Index}
    (ha : a.1<xs.length ∧ a.2<ys.length) (hb : b.1<xs.length ∧ b.2<ys.length) (axis : a.1=b.1 ∨ a.2=b.2)
    {z : Point} {c : Nat × Nat} (zx : atom z.1 xs=c.1) (zy : atom z.2 ys=c.2) :
    (side a b c<0 → ArtGallery.det (gridPt xs ys a) (gridPt xs ys b) z<0) ∧
      (0<side a b c → 0<ArtGallery.det (gridPt xs ys a) (gridPt xs ys b) z) := by
  unfold side
  simp only [ArtGallery.det,gridPt]
  split
  · next v =>
    rw [v]
    have e : (xs.getD b.1 0-xs.getD b.1 0)*(z.2-ys.getD a.2 0)-(z.1-xs.getD b.1 0)*(ys.getD b.2 0-ys.getD a.2 0)=
        -((ys.getD b.2 0-ys.getD a.2 0)*(z.1-xs.getD b.1 0)) := by ring
    rw [e]
    have m := mul_sign (level_sign hy hb.2 ha.2) (code_sign hx hb.1 (c:=c.1) zx) (cmp_cases _ _) (cmp_cases _ _)
    constructor
    · intro h
      rw [neg_mul] at h
      have := m.2 (by linarith)
      linarith
    · intro h
      rw [neg_mul] at h
      have := m.1 (by linarith)
      linarith
  · next v =>
    have hz : a.2=b.2 := axis.resolve_left v
    rw [← hz]
    have e : (xs.getD b.1 0-xs.getD a.1 0)*(z.2-ys.getD a.2 0)-(z.1-xs.getD a.1 0)*(ys.getD a.2 0-ys.getD a.2 0)=
        (xs.getD b.1 0-xs.getD a.1 0)*(z.2-ys.getD a.2 0) := by ring
    rw [e]
    have m := mul_sign (level_sign hx hb.1 ha.1) (code_sign hy ha.2 (c:=c.2) zy) (cmp_cases _ _) (cmp_cases _ _)
    exact ⟨m.1,m.2⟩

/-- The atom code of a grid level is its line code. -/
theorem atom_level {xs : List ℝ} (hx : xs.IsChain (·<·)) {i : Nat} (hi : i<xs.length) :
    atom (xs.getD i 0) xs=line i := ((compare_line hx hi _).2).mp rfl

/-- `side` evaluated at a grid node. -/
def sideNode (a b p : Index) : Int := side a b (line p.1,line p.2)

theorem side_node {xs ys : List ℝ} (hx : xs.IsChain (·<·)) (hy : ys.IsChain (·<·)) {a b p : Index}
    (ha : a.1<xs.length ∧ a.2<ys.length) (hb : b.1<xs.length ∧ b.2<ys.length)
    (hp : p.1<xs.length ∧ p.2<ys.length) (axis : a.1=b.1 ∨ a.2=b.2) :
    (sideNode a b p<0 → ArtGallery.det (gridPt xs ys a) (gridPt xs ys b) (gridPt xs ys p)<0) ∧
      (0<sideNode a b p → 0<ArtGallery.det (gridPt xs ys a) (gridPt xs ys b) (gridPt xs ys p)) :=
  side_sound hx hy ha hb axis (z:=gridPt xs ys p) (c:=(line p.1,line p.2)) (atom_level hx hp.1) (atom_level hy hp.2)

end ArtGallery.Orthogonal.BoundaryPoint.SepGeom
end
