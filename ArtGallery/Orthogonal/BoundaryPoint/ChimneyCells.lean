module

public import ArtGallery.Geometry.Basic

/-! # Closed cells of the isolated stepped relay chimney -/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ChimneyRegion
open Set

/-- An axis-parallel closed cell, in the coordinate order used by the generator. -/
def cell (xlo xhi ylo yhi : ℝ) : Set Point :=
  {p | xlo ≤ p.1 ∧ p.1 ≤ xhi ∧ ylo ≤ p.2 ∧ p.2 ≤ yhi}

def leftRoom : Set Point := cell (-20) (1 / 2) (-10) 0

def rightRoom : Set Point := cell (1 / 2) 20 (-12) 0

def shaft : Set Point := cell 0 1 0 (20 / 11)

theorem cell_eq_prod (a b c d : ℝ) : cell a b c d = Icc a b ×ˢ Icc c d := by
  ext p
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ (_ ∧ _)
  tauto

theorem cell_closed (a b c d : ℝ) : IsClosed (cell a b c d) := by
  rw [cell_eq_prod]
  exact isClosed_Icc.prod isClosed_Icc

theorem cell_convex (a b c d : ℝ) : Convex ℝ (cell a b c d) := by
  rw [cell_eq_prod]
  exact (convex_Icc _ _).prod (convex_Icc _ _)

end ArtGallery.Orthogonal.BoundaryPoint.ChimneyRegion
end
