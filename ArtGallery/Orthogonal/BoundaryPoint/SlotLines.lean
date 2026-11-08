module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomCoordinates
public import ArtGallery.Orthogonal.BoundaryPoint.InversionCriticalAlgebra

/-! # Lines from the guards in a physical room

The slot displacement ranges from zero to 3/2. The endpoints used here are
entries one and two of the same role records as the generator and pin audits.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SlotLines
open RoomGrid ArtGallery.Orthogonal.Hard Geometry

noncomputable def slot (pt : Index → Point) (roles : List (List Index)) (i : Nat) (t : ℝ) : Point :=
  let row := roles.getD i []
  lerp (pt (row.getD 1 (0,0))) (pt (row.getD 2 (0,0))) (t*(2/3))

noncomputable def xSlope (edge : ℝ) (p : Point) := (edge-p.1)/(-p.2)
noncomputable def rayY (g c : Point) (x : ℝ) := g.2+(c.2-g.2)*(x-g.1)/(c.1-g.1)
noncomputable def world (v : ℝ) (p : Point) : Point := (501/2+5*v*p.1,-4+p.2/12)

theorem ray_world {v : ℝ} (hv : 0<v) (g c : Point) (X : ℝ) :
    rayY (world v g) (world v c) (501/2+5*v*X) = -4+rayY g c X/12 := by
  unfold world rayY
  dsimp only
  by_cases h : c.1=g.1
  · simp [h]
  · have hdiff : 501/2+5*v*c.1-(501/2+5*v*g.1) = (5*v)*(c.1-g.1) := by ring
    rw [hdiff]
    field_simp [sub_ne_zero.mpr h,ne_of_gt hv] <;> ring

end ArtGallery.Orthogonal.BoundaryPoint.SlotLines
end
