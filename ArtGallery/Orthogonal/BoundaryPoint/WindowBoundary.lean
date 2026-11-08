module

public import ArtGallery.Jordan.Jordan

/-! # Boundary guards under attachment

A global boundary guard lying in a room is a local boundary guard. In the
other direction, a local boundary guard outside the attached closed region
remains available globally. These statements connect closed-region gluing to
the boundary restriction in the art-gallery specification.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WindowBoundary

open Set

/-- Every global boundary point in a contained room belongs to that
room's polygonal boundary. -/
theorem restrict_guard {room P : Polygon} (hr : room.Simple) (hp : P.Simple)
    (hsub : room.filled ⊆ P.filled) {g : Point}
    (hg : g ∈ P.boundary) (hin : g ∈ room.filled) : g ∈ room.boundary := by
  by_contra h
  have hlocal : g ∈ interior room.filled := by
    rw [Jordan.interior_filled hr]
    exact ⟨hin,h⟩
  have hglobal := interior_mono hsub hlocal
  rw [Jordan.interior_filled hp] at hglobal
  exact hglobal.2 hg

/-- A canonical room guard outside a closed addition remains on the global
polygon boundary. -/
theorem extend_guard {room P : Polygon} {H : Set Point} (hr : room.Simple) (hp : P.Simple)
    (hjoined : P.filled = room.filled ∪ H) (hH : IsClosed H) {g : Point}
    (hg : g ∈ room.boundary) (hoff : g ∉ H) : g ∈ P.boundary := by
  by_contra h
  have hglobal : g ∈ interior P.filled := by
    rw [Jordan.interior_filled hp]
    refine ⟨?_,h⟩
    rw [hjoined]
    exact Or.inl (Jordan.boundary_subset_filled room hg)
  rw [hjoined] at hglobal
  have haway : g ∈ interior Hᶜ := by simpa [hH.isOpen_compl.interior_eq] using hoff
  have hlocal : g ∈ interior room.filled :=
    interior_union_inter_interior_compl_right_subset ⟨hglobal,haway⟩
  rw [Jordan.interior_filled hr] at hlocal
  exact hlocal.2 hg

end ArtGallery.Orthogonal.BoundaryPoint.WindowBoundary
end
