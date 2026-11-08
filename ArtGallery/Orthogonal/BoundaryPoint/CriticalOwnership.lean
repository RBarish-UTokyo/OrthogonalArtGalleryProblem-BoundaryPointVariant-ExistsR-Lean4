module

public import ArtGallery.Orthogonal.BoundaryPoint.WindowTree

/-! # Restricting a global cover to the critical regions of an attached room
The other gallery guards may illuminate the room outside its arithmetic tests.
Only exclusion from the critical target set is needed to read the equation. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CriticalOwnership
open Set

theorem restrict_to_room {P room : Polygon} (tree : WindowTree.Attachments room.filled P.filled)
    (critical : Point → Prop) (H : Set Point) (roles : Nat) (G : Nat → Point)
    (inside : ∀ i, i<roles → G i∈room.filled)
    (cover : ∀ z∈P.filled, ∃ g∈H, P.Sees g z)
    (exclude : ∀ z∈room.filled, critical z → ∀ g∈H, (∀ i, i<roles → g≠G i) → ¬P.Sees g z) :
    ∀ z∈room.filled, critical z → ∃ i, i<roles ∧ room.Sees (G i) z := by
  classical
  intro z hz test
  obtain ⟨g,hg,see⟩ := cover z (tree.subset hz)
  by_cases own : ∃ i, i<roles ∧ g=G i
  · obtain ⟨i,hi,rfl⟩ := own
    exact ⟨i,hi,(tree.sees_iff (inside i hi) hz).1 see⟩
  · exact (exclude z hz test g hg (fun i hi h => own ⟨i,hi,h⟩) see).elim

end ArtGallery.Orthogonal.BoundaryPoint.CriticalOwnership
end
