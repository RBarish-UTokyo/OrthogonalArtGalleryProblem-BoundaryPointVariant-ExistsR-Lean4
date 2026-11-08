module

public import ArtGallery.Orthogonal.BoundaryPoint.EmittedGallery
public import ArtGallery.Orthogonal.BoundaryPoint.RealizedWings
public import ArtGallery.Orthogonal.BoundaryPoint.RegistryMap
public import ArtGallery.Orthogonal.BoundaryPoint.EmptySource

/-! # Global topological correctness of the polynomial-time word map
The complete closed polygon is the hub with exactly its simple wing polygons
attached at the doors. The remaining language-equivalence statement concerns
the guard placements and their visibility. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GlobalShape
open Complexity RectContour CandidateWord

theorem decomposition {eqs : List ETRINV.Constraint} (nonempty : eqs≠[]) {v : List Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g)) :
    EmittedGallery.Shape eqs ⟨v.map ratPoint⟩ :=
  EmittedGallery.of_splice nonempty (fun _ _ _ path => RealizedWings.simple path) out

theorem simple {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g)) : (Polygon.mk (v.map ratPoint)).Simple := by
  by_cases empty : eqs=[]
  · subst eqs
    have accepted := EmptySource.accepted
    rw [word_of_output EmptySource.emitted] at accepted
    have h := ((encoded_iff _ _).mp accepted).1
    rw [EmptySource.emitted] at out
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj out)
    exact h
  · exact (decomposition empty out).simple

theorem geometry (eqs : List ETRINV.Constraint) :
    ∃ v g,CandidateWord.vertices eqs=some (v,g) ∧
      (Polygon.mk (v.map ratPoint)).Simple ∧ (Polygon.mk (v.map ratPoint)).Orthogonal := by
  obtain ⟨v,g,h⟩ := CandidateTotal.exists_vertices eqs
  exact ⟨v,g,h,simple h,HubTurn.word_vertices eqs h⟩

theorem target_iff_guards (w : Word) : AGPOrthBoundaryPoint (CandidateWord.word w) ↔
    ∃ eqs v g, ETRINV.decodeINV w=some eqs ∧ CandidateWord.vertices eqs=some (v,g) ∧
      (Polygon.mk (v.map ratPoint)).HasGuardSetOnBoundaryOfCard g := by
  rw [RegistryMap.target_iff]
  constructor
  · rintro ⟨eqs,v,g,parse,out,_,cover⟩; exact ⟨eqs,v,g,parse,out,cover⟩
  · rintro ⟨eqs,v,g,parse,out,cover⟩; exact ⟨eqs,v,g,parse,out,simple out,cover⟩

end ArtGallery.Orthogonal.BoundaryPoint.GlobalShape
end
