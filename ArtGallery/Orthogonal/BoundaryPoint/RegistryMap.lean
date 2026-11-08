module

public import ArtGallery.Orthogonal.BoundaryPoint.HubTurn
public import ArtGallery.Orthogonal.BoundaryPoint.VertexCount
public import ArtGallery.Orthogonal.BoundaryPoint.CandidateSemantics
public import ArtGallery.Orthogonal.BoundaryPoint.WordTime
public import ArtGallery.PTime.ETRtoINV

/-! # The ETR word map and the two language specifications
At the source, satisfiability is equivalent to feasibility of the actual
ranked physical rows. At the target, every emitted rational cycle is
orthogonal, so its simple-polygon and boundary-guard conditions suffice. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegistryMap
open Complexity Complexity.PT CandidateWord CatalogRanks DerivedAlgebra

def fromETR (w : Word) : Word := CandidateWord.word (etrReduction w)

theorem polynomial_time : PolyTime fromETR := (WordTime.typed.comp PT.etrReduction).polyTime_word

theorem inv_iff_plan (w : Word) : ETRINV w ↔ ∃ eqs, ETRINV.decodeINV w=some eqs ∧
    ∃ a : Addr → ℝ, (∀ i,InRange (a i)) ∧ Physical (CatalogPlan.compile eqs) a := by
  constructor
  · rintro ⟨eqs,rfl,h⟩
    exact ⟨eqs,ETRINV.decodeINV_encode _,(CatalogRanks.compile_correct _).2 h⟩
  · rintro ⟨eqs,parse,h⟩
    exact ⟨eqs,ETRINV.encode_of_decodeINV parse,(CatalogRanks.compile_correct _).1 h⟩

theorem etr_iff_plan (w : Word) : ETR w ↔ ∃ eqs, ETRINV.decodeINV (etrReduction w)=some eqs ∧
    ∃ a : Addr → ℝ, (∀ i,InRange (a i)) ∧ Physical (CatalogPlan.compile eqs) a :=
  (etrReduction_correct w).trans (inv_iff_plan _)

theorem target_iff (w : Word) : AGPOrthBoundaryPoint (word w) ↔
    ∃ eqs v g, ETRINV.decodeINV w=some eqs ∧ CandidateWord.vertices eqs=some (v,g) ∧
      let P := Polygon.mk (v.map ratPoint)
      P.Simple ∧ P.HasGuardSetOnBoundaryOfCard g := by
  rw [output_iff]
  constructor
  · rintro ⟨eqs,v,g,hp,hv,hs,_,hg⟩; exact ⟨eqs,v,g,hp,hv,hs,hg⟩
  · rintro ⟨eqs,v,g,hp,hv,hs,hg⟩
    exact ⟨eqs,v,g,hp,hv,hs,HubTurn.word_vertices eqs hv,hg⟩

end ArtGallery.Orthogonal.BoundaryPoint.RegistryMap
end
