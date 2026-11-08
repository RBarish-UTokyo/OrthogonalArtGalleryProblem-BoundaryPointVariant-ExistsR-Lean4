module

public import ArtGallery.Orthogonal.BoundaryPoint.CoverValuation
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalShape

/-! # Any positive output of the reduction has a satisfiable source -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ReductionSound
open Set Complexity

theorem from_cover {eqs : List ETRINV.Constraint} {vs : List RectContour.Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (vs,g))
    (covered : (Polygon.mk (vs.map ratPoint)).HasGuardSetOnBoundaryOfCard g) : ETRINV.Satisfiable eqs := by
  by_cases ne : eqs=[]
  · subst eqs; exact ⟨fun _ => 1,fun _ => ⟨by norm_num,by norm_num⟩,by simp⟩
  · obtain ⟨G,card,cover⟩ := covered
    exact CoverValuation.satisfiable ne out G cover card.le

theorem inv (w : Word) (covered : AGPOrthBoundaryPoint (CandidateWord.word w)) : ETRINV w := by
  obtain ⟨eqs,vs,g,decode,out,cover⟩ := (GlobalShape.target_iff_guards w).mp covered
  exact ⟨eqs,ETRINV.encode_of_decodeINV decode,from_cover out cover⟩

theorem etr (w : Word) (covered : AGPOrthBoundaryPoint (RegistryMap.fromETR w)) : ETR w :=
  (etrReduction_correct w).mpr (inv _ covered)

end ArtGallery.Orthogonal.BoundaryPoint.ReductionSound
end
