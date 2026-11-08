module

public import ArtGallery.Orthogonal.BoundaryPoint.Forward
public import ArtGallery.Orthogonal.BoundaryPoint.WingCatalog
public import ArtGallery.Orthogonal.BoundaryPoint.ReductionSound
public import ArtGallery.Orthogonal.MembershipMain

/-! # The orthogonal boundary-point art gallery problem is `∃ℝ`-complete

The word map `RegistryMap.fromETR` is computable in polynomial time; an ETR instance is true iff
its image is a positive instance: the canonical guards of a satisfying assignment cover the
emitted polygon (`Forward.forward` with the wing catalogue), and the owned guards of any boundary
guard set of the right size read off a satisfying assignment (`ReductionSound.etr`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.Main
open Complexity

theorem forward_word (w : Word) (h : ETR w) : AGPOrthBoundaryPoint (RegistryMap.fromETR w) := by
  obtain ⟨eqs,parse,a,ha,phys⟩ := (RegistryMap.etr_iff_plan w).mp h
  obtain ⟨v,g,hv⟩ := CandidateTotal.exists_vertices eqs
  rw [RegistryMap.fromETR,RegistryMap.target_iff]
  exact ⟨eqs,v,g,parse,hv,GlobalShape.simple hv,
    Forward.forward hv ((CatalogRanks.compile_correct eqs).mp ⟨a,ha,phys⟩) WingCatalog.cat⟩

theorem etr_polyRed : PolyRed ETR AGPOrthBoundaryPoint :=
  ⟨RegistryMap.fromETR,RegistryMap.polynomial_time,fun w => ⟨forward_word w,ReductionSound.etr w⟩⟩

end ArtGallery.Orthogonal.BoundaryPoint.Main

namespace ArtGallery

/-- **The orthogonal boundary-point art gallery problem is `∃ℝ`-complete.** -/
theorem agpOrthBoundaryPoint_erComplete : ERComplete AGPOrthBoundaryPoint :=
  ERComplete.of_polyRed_ETR agpOrthBoundaryPoint_inER Orthogonal.BoundaryPoint.Main.etr_polyRed

end ArtGallery

end
