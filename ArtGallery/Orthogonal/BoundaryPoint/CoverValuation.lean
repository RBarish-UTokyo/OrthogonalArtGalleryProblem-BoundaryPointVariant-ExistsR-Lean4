module

public import ArtGallery.Orthogonal.BoundaryPoint.SepCatalogue
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvRevGe_40_200

/-! # A boundary cover within the budget yields a satisfying assignment

Every guard set on the boundary of the emitted polygon that sees the whole closed polygon and
has at most the budgeted number of guards owns every role (`SepCatalogue.owned`). The values
read from the owners of the hub slots lie in `[1/2,2]` and satisfy the relation of every
compiled row (`RowValue.<P>.row`), hence the source constraints. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CoverValuation
open CatalogPlan CatalogRanks HubOwners ValueChain

theorem satisfiable {eqs : List ETRINV.Constraint} (ne : eqs≠[]) {v : List RectContour.Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g)) (G : Finset Point)
    (cover : (Polygon.mk (v.map ratPoint)).IsGuardSetOnBoundary (G:Set Point)) (budget : G.card≤g) :
    ETRINV.Satisfiable eqs := by
  obtain ⟨-,hall,hevery⟩ := SepCatalogue.owned ne out G cover budget
  let ownerB := fun (k : Fin (slots eqs).length) => Classical.choose (hall (.inl (.inl k)))
  have hspot (k : Fin (slots eqs).length) : ((sx eqs k:ℚ):ℝ)≤(ownerB k).1 ∧ (ownerB k).1≤((sx eqs k:ℚ):ℝ)+3/2 := by
    show ((sx eqs k:ℚ):ℝ)≤(Classical.choose (hall (.inl (.inl k)))).1 ∧
      (Classical.choose (hall (.inl (.inl k)))).1≤((sx eqs k:ℚ):ℝ)+3/2
    have sp := (Classical.choose_spec (hall (.inl (.inl k)))).2.2.1
    generalize Classical.choose (hall (.inl (.inl k)))=p at sp ⊢
    simp only [Sum.elim_inl,HubOwners.group,HubOwners.lo,HubOwners.hi] at sp
    obtain ⟨-,a,b⟩ := sp; exact ⟨a,by push_cast at b ⊢; linarith⟩
  apply (compile_correct eqs).mp
  refine ⟨value ownerB,fun a => value_range ownerB hspot a,?_⟩
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hr
  have tag := (CandidateTotal.valid_row hr).1
  let fi : Fin (PrivateRoles.rows eqs).length := ⟨i,hi⟩
  have e : (compile eqs).1[i]=(PrivateRoles.rows eqs)[fi] := rfl
  rw [e]
  rw [e] at tag
  generalize ht : ((PrivateRoles.rows eqs)[fi]).1=k at tag ⊢
  interval_cases k
  · exact RowValue.Ordinary_40_200_520.row ne out _ G cover hall hevery fi ht
  · exact RowValue.Shifted_40_200_520.row ne out _ G cover hall hevery fi ht
  · exact RowValue.Lower_40_200_1000.row ne out _ G cover hall hevery fi ht
  · exact RowValue.Lower_10_40_1000.row ne out _ G cover hall hevery fi ht
  · exact RowValue.Lower_10_200_1000.row ne out _ G cover hall hevery fi ht
  · exact RowValue.Lower_10_360_1000.row ne out _ G cover hall hevery fi ht
  · exact RowValue.Lower_10_520_1000.row ne out _ G cover hall hevery fi ht
  · exact RowValue.InvLe_1_40.row ne out _ G cover hall hevery fi ht
  · exact RowValue.InvLe_1_200.row ne out _ G cover hall hevery fi ht
  · exact RowValue.InvLe_1_360.row ne out _ G cover hall hevery fi ht
  · exact RowValue.InvLe_1_520.row ne out _ G cover hall hevery fi ht
  · exact RowValue.InvRevGe_1_10.row ne out _ G cover hall hevery fi ht
  · exact RowValue.InvLe_40_200.row ne out _ G cover hall hevery fi ht
  · exact RowValue.InvRevGe_40_200.row ne out _ G cover hall hevery fi ht

end ArtGallery.Orthogonal.BoundaryPoint.CoverValuation
end
