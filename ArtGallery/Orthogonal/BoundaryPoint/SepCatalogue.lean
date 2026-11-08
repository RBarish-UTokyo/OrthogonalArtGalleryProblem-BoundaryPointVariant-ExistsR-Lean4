module

public import ArtGallery.Orthogonal.BoundaryPoint.GuardOwnership
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_40_200

/-! # The catalogue of same-wing separation certificates

The fourteen profile certificates discharge the separation hypothesis of guard
ownership, so every boundary guard set within the budget is owned role by role. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SepCatalogue

/-- The anchor cells of the private roles, profile by profile. -/
def anchors : List (List Nat) := [
  SepData.Ordinary_40_200_520.anchors,
  SepData.Shifted_40_200_520.anchors,
  SepData.Lower_40_200_1000.anchors,
  SepData.Lower_10_40_1000.anchors,
  SepData.Lower_10_200_1000.anchors,
  SepData.Lower_10_360_1000.anchors,
  SepData.Lower_10_520_1000.anchors,
  SepData.InvLe_1_40.anchors,
  SepData.InvLe_1_200.anchors,
  SepData.InvLe_1_360.anchors,
  SepData.InvLe_1_520.anchors,
  SepData.InvRevGe_1_10.anchors,
  SepData.InvLe_40_200.anchors,
  SepData.InvRevGe_40_200.anchors]

theorem sepAll : ∀ tag t, ChartDrawing.catalog[tag]?=some t → ∀ a, WingSeparation.arities[tag]?=some a →
    RoleSeparation.Profile (anchors.getD tag []) t a := by
  intro tag t ht a ha
  have hl : tag<14 := by
    have := (List.getElem?_eq_some_iff.mp ha).1; simpa [WingSeparation.arities] using this
  interval_cases tag <;> simp only [ChartDrawing.catalog,WingSeparation.arities,List.getElem?_cons_succ,
    List.getElem?_cons_zero,Option.some.injEq] at ht ha <;> subst ht ha
  · exact SepData.Ordinary_40_200_520.profile
  · exact SepData.Shifted_40_200_520.profile
  · exact SepData.Lower_40_200_1000.profile
  · exact SepData.Lower_10_40_1000.profile
  · exact SepData.Lower_10_200_1000.profile
  · exact SepData.Lower_10_360_1000.profile
  · exact SepData.Lower_10_520_1000.profile
  · exact SepData.InvLe_1_40.profile
  · exact SepData.InvLe_1_200.profile
  · exact SepData.InvLe_1_360.profile
  · exact SepData.InvLe_1_520.profile
  · exact SepData.InvRevGe_1_10.profile
  · exact SepData.InvLe_40_200.profile
  · exact SepData.InvRevGe_40_200.profile

/-- Guard ownership in the emitted gallery, with the separation catalogue discharged. -/
theorem owned {eqs : List ETRINV.Constraint} (ne : eqs≠[]) {v : List RectContour.Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g))
    (G : Finset Point) (cover : (Polygon.mk (v.map ratPoint)).IsGuardSetOnBoundary (G:Set Point))
    (budget : G.card≤g) :
    let P := Polygon.mk (v.map ratPoint)
    let a := HubOwners.group eqs P
    let b := PrivateRoles.group eqs anchors
    G.card=g ∧
    (∀ i : HubOwners.HubRole eqs⊕PrivateRoles.Role eqs, ∃ p∈G, P.Sees p (Sum.elim a.mark b.mark i) ∧
      p∈Sum.elim a.spot b.spot i ∧ ∀ q∈G,P.Sees q (Sum.elim a.mark b.mark i) → q=p) ∧
    (∀ p∈G,∃ i : HubOwners.HubRole eqs⊕PrivateRoles.Role eqs,P.Sees p (Sum.elim a.mark b.mark i) ∧
      p∈Sum.elim a.spot b.spot i) :=
  GuardOwnership.owned sepAll ne out G cover budget

end ArtGallery.Orthogonal.BoundaryPoint.SepCatalogue
end
