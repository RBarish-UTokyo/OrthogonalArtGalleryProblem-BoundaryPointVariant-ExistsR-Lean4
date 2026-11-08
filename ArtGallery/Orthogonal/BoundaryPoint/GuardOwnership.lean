module

public import ArtGallery.Orthogonal.BoundaryPoint.BudgetCount

/-! # Guard ownership in the emitted gallery

For a nonempty source, every boundary guard set of the emitted polygon with the
emitted budget assigns one guard to every hub role (base slot, door step) and
every private role, the guard lies on the role's spot and is the only guard
seeing the role's anchor, and every guard belongs to some role. The only
hypothesis is the catalogue of same-wing separation certificates. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GuardOwnership
open HubOwners

theorem owned {ancs : List (List Nat)}
    (sepAll : ∀ tag t, ChartDrawing.catalog[tag]?=some t → ∀ a, WingSeparation.arities[tag]?=some a →
      RoleSeparation.Profile (ancs.getD tag []) t a)
    {eqs : List ETRINV.Constraint} (ne : eqs≠[]) {v : List RectContour.Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g))
    (G : Finset Point) (cover : (Polygon.mk (v.map ratPoint)).IsGuardSetOnBoundary (G:Set Point))
    (budget : G.card≤g) :
    let P := Polygon.mk (v.map ratPoint)
    let a := HubOwners.group eqs P
    let b := PrivateRoles.group eqs ancs
    G.card=g ∧
    (∀ i : HubRole eqs⊕PrivateRoles.Role eqs, ∃ p∈G, P.Sees p (Sum.elim a.mark b.mark i) ∧
      p∈Sum.elim a.spot b.spot i ∧ ∀ q∈G,P.Sees q (Sum.elim a.mark b.mark i) → q=p) ∧
    (∀ p∈G,∃ i : HubRole eqs⊕PrivateRoles.Role eqs,P.Sees p (Sum.elim a.mark b.mark i) ∧
      p∈Sum.elim a.spot b.spot i) := by
  have count := BudgetCount.card_eq ne out
  have r := PrivateRoles.owners sepAll out (OwnerAssembly.side ne out ancs) G cover (count ▸ budget)
  exact ⟨r.1.trans count,r.2⟩

end ArtGallery.Orthogonal.BoundaryPoint.GuardOwnership
end
