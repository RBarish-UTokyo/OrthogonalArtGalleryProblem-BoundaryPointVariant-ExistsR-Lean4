module

public import ArtGallery.Orthogonal.BoundaryPoint.GlobalShape
public import ArtGallery.Orthogonal.BoundaryPoint.RoomAttachment

/-! # Boundary eligibility survives the full join away from the doors -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GalleryBoundary
open Set RectContour CatalogPlan CompiledSize ContourJoin WingSeparation SourceEntrances EmittedGallery

theorem closed_union (ws : List Entrance) (P : Entrance → Prop) :
    IsClosed {q : Point | ∃ e∈ws,P e ∧ q∈(RealizedDoors.wing e).filled} := by
  induction ws with
  | nil => simpa using isClosed_empty (X:=Point)
  | cons a ws ih =>
    by_cases ha : P a
    · have eq : {q : Point | ∃ e∈a::ws,P e ∧ q∈(RealizedDoors.wing e).filled} =
        (RealizedDoors.wing a).filled∪{q | ∃ e∈ws,P e ∧ q∈(RealizedDoors.wing e).filled} := by
        ext q; simp [ha]
      rw [eq]; exact (Jordan.isClosed_filled _).union ih
    · convert ih using 1; ext q; simp [ha]

theorem same_at_index {eqs : List ETRINV.Constraint} {r s : CatalogPlan.Row} {j : Nat} {a b : Entrance}
    (ha : emitted eqs r j a) (hb : emitted eqs s j b) : a=b := by
  have h₁ := (List.mem_zipIdx' ha.1).2
  have h₂ := (List.mem_zipIdx' hb.1).2
  have same : r=s := h₁.trans h₂.symm
  subst s
  exact Option.some.inj (ha.2.symm.trans hb.2)

noncomputable def joined {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    : RoomAttachment.Joined (Polygon.mk (v.map ratPoint)) (RealizedDoors.wing e)
      ((BankCoordinates.door j:ℝ),1) ((BankCoordinates.door j:ℝ)+(BankCoordinates.W (scale eqs):ℝ),1) := by
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  let H := (RealizedDoors.hub eqs).filled
  let W := (RealizedDoors.wing e).filled
  let others : Set Point := {q | ∃ a∈wings eqs,a≠e ∧ q∈(RealizedDoors.wing a).filled}
  let P : Polygon := ⟨v.map ratPoint⟩
  obtain shape := GlobalShape.decomposition ne out
  have member := present.mpr ⟨r,j,path⟩
  have split : unionWings eqs=W∪others := by
    ext q; constructor
    · rintro ⟨a,ha,hq⟩
      by_cases same : a=e
      · subst a; exact Or.inl hq
      · exact Or.inr ⟨a,ha,same,hq⟩
    · rintro (atE|⟨a,ha,_,hq⟩)
      · exact ⟨e,member,atE⟩
      · exact ⟨a,ha,hq⟩
  have total : P.filled=W∪(H∪others) := by
    rw [show P.filled=H∪unionWings eqs from shape.filled,split,Set.union_left_comm]
  refine ⟨H∪others,(Jordan.isClosed_filled _).union (closed_union (wings eqs) (·≠e)),total,?_⟩
  change W∩(H∪others)=RealizedDoors.seam (scale eqs) j
  rw [←RealizedDoors.intersection path]
  ext p
  constructor
  · rintro ⟨inside,inHub|⟨a,ha,diff,overlap⟩⟩
    · exact ⟨inHub,inside⟩
    · obtain ⟨s,k,other⟩ := present.mp ha
      have neq : k≠j := by intro k_eq; subst k; exact diff (same_at_index other path)
      exact (Set.disjoint_left.mp (WingSeparation.disjoint other path neq) overlap inside).elim
  · exact fun h => ⟨h.2,Or.inl h.1⟩

theorem wing_iff {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    {p : Point} (inside : p∈(RealizedDoors.wing e).filled) (off : p∉RealizedDoors.seam (scale eqs) j) :
    p∈(Polygon.mk (v.map ratPoint)).boundary ↔ p∈(RealizedDoors.wing e).boundary := by
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  let d := joined path out
  have shape := GlobalShape.decomposition ne out
  have localSimple := RealizedWings.simple path
  constructor
  · exact fun h => WindowBoundary.restrict_guard localSimple shape.simple (shape.from_wing r j e path).subset h inside
  · intro h
    refine WindowBoundary.extend_guard localSimple shape.simple d.fill d.closed h ?_
    intro hr
    apply off
    change p∈ArtGallery.segment _ _
    rw [←d.contact]
    exact ⟨inside,hr⟩

theorem hub_iff {eqs : List ETRINV.Constraint} (ne : eqs≠[]) {v g}
    (out : CandidateWord.vertices eqs=some (v,g)) {p : Point} (inside : p∈(RealizedDoors.hub eqs).filled)
    (off : ∀ r j e,emitted eqs r j e → p∉RealizedDoors.seam (scale eqs) j) :
    p∈(Polygon.mk (v.map ratPoint)).boundary ↔ p∈(RealizedDoors.hub eqs).boundary := by
  have shape := GlobalShape.decomposition ne out
  have hub := RealizedHub.production ne
  constructor
  · exact fun h => WindowBoundary.restrict_guard hub shape.simple shape.from_hub.subset h inside
  · intro h
    refine WindowBoundary.extend_guard hub shape.simple shape.filled ?_ h ?_
    · simpa only [unionWings,true_and] using closed_union (wings eqs) (fun _ => True)
    · rintro ⟨e,mem,hit⟩
      obtain ⟨r,j,path⟩ := present.mp mem
      apply off r j e path
      rw [←RealizedDoors.intersection path]; exact ⟨inside,hit⟩

end ArtGallery.Orthogonal.BoundaryPoint.GalleryBoundary
end
