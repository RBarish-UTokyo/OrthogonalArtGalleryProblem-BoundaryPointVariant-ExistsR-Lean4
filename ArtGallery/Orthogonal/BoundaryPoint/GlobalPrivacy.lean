module

public import ArtGallery.Orthogonal.BoundaryPoint.GlobalPins
public import ArtGallery.Orthogonal.BoundaryPoint.PrivacyCatalogue
public import ArtGallery.Orthogonal.BoundaryPoint.WitnessView

/-! # Any viewer of a private witness is in its own wing and off the closed hub door -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GlobalPrivacy
open PrivacyCatalogue CatalogPlan CatalogRanks CompiledSize CompiledAddresses ChartDrawing
open ContourJoin RectContour BankCoordinates

private theorem selected {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    (hn : 65≤scale eqs) (hj : j≤scale eqs) (hr : ∀ i∈r.2,i≤scale eqs)
    {ts : List Template} {ar : List Nat} (all : List.Forall₂ Profile ts ar) (tag : Nat)
    (arity : ar[tag]?=some r.2.length)
    (hit : (choose ts (fun t => drawOne t (scale eqs) j r.2) tag (none,0)).1=some e)
    {c a b u v₁ w : Vertex} (row : [c,a,b,u,v₁,w]∈choose ts (fun t => GlobalPins.records t (scale eqs) j r.2) tag [])
    {h : Vertex} (witness : h∈[u,v₁,w]) {z : Point}
    (seen : (Polygon.mk (v.map ratPoint)).Sees z (HighStep.moved (door j) h)) :
    z∈(RealizedDoors.wing e).filled \ RealizedDoors.seam (scale eqs) j := by
  induction all generalizing tag with
  | nil => simp at arity
  | @cons t n ts ar cert _ ih =>
    cases tag with
    | zero =>
      have size : r.2.length=n := by simpa using (Option.some.inj arity).symm
      have ⟨marked,hidden⟩ := cert r.2 size _ _ hn hj hr
      let s := (1:ℚ)/scale eqs
      let args := s::((j:ℚ)*s)::(r.2.map fun (i:Nat) => (i:ℚ)*s)
      let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
      change (atDoor (door j) (W (scale eqs)) (t.chart.draw data)).map (fun x => (door j,x))=some e at hit
      obtain ⟨l,opened,eq⟩ := Option.map_eq_some_iff.mp hit
      rw [show l=e.2 from congrArg Prod.snd eq] at opened
      exact WitnessView.from_role path out (args:=args) rfl marked hidden opened row witness seen
    | succ k => exact ih k (by simpa using arity) (by simpa [choose] using hit) (by simpa [choose] using row)

theorem viewer {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    {c a b u v₁ w : Vertex} (row : [c,a,b,u,v₁,w]∈GlobalPins.emitted eqs r j)
    {h : Vertex} (witness : h∈[u,v₁,w]) {z : Point}
    (seen : (Polygon.mk (v.map ratPoint)).Sees z (HighStep.moved (door j) h)) :
    z∈(RealizedDoors.wing e).filled \ RealizedDoors.seam (scale eqs) j := by
  have ne : eqs≠[] := by intro h; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have member := List.fst_mem_of_mem_zipIdx path.1
  obtain ⟨valid,arity⟩ := CandidateTotal.valid_row member
  have sizes : WingSeparation.arities[r.1]?=some (profileBanks r.1).length := by
    generalize hi : r.1=i at valid ⊢; interval_cases i <;> rfl
  exact selected path out (scale_bounds ne).1 (program_door eqs path.1).le (fun i hi => (program_ranks eqs member hi).le)
    catalogue r.1 (arity ▸ sizes) path.2 row witness seen

end ArtGallery.Orthogonal.BoundaryPoint.GlobalPrivacy
end
