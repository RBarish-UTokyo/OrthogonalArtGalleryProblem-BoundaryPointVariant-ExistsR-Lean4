module

public import ArtGallery.Orthogonal.BoundaryPoint.WingMarkCatalogue

/-! # Every actual wing guard segment and its witnesses lie on the global boundary -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GlobalMarks
open WingMarkCatalogue WingMarks PlacedMarks CatalogPlan CatalogRanks CompiledSize
open CompiledAddresses ChartDrawing ContourJoin RectContour BankCoordinates Geometry Set

def intervals (t : Template) (n j : Nat) (rs : List Nat) : List (Vertex × Vertex) :=
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  requests ((t.corridor.coords args).2++(t.room.coords s).2)

def emitted (eqs : List ETRINV.Constraint) (r : CatalogPlan.Row) (j : Nat) :=
  choose catalog (fun t => intervals t (scale eqs) j r.2) r.1 []

private theorem straight (d : ℚ) (a b : Vertex) (t : ℝ) :
    move d (lerp (ratPoint a) (ratPoint b) t)=lerp (HighStep.moved d a) (HighStep.moved d b) t := by
  apply Prod.ext <;> simp [move,lerp,HighStep.moved,ratPoint] <;> ring

private theorem selected {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    (hn : 65≤scale eqs) (hj : j≤scale eqs) (hr : ∀ i∈r.2,i≤scale eqs)
    {ts : List Template} {ar : List Nat} (all : List.Forall₂ Safe ts ar) (tag : Nat)
    (arity : ar[tag]?=some r.2.length)
    (hit : (choose ts (fun t => drawOne t (scale eqs) j r.2) tag (none,0)).1=some e) {ends : Vertex × Vertex}
    (req : ends∈choose ts (fun t => intervals t (scale eqs) j r.2) tag []) :
    ArtGallery.segment (HighStep.moved (door j) ends.1) (HighStep.moved (door j) ends.2) ⊆
      (Polygon.mk (v.map ratPoint)).boundary := by
  induction all generalizing tag with
  | nil => simp at arity
  | @cons t n ts ar cert _ ih =>
    cases tag with
    | zero =>
      have size : r.2.length=n := by simpa using (Option.some.inj arity).symm
      have ⟨has,clear⟩ := cert r.2 size _ _ hn hj hr
      let s := (1:ℚ)/scale eqs
      let args := s::((j:ℚ)*s)::(r.2.map fun (i:Nat) => (i:ℚ)*s)
      let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
      change (atDoor (door j) (W (scale eqs)) (t.chart.draw data)).map (fun x => (door j,x))=some e at hit
      have used : ends∈requests data.2 := req
      obtain ⟨l,opened,eq⟩ := Option.map_eq_some_iff.mp hit
      have second : l=e.2 := congrArg Prod.snd eq
      rw [second] at opened
      intro z hz
      obtain ⟨u,hu,hU,rfl⟩ := mem_segment_iff_lerp.mp hz
      rw [←straight]
      have mark := lerp_mem_segment (ratPoint ends.1) (ratPoint ends.2) hu hU
      exact in_gallery path out opened (has ends used mark) (clear ends used _ mark)
    | succ k =>
      exact ih k (by simpa using arity) (by simpa [choose] using hit) (by simpa [choose] using req)

theorem boundary {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    {ends : Vertex × Vertex} (registered : ends∈emitted eqs r j) :
    ArtGallery.segment (HighStep.moved (door j) ends.1) (HighStep.moved (door j) ends.2) ⊆
      (Polygon.mk (v.map ratPoint)).boundary := by
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have member := List.fst_mem_of_mem_zipIdx path.1
  obtain ⟨valid,arity⟩ := CandidateTotal.valid_row member
  have sizes : WingSeparation.arities[r.1]?=some (profileBanks r.1).length := by
    generalize hi : r.1=i at valid ⊢; interval_cases i <;> rfl
  exact selected path out (scale_bounds ne).1 (program_door eqs path.1).le (fun i hi => (program_ranks eqs member hi).le)
    catalogue r.1 (arity ▸ sizes) path.2 registered

end ArtGallery.Orthogonal.BoundaryPoint.GlobalMarks
end
