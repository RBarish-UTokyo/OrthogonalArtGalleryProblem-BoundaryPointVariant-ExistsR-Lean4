module

public import ArtGallery.Orthogonal.BoundaryPoint.SourceSplice

/-! # Identifying both sides of the global polygon decomposition -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.EmittedGallery
open Set RectContour CatalogPlan CompiledSize SourceEntrances SourceSplice ChartDrawing ContourJoin
open WingSeparation BankCoordinates WindowTree

def unionWings (eqs : List ETRINV.Constraint) : Set Point := {p | ∃ e∈wings eqs,p∈(RealizedDoors.wing e).filled}
def drawn (eqs : List ETRINV.Constraint) := EdgeSew.after [] (rows eqs)

theorem physical {eqs : List ETRINV.Constraint} (ne : eqs≠[]) {v g} (out : CandidateWord.vertices eqs=some (v,g)) :
    drawn eqs=⟨v.map ratPoint⟩ := by
  have nonempty : (compile eqs).1.isEmpty=false := by
    have m := List.length_pos_iff.mpr ne
    have lower := (row_bounds eqs).1
    exact List.isEmpty_eq_false_iff.mpr (List.length_pos_iff.mp (by omega))
  change ChartDrawing.vertices (compile eqs)=some (v,g) at out
  unfold ChartDrawing.vertices at out
  simp only [nonempty,Bool.false_eq_true,ite_false] at out
  split at out
  · obtain ⟨l,join,eq⟩ := Option.map_eq_some_iff.mp out
    obtain rfl : l=v := congrArg Prod.fst eq
    exact SourceSplice.output join
  · cases out

private theorem member {p : Point} (rs : List EdgeSew.Row) :
    p∈EdgeSew.added rs ↔ ∃r∈rs,p∈EdgeSew.part r := by
  induction rs with
  | nil => simp [EdgeSew.added]
  | cons r rs ih =>
    simp only [EdgeSew.added,Set.mem_union,ih]
    constructor
    · rintro (h|⟨s,hs,hp⟩)
      · exact ⟨r,List.mem_cons_self,h⟩
      · exact ⟨s,List.mem_cons_of_mem _ hs,hp⟩
    · rintro ⟨s,hs,hp⟩
      rcases List.mem_cons.mp hs with rfl|rest
      · exact Or.inl hp
      · exact Or.inr ⟨s,rest,hp⟩

theorem actual_row {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (path : emitted eqs r j e) :
    ∃ q∈rows eqs, q.path=e.2.map ratPoint := by
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have hn := (scale_bounds ne).1
  let edge := HubDoors.topEdge j
  have top : edge∈(List.range (compile eqs).1.length).map HubDoors.topEdge :=
    List.mem_map.mpr ⟨j,List.mem_range.mpr (List.mem_zipIdx' path.1).1,rfl⟩
  rw [←HubDoors.ceiling _ _ (PlacedSlots.starts eqs) hn] at top
  have he : edge∈edges eqs := List.mem_of_mem_filter top
  have adr := (placement path).1
  have act : e∈(wings eqs).filter (compat (W (scale eqs)) edge) := by
    apply List.mem_filter.mpr
    refine ⟨present.mpr ⟨r,j,path⟩,?_⟩
    have good := HubDoors.slot (scale eqs) j j hn e.2
    rw [←adr] at good
    simpa [edge] using good
  rcases one_or_none he with empty|⟨f,only,_,_⟩
  · rw [empty] at act; contradiction
  rw [only] at act
  obtain rfl := List.mem_singleton.mp act
  refine ⟨row eqs edge,List.mem_map.mpr ⟨edge,he,rfl⟩,?_⟩
  simp [row,only]

theorem union_eq {eqs : List ETRINV.Constraint} (all : SimpleWings eqs) :
    EdgeSew.added (rows eqs)=unionWings eqs := by
  ext p
  rw [member]
  constructor
  · rintro ⟨q,hq,hp⟩
    obtain ⟨edge,he,rfl⟩ := List.mem_map.mp hq
    rcases one_or_none he with empty|⟨e,only,mem,_⟩
    · simp [row,EdgeSew.part,empty] at hp
    · by_cases no : e.2=[]
      · simp [row,EdgeSew.part,only,no] at hp
      · exact ⟨e,mem,by simpa [RealizedDoors.wing,EdgeSew.part,EdgeSew.wing,row,only,no] using hp⟩
  · rintro ⟨e,mem,hp⟩
    obtain ⟨r,j,path⟩ := present.mp mem
    obtain ⟨q,hq,matchPath⟩ := actual_row path
    have length := (all r j e path).1
    have nonempty : e.2≠[] := by
      change 3≤(e.2.map ratPoint).length at length; intro empty; simp [empty] at length
    refine ⟨q,hq,?_⟩
    simpa [EdgeSew.part,EdgeSew.wing,matchPath,nonempty,RealizedDoors.wing] using hp

structure Shape (eqs : List ETRINV.Constraint) (P : Polygon) : Prop where
  simple : P.Simple
  filled : P.filled=(RealizedDoors.hub eqs).filled∪unionWings eqs
  from_hub : Attachments (RealizedDoors.hub eqs).filled P.filled
  from_wing : ∀ r j e,emitted eqs r j e → Attachments (RealizedDoors.wing e).filled P.filled

theorem of_splice {eqs : List ETRINV.Constraint} (ne : eqs≠[]) (all : SimpleWings eqs) {v g}
    (out : CandidateWord.vertices eqs=some (v,g)) : Shape eqs ⟨v.map ratPoint⟩ := by
  rw [←physical ne out]
  obtain ⟨simple,filled,hub,leaves⟩ := assembly ne all
  rw [base,union_eq all] at filled
  rw [base] at hub
  refine ⟨simple,filled,hub,?_⟩
  intro r j e path
  obtain ⟨q,mem,hq⟩ := actual_row path
  have len := (all r j e path).1
  have nonempty : q.path≠[] := by
    change 3≤(e.2.map ratPoint).length at len
    rw [←hq] at len
    intro empty; simp [empty] at len
  simpa [drawn,EdgeSew.wing,RealizedDoors.wing,hq] using leaves q mem nonempty

end ArtGallery.Orthogonal.BoundaryPoint.EmittedGallery
end
