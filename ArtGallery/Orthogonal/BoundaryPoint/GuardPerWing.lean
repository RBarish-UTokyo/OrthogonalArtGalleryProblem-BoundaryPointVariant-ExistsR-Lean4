module

public import ArtGallery.Orthogonal.BoundaryPoint.GlobalPrivacy
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalMarks
public import ArtGallery.Vis.Pinning

/-! # An unconditional guard lower bound for the complete generated gallery
Each row supplies a marked target unseen from every other wing. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GuardPerWing
open Set PrivatePorts CatalogPlan CatalogRanks CompiledSize CompiledAddresses ChartDrawing WingMarks
open ContourJoin RectContour BankCoordinates ShapeRefs CorridorProgram

theorem catalogue : catalog.all (fun t => (refs t).2.any (fun r => r.length==6))=true := by decide +kernel

private theorem six {α : Type} (r : List α) (h : r.length=6) : ∃ c a b u v w,r=[c,a,b,u,v,w] := by
  rcases r with _|⟨c,r⟩; simp at h
  rcases r with _|⟨a,r⟩; simp at h
  rcases r with _|⟨b,r⟩; simp at h
  rcases r with _|⟨u,r⟩; simp at h
  rcases r with _|⟨v,r⟩; simp at h
  rcases r with _|⟨w,r⟩; simp at h
  have tail : r=[] := by simpa using h
  exact ⟨c,a,b,u,v,w,tail ▸ rfl⟩

private theorem role {t : Template} (h : (refs t).2.any (fun r => r.length==6)=true)
    (n j : Nat) (rs : List Nat) : ∃ c a b u v w, [c,a,b,u,v,w]∈GlobalPins.records t n j rs := by
  obtain ⟨r,hr,hlen⟩ := List.any_eq_true.mp h
  obtain ⟨c,a,b,u,v,w,rfl⟩ := six r (eq_of_beq hlen)
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
  change ∃ c a b u v w,[c,a,b,u,v,w]∈data.2
  let xs := MarginCert.execRat args [] (t.corridor.baseRows++t.corridor.rest)
  let f (p : Ref × Ref) : Vertex := (readRef xs t.room.x s p.1,readRef xs t.room.y s p.2)
  have eq : data.2=(refs t).2.map (List.map f) := (congrArg Prod.snd (ShapeRefs.coords t args s)).symm
  rw [eq]
  exact ⟨f c,f a,f b,f u,f v,f w,List.mem_map_of_mem hr⟩

private theorem row_exists (ts : List Template) (n j tag : Nat) (rs : List Nat)
    (safe : ts.all (fun t => (refs t).2.any (fun r => r.length==6))=true) (valid : tag<ts.length) :
    ∃ c a b u v w,[c,a,b,u,v,w]∈choose ts (fun t => GlobalPins.records t n j rs) tag [] := by
  induction ts generalizing tag with
  | nil => simp at valid
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true] at safe
    obtain ⟨first,tail⟩ := safe
    cases tag with
    | zero => exact role first n j rs
    | succ k => exact ih k tail (by simpa using valid)

private theorem marks (ts : List Template) (n j tag : Nat) (rs : List Nat) :
    choose ts (fun t => GlobalMarks.intervals t n j rs) tag [] =
      requests (choose ts (fun t => GlobalPins.records t n j rs) tag []) := by
  induction ts generalizing tag with
  | nil => rfl
  | cons t ts ih => cases tag with | zero => rfl | succ k => exact ih k

theorem target {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (emit : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g)) :
    ∃ w∈(Polygon.mk (v.map ratPoint)).filled,∀ z,(Polygon.mk (v.map ratPoint)).Sees z w →
      z∈(RealizedDoors.wing e).filled \ RealizedDoors.seam (scale eqs) j := by
  have tag := (CandidateTotal.valid_row (List.fst_mem_of_mem_zipIdx emit.1)).1
  obtain ⟨c,a,b,u,v₁,w,row⟩ := row_exists catalog (scale eqs) j r.1 r.2 catalogue tag
  refine ⟨HighStep.moved (door j) u,?_,fun z h => GlobalPrivacy.viewer emit out row (by simp) h⟩
  apply Jordan.boundary_subset_filled
  apply GlobalMarks.boundary emit out (ends:=(u,u)) _ (Geometry.left_mem_segment _ _)
  change (u,u)∈choose catalog _ r.1 []
  rw [marks]
  apply List.mem_flatMap.mpr
  exact ⟨_,row,by simp [perRole]⟩

private theorem placed {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat}
    (row : (r,j)∈(compile eqs).1.zipIdx) : ∃ e, WingSeparation.emitted eqs r j e := by
  have inPlan := List.fst_mem_of_mem_zipIdx row
  have ne : eqs≠[] := by intro h; subst eqs; exact (List.not_mem_nil (a:=(r,j))) row
  have h := CandidateTotal.valid_row inPlan
  obtain ⟨e,hit⟩ := Option.isSome_iff_exists.mp (CandidateTotal.safe (scale eqs) j r.1 r.2
    (scale_bounds ne).1 (program_door eqs row).le h.1 h.2 (fun _ h => (program_ranks eqs inPlan h).le))
  exact ⟨e,row,hit⟩

theorem count {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g)) (G : Finset Point)
    (cover : (Polygon.mk (v.map ratPoint)).IsGuardSetOnBoundary (G:Set Point)) :
    (compile eqs).1.length≤G.card := by
  let rows := (compile eqs).1
  let P : Polygon := ⟨v.map ratPoint⟩
  have loc (i : Fin rows.length) : (rows[i],(i:Nat))∈rows.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]; simp
  choose e he using fun i : Fin rows.length => placed (eqs:=eqs) (loc i)
  choose w hw force using fun i : Fin rows.length => target (he i) out
  have lb := P.card_le_of_witnesses_on cover.1 cover.2 w hw (by
    intro i j distinct z _ hit other
    have ne : (i:Nat)≠(j:Nat) := fun same => distinct (Fin.ext same)
    exact Set.disjoint_left.mp (WingSeparation.disjoint (he i) (he j) ne) (force i z hit).1 (force j z other).1)
  simpa only [Fintype.card_fin] using lb

theorem linear {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}
    (out : CandidateWord.vertices eqs=some (v,g)) (G : Finset Point)
    (cover : (Polygon.mk (v.map ratPoint)).IsGuardSetOnBoundary (G:Set Point)) :
    65*eqs.length≤G.card := (row_bounds eqs).1.trans (count out G cover)

end ArtGallery.Orthogonal.BoundaryPoint.GuardPerWing
end
