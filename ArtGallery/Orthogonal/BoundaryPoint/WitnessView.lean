module

public import ArtGallery.Orthogonal.BoundaryPoint.PinTransport
public import ArtGallery.Orthogonal.BoundaryPoint.WingPrivacy

/-! # A viewer of one private witness must lie behind its own door -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WitnessView
open Set CatalogPlan ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport
open ShapeRefs WingMarks Geometry Hardening.Invariance

theorem unshift_door {eqs : List ETRINV.Constraint} {j : Nat} {q : Point} (hq : q∈RealizedDoors.seam (scale eqs) j) :
    PortalGate.Door (((1:ℚ)/(scale eqs:ℚ)):ℝ) ((shift (door j)).symm q) := by
  let A := shift (door j)
  let x := A.symm q
  have same : A x=q := A.apply_symm_apply _
  obtain ⟨v,hv,hV,ev⟩ := hq
  have h1 := congrArg Prod.fst (ev.symm.trans same.symm)
  have h2 := congrArg Prod.snd (ev.symm.trans same.symm)
  simp only [A,shift_pt,sub_self,mul_zero,add_zero,add_sub_cancel_left] at h1 h2
  have width : (W (scale eqs):ℝ)=(((1:ℚ)/(scale eqs:ℚ)):ℝ)/320 := by simp [W]; ring
  have pos : 0≤(W (scale eqs):ℝ) := by unfold W; positivity
  change 0≤x.1 ∧ x.1≤_ ∧ x.2=1
  refine ⟨by linarith [mul_nonneg hv pos],?_,h2.symm⟩
  rw [←width]; linarith [mul_le_mul_of_nonneg_right hV pos]

theorem behind {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {vs g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (vs,g))
    {l : List Vertex} (opened : atDoor (door j) (W (scale eqs)) l=some e.2)
    (w : Vertex) (inside : ratPoint w∈(Polygon.mk (l.map ratPoint)).filled)
    (dark : ∀ q,PortalGate.Door (((1:ℚ)/(scale eqs:ℚ)):ℝ) q → ¬(Polygon.mk (l.map ratPoint)).Sees (ratPoint w) q)
    {z : Point} (seen : (Polygon.mk (vs.map ratPoint)).Sees z (HighStep.moved (door j) w)) :
    z∈(RealizedDoors.wing e).filled \ RealizedDoors.seam (scale eqs) j := by
  let A := shift (door j)
  let L : Polygon := ⟨l.map ratPoint⟩
  let R := RealizedDoors.wing e
  obtain ⟨k,rot⟩ := placed opened
  change R=(mapPoly A L).rotate k at rot
  have fill : R.filled=A '' L.filled := by rw [rot,Existence.filled_rotate,filled_mapPoly]
  let join := GalleryBoundary.joined path out
  have rloc := join.local_view (g:=z) (w:=A (ratPoint w)) (fill ▸ Set.mem_image_of_mem _ inside)
  have missed : ∀ q∈RealizedDoors.seam (scale eqs) j,¬R.Sees (A (ratPoint w)) q := by
    intro q hq sight
    let x := A.symm q
    have same : A x=q := A.apply_symm_apply q
    apply dark x (unshift_door hq)
    change ArtGallery.segment (A (ratPoint w)) q ⊆ R.filled at sight
    rwa [←same,fill,←image_segment',Set.image_subset_image_iff A.injective] at sight
  have zview := rloc missed (by simpa only [A,shift_vertex] using seen)
  refine ⟨zview.1,?_⟩
  intro atDoor
  apply zview.2.1
  have inter : z∈R.filled∩join.rest := by rw [join.contact]; exact atDoor
  exact inter.2

theorem from_role {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {vs g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (vs,g))
    {t : Template} {args : List ℚ} (reciprocal : MarginCert.getRat args 0=1/(scale eqs:ℚ))
    (eligible : WingMarks.Holds t args) (hidden : WingPrivacy.AllHidden t args)
    (opened : atDoor (door j) (W (scale eqs))
      (t.chart.draw (ShapeRefs.join (t.corridor.coords args) (t.room.coords (MarginCert.getRat args 0))))=some e.2)
    {c a b u v w : Vertex} (role : [c,a,b,u,v,w]∈(t.corridor.coords args).2++(t.room.coords (MarginCert.getRat args 0)).2)
    {h : Vertex} (hh : h∈[u,v,w]) {z : Point}
    (sight : (Polygon.mk (vs.map ratPoint)).Sees z (HighStep.moved (door j) h)) :
    z∈(RealizedDoors.wing e).filled \ RealizedDoors.seam (scale eqs) j := by
  apply behind path out opened h _ _ sight
  · apply Jordan.boundary_subset_filled
    apply eligible (h,h) _ (Geometry.left_mem_segment _ _)
    apply List.mem_flatMap.mpr
    refine ⟨[c,a,b,u,v,w],role,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl <;> simp [WingMarks.perRole]
  · intro q hq
    apply hidden _ role _ hh q
    simpa only [reciprocal,Rat.cast_div] using hq

end ArtGallery.Orthogonal.BoundaryPoint.WitnessView
end
