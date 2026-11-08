module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEscape
public import ArtGallery.Orthogonal.BoundaryPoint.WingPinProof
public import ArtGallery.Orthogonal.BoundaryPoint.PlacedMarks
public import ArtGallery.Vis.CertCheckerTransfer

/-! # A single viewer of a registered triple in the joined gallery -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PinTransport
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize
open ShapeRefs WingMarks PlacedMarks Geometry Hardening.Invariance

noncomputable def shift (d : ℚ) : Point ≃ᵃ[ℝ] Point := AffineEquiv.constVAdd ℝ Point ((d:ℝ),0)

theorem shift_pt (d : ℚ) (p : Point) : shift d p=(p.1+(d:ℝ),p.2) := by
  change ((d:ℝ)+p.1,0+p.2)=(p.1+d,p.2)
  simp [add_comm]

theorem shift_vertex (d : ℚ) (a : Vertex) : shift d (ratPoint a)=HighStep.moved d a := by
  simp [shift_pt,HighStep.moved,ratPoint]

theorem placed {l path : List Vertex} {d w : ℚ} (opened : atDoor d w l=some path) :
    ∃ k, Polygon.mk (path.map ratPoint)=(mapPoly (shift d) ⟨l.map ratPoint⟩).rotate k := by
  let i := l.idxOf (0,1)
  unfold atDoor at opened; dsimp only at opened
  split at opened
  · contradiction
  next good =>
    have bounded : i+1≤l.length := by
      have h : ¬(i≥l.length ∨ (l.getD ((i+1)%l.length) (0,0) != (w,1))=true) := by
        simpa only [i,Bool.or_eq_true,decide_eq_true_eq] using good
      omega
    obtain rfl := Option.some.inj opened
    refine ⟨i+1,?_⟩
    change Polygon.mk (((l.drop (i+1)++l.take (i+1)).map _).map ratPoint)=_
    rw [←List.rotate_eq_drop_append_take bounded,List.map_map]
    change Polygon.mk ((l.rotate (i+1)).map (HighStep.moved d))=_
    have eq : (shift d ∘ ratPoint)=HighStep.moved d := funext (shift_vertex d)
    rw [List.map_rotate,InsideDoor.rotate_list]
    simp only [mapPoly,List.map_map,eq]

theorem localize {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {vs g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (vs,g))
    {t : Template} {args : List ℚ} (reciprocal : MarginCert.getRat args 0=1/(scale eqs:ℚ))
    (eligible : WingMarks.Holds t args) (hidden : WingEscape.Hidden t args) (forces : WingPinProof.Forces t args)
    (opened : atDoor (door j) (W (scale eqs))
      (t.chart.draw (ShapeRefs.join (t.corridor.coords args) (t.room.coords (MarginCert.getRat args 0))))=some e.2)
    {c a b u v w : Vertex} (role : [c,a,b,u,v,w]∈(t.corridor.coords args).2++(t.room.coords (MarginCert.getRat args 0)).2)
    {z : Point} (bd : z∈(Polygon.mk (vs.map ratPoint)).boundary)
    (seen : ∀ h∈[u,v,w],(Polygon.mk (vs.map ratPoint)).Sees z (HighStep.moved (door j) h)) :
    z∈ArtGallery.segment (HighStep.moved (door j) a) (HighStep.moved (door j) b) := by
  let d := door j
  let s := MarginCert.getRat args 0
  let A := shift d
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
  let L := BoundaryChart.actual t.chart data
  let R := RealizedDoors.wing e
  let P := Polygon.mk (vs.map ratPoint)
  have member : [c,a,b,u,v,w]∈data.2 := role
  obtain ⟨k,rot⟩ := placed opened
  change R=(mapPoly A L).rotate k at rot
  have filled : R.filled=A '' L.filled := by rw [rot,Existence.filled_rotate,filled_mapPoly]
  have boundary : R.boundary=A '' L.boundary := by rw [rot,Existence.boundary_rotate,boundary_mapPoly]
  have sees (i h : Point) : R.Sees (A i) (A h) ↔ L.Sees i h := by
    change ArtGallery.segment (A i) (A h) ⊆ R.filled ↔ ArtGallery.segment i h ⊆ L.filled
    rw [filled,←image_segment',Set.image_subset_image_iff A.injective]
  have at_vertex (h : Vertex) : A (ratPoint h)=HighStep.moved d h := shift_vertex _ _
  have inside (h : Vertex) (hit : h∈[u,v,w]) : ratPoint h∈L.filled := by
    apply Jordan.boundary_subset_filled
    apply eligible (h,h) _ (Geometry.left_mem_segment _ _)
    apply List.mem_flatMap.mpr
    refine ⟨[c,a,b,u,v,w],member,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with rfl|rfl|rfl <;> simp [WingMarks.perRole]
  let join := GalleryBoundary.joined path out
  obtain ⟨p,inList,dark⟩ := hidden _ member
  have wit : p∈[u,v,w] := inList
  have source : A (ratPoint p)∈R.filled := filled ▸ Set.mem_image_of_mem _ (inside p wit)
  have vis : P.Sees z (A (ratPoint p)) := by rw [at_vertex]; exact seen p wit
  have miss : ∀ q∈RealizedDoors.seam (scale eqs) j,¬R.Sees (A (ratPoint p)) q := by
    intro q inSeam sight
    let x := A.symm q
    have eqx : A x=q := A.apply_symm_apply q
    apply dark x ?_ ((sees _ _).mp (by rwa [eqx]))
    obtain ⟨v,hv,hV,ev⟩ := inSeam
    have h1 := congrArg Prod.fst (ev.symm.trans eqx.symm)
    have h2 := congrArg Prod.snd (ev.symm.trans eqx.symm)
    simp only [A,d,shift_pt,sub_self,mul_zero,add_zero,add_sub_cancel_left] at h1 h2
    have ident : (W (scale eqs):ℝ)=(s:ℝ)/320 := by
      dsimp only [s]; rw [reciprocal]; simp [W]; ring
    have sign : 0≤(W (scale eqs):ℝ) := by unfold W; positivity
    refine ⟨?_,?_,?_⟩
    · linarith [mul_nonneg hv sign]
    · rw [←ident]; linarith [mul_le_mul_of_nonneg_right hV sign]
    · exact h2.symm
  have confined := join.local_view source miss vis
  have ne : eqs≠[] := by intro h; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have gallery := GlobalShape.decomposition ne out
  have tree := gallery.from_wing r j e path
  have rb : z∈R.boundary := WindowBoundary.restrict_guard (RealizedWings.simple path) gallery.simple tree.subset bd confined.1
  rw [boundary] at rb
  obtain ⟨y,hy,rfl⟩ := rb
  have localSight (h : Vertex) (hh : h∈[u,v,w]) : L.Sees y (ratPoint h) := by
    apply (sees _ _).mp
    apply (tree.sees_iff confined.1 (filled ▸ Set.mem_image_of_mem _ (inside h hh))).mp
    rw [at_vertex]; exact seen h hh
  have onSpot := forces c a b u v w member y hy (localSight u (by simp)) (localSight v (by simp)) (localSight w (by simp))
  rw [←at_vertex,←at_vertex,←image_segment']
  exact Set.mem_image_of_mem _ onSpot

end ArtGallery.Orthogonal.BoundaryPoint.PinTransport
end
