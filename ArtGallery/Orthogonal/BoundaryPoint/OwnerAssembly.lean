module

public import ArtGallery.Orthogonal.BoundaryPoint.HubOwners
public import ArtGallery.Orthogonal.BoundaryPoint.PrivateRoles

/-! # Hub facts of the emitted gallery

Private role spots lie in their own wings. Together with the hub witness bands
this proves every field of `PrivateRoles.HubSide` for the hub roles of
`HubOwners`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.OwnerAssembly
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize CatalogPlan CatalogRanks CompiledAddresses
open ShapeRefs WingMarks PinTransport Geometry Hardening.Invariance HubOwners HubRoles

private theorem spot_local {eqs : List ETRINV.Constraint} {j : Nat} {e : Entrance}
    {t : Template} {args : List ℚ} (eligible : WingMarks.Holds t args)
    (opened : atDoor (door j) (W (scale eqs))
      (t.chart.draw (ShapeRefs.join (t.corridor.coords args) (t.room.coords (MarginCert.getRat args 0))))=some e.2)
    {c a b u v w : Vertex} (role : [c,a,b,u,v,w]∈(t.corridor.coords args).2++(t.room.coords (MarginCert.getRat args 0)).2) :
    ArtGallery.segment (HighStep.moved (door j) a) (HighStep.moved (door j) b)⊆(RealizedDoors.wing e).filled := by
  let A := shift (door j)
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (MarginCert.getRat args 0))
  let L := BoundaryChart.actual t.chart data
  obtain ⟨k,rot⟩ := placed opened
  change RealizedDoors.wing e=(mapPoly A L).rotate k at rot
  have filled : (RealizedDoors.wing e).filled=A '' L.filled := by rw [rot,Existence.filled_rotate,filled_mapPoly]
  have local_ : ArtGallery.segment (ratPoint a) (ratPoint b)⊆L.filled := by
    intro z hz
    apply Jordan.boundary_subset_filled
    apply eligible (a,b) _ hz
    exact List.mem_flatMap.mpr ⟨[c,a,b,u,v,w],role,by simp [WingMarks.perRole]⟩
  rw [filled,←shift_vertex,←shift_vertex,←image_segment']
  exact Set.image_mono local_

private theorem selected {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (hn : 65≤scale eqs) (hj : j≤scale eqs) (hr : ∀ i∈r.2,i≤scale eqs)
    {ts : List Template} {ar : List Nat} (all : List.Forall₂ PrivacyCatalogue.Profile ts ar) (tag : Nat)
    (arity : ar[tag]?=some r.2.length)
    (hit : (choose ts (fun t => drawOne t (scale eqs) j r.2) tag (none,0)).1=some e)
    {c a b u v w : Vertex} (row : [c,a,b,u,v,w]∈choose ts (fun t => GlobalPins.records t (scale eqs) j r.2) tag []) :
    ArtGallery.segment (HighStep.moved (door j) a) (HighStep.moved (door j) b)⊆(RealizedDoors.wing e).filled := by
  induction all generalizing tag with
  | nil => simp at arity
  | @cons t n ts ar cert _ ih =>
    cases tag with
    | zero =>
      have size : r.2.length=n := by simpa using (Option.some.inj arity).symm
      have ⟨marked,_⟩ := cert r.2 size _ _ hn hj hr
      change (atDoor (door j) (W (scale eqs)) (t.chart.draw _)).map (fun x => (door j,x))=some e at hit
      obtain ⟨l,opened,eq⟩ := Option.map_eq_some_iff.mp hit
      rw [show l=e.2 from congrArg Prod.snd eq] at opened
      exact spot_local (eqs:=eqs) marked opened row
    | succ k => exact ih k (by simpa using arity) (by simpa [choose] using hit) (by simpa [choose] using row)

/-- A private role spot lies in the region of its own wing. -/
theorem spot_in_wing {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (path : WingSeparation.emitted eqs r j e)
    {c a b u v w : Vertex} (row : [c,a,b,u,v,w]∈GlobalPins.emitted eqs r j) :
    ArtGallery.segment (HighStep.moved (door j) a) (HighStep.moved (door j) b)⊆(RealizedDoors.wing e).filled := by
  have ne : eqs≠[] := by intro h; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have member := List.fst_mem_of_mem_zipIdx path.1
  obtain ⟨valid,arity⟩ := CandidateTotal.valid_row member
  have sizes : WingSeparation.arities[r.1]?=some (profileBanks r.1).length := by
    generalize hi : r.1=i at valid ⊢; interval_cases i <;> rfl
  exact selected (scale_bounds ne).1 (program_door eqs path.1).le (fun i hi => (program_ranks eqs member hi).le)
    PrivacyCatalogue.catalogue r.1 (arity ▸ sizes) path.2 row

section Side
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,g))
include ne out

theorem wit_cases (i : HubRole eqs) (t : Fin 3) :
    (HubOwners.group eqs (Polygon.mk (v.map ratPoint))).w i t=tipL eqs i ∨
      (HubOwners.group eqs (Polygon.mk (v.map ratPoint))).w i t=tipR eqs i := by
  simp only [HubOwners.group]; split <;> simp

private theorem sep_bands {i j : HubRole eqs} (ne' : i≠j) {z : Point}
    (hi : lo eqs i≤z.1 ∧ z.1≤lo eqs i+9/2) (hj : lo eqs j-3≤z.1 ∧ z.1≤lo eqs j+9/2) : False := by
  have wi := width (eqs:=eqs) i
  have wj := width (eqs:=eqs) j
  rcases apart ne out ne' with h|h <;> linarith [hi.1,hi.2,hj.1,hj.2]

/-- The hub-side facts of the emitted gallery. -/
noncomputable def side (ancs : List (List Nat)) :
    PrivateRoles.HubSide (Polygon.mk (v.map ratPoint)) (HubOwners.group eqs (Polygon.mk (v.map ratPoint)))
      (PrivateRoles.group eqs ancs) (PrivateRoles.wingSet eqs) where
  hub := {q | q∉EmittedGallery.unionWings eqs}
  buried := tipL eqs
  buriedFilled i := (tip_filled ne out i).1
  hubFilled i t := by
    rcases wit_cases ne out i t with h|h <;> rw [h]
    · exact (tip_filled ne out i).1
    · exact (tip_filled ne out i).2
  hubWing k := by
    apply Set.disjoint_left.mpr
    intro q hq hw
    apply hq
    have spec := PrivateRoles.entrance_spec eqs k
    exact ⟨PrivateRoles.entrance eqs k,SourceEntrances.present.mpr ⟨_,_,spec⟩,hw.1⟩
  buriedView i z _ sees := by
    intro hz
    exact wing_free ne out (Or.inl rfl) hz (Polygon.sees_comm.mp sees)
  buriedSeparate i j ne' z hz _ si sj := by
    have zf := Jordan.boundary_subset_filled _ hz
    have bi := left_band ne out zf (Polygon.sees_comm.mp si)
    have bj := left_band ne out zf (Polygon.sees_comm.mp sj)
    exact sep_bands ne out ne' bi ⟨by linarith [bj.1],bj.2⟩
  hubSeparate i j ne' z hz _ si t sj := by
    have zf := Jordan.boundary_subset_filled _ hz
    have bi := left_band ne out zf (Polygon.sees_comm.mp si)
    have wj := width (eqs:=eqs) j
    rcases wit_cases ne out j t with h|h <;> rw [h] at sj
    · have bj := left_band ne out zf (Polygon.sees_comm.mp sj)
      exact sep_bands ne out ne' bi ⟨by linarith [bj.1],bj.2⟩
    · have bj := right_band ne out zf (Polygon.sees_comm.mp sj)
      exact sep_bands ne out ne' bi ⟨bj.1,by linarith [bj.2]⟩
  pinnedMissHub i z hz j t sees := by
    obtain ⟨c,a,b,u,w₁,w,hx⟩ := PrivateRoles.destruct (PrivateRoles.record_six eqs i)
    have mem := PrivateRoles.record_mem eqs i
    rw [hx] at mem
    have inWing := spot_in_wing (PrivateRoles.entrance_spec eqs i.1) mem
    simp only [PrivateRoles.group,hx] at hz
    have zw : z∈EmittedGallery.unionWings eqs :=
      ⟨PrivateRoles.entrance eqs i.1,SourceEntrances.present.mpr ⟨_,_,PrivateRoles.entrance_spec eqs i.1⟩,
        inWing (by simpa using hz)⟩
    exact wing_free ne out (wit_cases ne out j t) zw (Polygon.sees_comm.mp sees)
  hubSpot i z hz _ all := by
    have zf := Jordan.boundary_subset_filled _ hz
    have l := all 0
    have r := all 1
    simp only [HubOwners.group] at l r
    have bl := left_band ne out zf (Polygon.sees_comm.mp (by simpa using l))
    have br := right_band ne out zf (Polygon.sees_comm.mp (by simpa using r))
    exact ⟨hz,bl.1,br.2⟩

end Side

end ArtGallery.Orthogonal.BoundaryPoint.OwnerAssembly
end
