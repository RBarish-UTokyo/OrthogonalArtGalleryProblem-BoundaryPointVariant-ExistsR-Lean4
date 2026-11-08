module

public import ArtGallery.Orthogonal.BoundaryPoint.GuardPerWing
public import ArtGallery.Orthogonal.BoundaryPoint.JoinedBudget
public import ArtGallery.Orthogonal.BoundaryPoint.RoleSeparation

/-! # The private roles of the emitted gallery as a `JoinedBudget` group

Every compiled row places one wing behind door `j`. Each role record
`[c,a,b,u,v,w]` of that wing gives one private role: its witnesses are the
moved points `u,v,w`, its spot is the moved segment `[a,b]`, and its anchor is
the witness selected by an anchor table.

`PrivateRoles.facts` proves the private-role fields of `JoinedBudget.Geometry`
for the actual polygon: witnesses are filled points, viewers of a private
witness are behind its own door, distinct wings are disjoint, a boundary
viewer of all three witnesses is on the spot, and (given the per-profile
separation certificates of `RoleSeparation`) the anchor of one role shares no
viewer with any witness of another role. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PrivateRoles
open Set CatalogPlan CatalogRanks CompiledSize CompiledAddresses ChartDrawing WingMarks
open ContourJoin RectContour BankCoordinates ShapeRefs CorridorProgram RoleSeparation

/-- Every role record of every catalogue template has the six entries `[c,a,b,u,v,w]`. -/
theorem six_all : catalog.all (fun t => (refs t).2.all (fun r => r.length==6))=true := by
  decide +kernel

private theorem six_template {t : Template} (h : (refs t).2.all (fun r => r.length==6)=true)
    (n j : Nat) (rs : List Nat) {r : List Vertex} (hr : r∈GlobalPins.records t n j rs) : r.length=6 := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  let xs := MarginCert.execRat args [] (t.corridor.baseRows++t.corridor.rest)
  let f (p : Ref × Ref) : Vertex := (readRef xs t.room.x s p.1,readRef xs t.room.y s p.2)
  have eq : (ShapeRefs.join (t.corridor.coords args) (t.room.coords s)).2=(refs t).2.map (List.map f) :=
    (congrArg Prod.snd (ShapeRefs.coords t args s)).symm
  change r∈(ShapeRefs.join (t.corridor.coords args) (t.room.coords s)).2 at hr
  rw [eq] at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  simpa using List.all_eq_true.mp h q hq

theorem six {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {x : List Vertex}
    (hx : x∈GlobalPins.emitted eqs r j) : x.length=6 := by
  unfold GlobalPins.emitted at hx
  generalize r.1=tag at hx
  have all := six_all
  generalize catalog=ts at hx all
  induction ts generalizing tag with
  | nil => simp [choose] at hx
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true] at all
    cases tag with
    | zero => exact six_template all.1 _ _ _ hx
    | succ k => exact ih k (by simpa [choose] using hx) all.2

theorem destruct {x : List Vertex} (h : x.length=6) :
    ∃ c a b u v w,x=[c,a,b,u,v,w] := by
  rcases x with _|⟨c,_|⟨a,_|⟨b,_|⟨u,_|⟨v,_|⟨w,_|⟨y,x⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨c,a,b,u,v,w,rfl⟩

private theorem marks (ts : List Template) (n j tag : Nat) (rs : List Nat) :
    choose ts (fun t => GlobalMarks.intervals t n j rs) tag [] =
      requests (choose ts (fun t => GlobalPins.records t n j rs) tag []) := by
  induction ts generalizing tag with
  | nil => rfl
  | cons t ts ih => cases tag with | zero => rfl | succ k => exact ih k

theorem placed {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat}
    (row : (r,j)∈(compile eqs).1.zipIdx) : ∃ e, WingSeparation.emitted eqs r j e := by
  have inPlan := List.fst_mem_of_mem_zipIdx row
  have ne : eqs≠[] := by intro h; subst eqs; exact (List.not_mem_nil (a:=(r,j))) row
  have h := CandidateTotal.valid_row inPlan
  obtain ⟨e,hit⟩ := Option.isSome_iff_exists.mp (CandidateTotal.safe (scale eqs) j r.1 r.2
    (scale_bounds ne).1 (program_door eqs row).le h.1 h.2 (fun _ h => (program_ranks eqs inPlan h).le))
  exact ⟨e,row,hit⟩

section Roles
variable (eqs : List ETRINV.Constraint)

/-- Compiled rows of the source. -/
abbrev rows : List CatalogPlan.Row := (compile eqs).1

theorem row_loc (i : Fin (rows eqs).length) : ((rows eqs)[i],(i:Nat))∈(rows eqs).zipIdx := by
  rw [List.mk_mem_zipIdx_iff_getElem?]; simp

/-- The wing drawn for row `i`. -/
noncomputable def entrance (i : Fin (rows eqs).length) : Entrance := Classical.choose (placed (row_loc eqs i))

theorem entrance_spec (i : Fin (rows eqs).length) :
    WingSeparation.emitted eqs (rows eqs)[i] i (entrance eqs i) := Classical.choose_spec (placed (row_loc eqs i))

/-- Role records of row `i`. -/
def records (i : Fin (rows eqs).length) : List (List Vertex) := GlobalPins.emitted eqs (rows eqs)[i] i

/-- One private role: a row and a record of that row. -/
abbrev Role := Σ i : Fin (rows eqs).length, Fin (records eqs i).length

def record (x : Role eqs) : List Vertex := (records eqs x.1)[x.2]

theorem record_mem (x : Role eqs) : record eqs x∈GlobalPins.emitted eqs (rows eqs)[x.1] x.1 :=
  List.getElem_mem _

theorem record_six (x : Role eqs) : (record eqs x).length=6 := six (record_mem eqs x)

/-- The closed wing region of row `i` with its closed door removed. -/
def wingSet (i : Fin (rows eqs).length) : Set Point :=
  (RealizedDoors.wing (entrance eqs i)).filled \ RealizedDoors.seam (scale eqs) i

/-- The private group for an anchor table indexed by profile tag and role position. -/
def group (ancs : List (List Nat)) : JoinedBudget.Group (Role eqs) where
  w x t := HighStep.moved (door x.1) (witness (record eqs x) t)
  anc x := ⟨((ancs.getD (rows eqs)[x.1].1 []).getD x.2 0) % 3,Nat.mod_lt _ (by norm_num)⟩
  spot x := ArtGallery.segment (HighStep.moved (door x.1) ((record eqs x).getD 1 (0,0)))
    (HighStep.moved (door x.1) ((record eqs x).getD 2 (0,0)))

end Roles

/-- The private-role half of `JoinedBudget.Geometry` for the emitted gallery. -/
structure Facts (P : Polygon) {J K : Type} (b : JoinedBudget.Group J) (wing : K → Set Point) (site : J → K) : Prop where
  privFilled : ∀ i j, b.w i j ∈ P.filled
  wings : ∀ k l, k≠l → Disjoint (wing k) (wing l)
  privateView : ∀ i j, ∀ g∈P.boundary, P.Sees g (b.w i j) → g∈wing (site i)
  privateSeparate : ∀ i j, i≠j → site i=site j → ∀ g∈P.boundary, g∈wing (site i) →
    P.Sees g (b.mark i) → ∀ t, ¬P.Sees g (b.w j t)
  privateSpot : ∀ i, ∀ g∈P.boundary, g∈wing (site i) → (∀ j,P.Sees g (b.w i j)) → g∈b.spot i

private theorem witness_in {x : List Vertex} (h : x.length=6) (t : Fin 3) :
    witness x t∈x.drop 3 := witness_mem h t.isLt

theorem facts {ancs : List (List Nat)}
    (sepAll : ∀ tag t, catalog[tag]?=some t → ∀ a, WingSeparation.arities[tag]?=some a →
      RoleSeparation.Profile (ancs.getD tag []) t a)
    {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat} (out : CandidateWord.vertices eqs=some (v,g)) :
    Facts ⟨v.map ratPoint⟩ (group eqs ancs) (wingSet eqs) Sigma.fst := by
  constructor
  · -- witnesses lie on the polygon boundary
    intro x t
    obtain ⟨c,a,b,u,w₁,w,hx⟩ := destruct (record_six eqs x)
    apply Jordan.boundary_subset_filled
    have hw : witness (record eqs x) t∈(record eqs x).drop 3 := witness_in (record_six eqs x) t
    have req : (witness (record eqs x) t,witness (record eqs x) t)∈
        GlobalMarks.emitted eqs (rows eqs)[x.1] x.1 := by
      unfold GlobalMarks.emitted
      rw [marks]
      apply List.mem_flatMap.mpr
      exact ⟨_,record_mem eqs x,request_mem (record_six eqs x) hw⟩
    exact GlobalMarks.boundary (entrance_spec eqs x.1) out req (Geometry.left_mem_segment _ _)
  · -- wings of distinct rows are disjoint
    intro k l ne
    have d := WingSeparation.disjoint (entrance_spec eqs k) (entrance_spec eqs l)
      (fun h => ne (Fin.ext h))
    exact Set.disjoint_of_subset Set.sdiff_subset Set.sdiff_subset d
  · -- a viewer of a private witness is behind its own door
    intro x t z _ seen
    obtain ⟨c,a,b,u,w₁,w,hx⟩ := destruct (record_six eqs x)
    have mem := record_mem eqs x
    rw [hx] at mem
    have hw := witness_in (record_six eqs x) t
    rw [hx] at hw
    simp only [List.drop_succ_cons,List.drop_zero] at hw
    simp only [group] at seen
    rw [hx] at seen
    exact GlobalPrivacy.viewer (entrance_spec eqs x.1) out mem hw seen
  · -- anchors are private within a wing
    intro x y ne same z bd _ seen t
    obtain ⟨i,p⟩ := x
    obtain ⟨k,q⟩ := y
    obtain rfl : i=k := same
    have pq : (p:Nat)≠q := fun h => ne (by rw [Fin.ext h])
    have hi : (records eqs i)[(p:Nat)]?=some (record eqs ⟨i,p⟩) := List.getElem?_eq_getElem p.isLt
    have hk : (records eqs i)[(q:Nat)]?=some (record eqs ⟨i,q⟩) := List.getElem?_eq_getElem q.isLt
    have hw := witness_in (record_six eqs ⟨i,q⟩) t
    apply RoleSeparation.separate sepAll (entrance_spec eqs i) out pq hi hk bd ?_ hw
    simpa [JoinedBudget.Group.mark,group] using seen
  · -- a boundary viewer of all three witnesses is on the spot
    intro x z bd _ all
    obtain ⟨c,a,b,u,w₁,w,hx⟩ := destruct (record_six eqs x)
    have mem := record_mem eqs x
    rw [hx] at mem
    have h := GlobalPins.forces (entrance_spec eqs x.1) out mem bd ?_
    · simpa [group,hx] using h
    · intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl
      · simpa [group,hx,witness] using all 0
      · simpa [group,hx,witness] using all 1
      · simpa [group,hx,witness] using all 2

/-- The hub-side fields of `JoinedBudget.Geometry`: buried witnesses, hub groups and their
separation from the private roles. -/
structure HubSide (P : Polygon) {H J K : Type} (a : JoinedBudget.Group H) (b : JoinedBudget.Group J)
    (wing : K → Set Point) where
  hub : Set Point
  buried : H → Point
  buriedFilled : ∀ i, buried i ∈ P.filled
  hubFilled : ∀ i j, a.w i j ∈ P.filled
  hubWing : ∀ k, Disjoint hub (wing k)
  buriedView : ∀ i, ∀ g∈P.boundary, P.Sees g (buried i) → g∈hub
  buriedSeparate : ∀ i j, i≠j → ∀ g∈P.boundary, g∈hub → P.Sees g (buried i) → ¬P.Sees g (buried j)
  hubSeparate : ∀ i j, i≠j → ∀ g∈P.boundary, g∈hub → P.Sees g (a.mark i) → ∀ t, ¬P.Sees g (a.w j t)
  pinnedMissHub : ∀ i, ∀ g∈b.spot i, ∀ j t, ¬P.Sees g (a.w j t)
  hubSpot : ∀ i, ∀ g∈P.boundary, g∈hub → (∀ j,P.Sees g (a.w i j)) → g∈a.spot i

/-- Private facts and hub facts together are the joined counting geometry. -/
def geometry {P : Polygon} {H J K : Type} {a : JoinedBudget.Group H} {b : JoinedBudget.Group J}
    {wing : K → Set Point} {site : J → K} (f : Facts P b wing site) (h : HubSide P a b wing) :
    JoinedBudget.Geometry H J K P a b where
  hub := h.hub
  wing := wing
  site := site
  buried := h.buried
  buriedFilled := h.buriedFilled
  hubFilled := h.hubFilled
  privFilled := f.privFilled
  hubWing := h.hubWing
  wings := f.wings
  buriedView := h.buriedView
  privateView := f.privateView
  buriedSeparate := h.buriedSeparate
  hubSeparate := h.hubSeparate
  privateSeparate := f.privateSeparate
  pinnedMissHub := h.pinnedMissHub
  hubSpot := h.hubSpot
  privateSpot := f.privateSpot

/-- Ownership in the emitted gallery: with the per-profile separation certificates and the
hub-side facts, every boundary cover with at most one guard per hub role and per private role
has exactly that many guards, each role owns exactly one guard on its spot, and every guard
belongs to a role. -/
theorem owners {ancs : List (List Nat)}
    (sepAll : ∀ tag t, catalog[tag]?=some t → ∀ a, WingSeparation.arities[tag]?=some a →
      RoleSeparation.Profile (ancs.getD tag []) t a)
    {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat} (out : CandidateWord.vertices eqs=some (v,g))
    {H : Type} [Fintype H] {a : JoinedBudget.Group H}
    (hub : HubSide ⟨v.map ratPoint⟩ a (group eqs ancs) (wingSet eqs))
    (G : Finset Point) (cover : (Polygon.mk (v.map ratPoint)).IsGuardSetOnBoundary (G:Set Point))
    (budget : G.card≤Fintype.card H+Fintype.card (Role eqs)) :
    G.card=Fintype.card H+Fintype.card (Role eqs) ∧
    (∀ i : H⊕Role eqs, ∃ p∈G, (Polygon.mk (v.map ratPoint)).Sees p (Sum.elim a.mark (group eqs ancs).mark i) ∧
      p∈Sum.elim a.spot (group eqs ancs).spot i ∧
      ∀ q∈G,(Polygon.mk (v.map ratPoint)).Sees q (Sum.elim a.mark (group eqs ancs).mark i) → q=p) ∧
    (∀ p∈G,∃ i : H⊕Role eqs,(Polygon.mk (v.map ratPoint)).Sees p (Sum.elim a.mark (group eqs ancs).mark i) ∧
      p∈Sum.elim a.spot (group eqs ancs).spot i) :=
  JoinedBudget.force (geometry (facts sepAll out) hub) G cover budget

end ArtGallery.Orthogonal.BoundaryPoint.PrivateRoles
end
