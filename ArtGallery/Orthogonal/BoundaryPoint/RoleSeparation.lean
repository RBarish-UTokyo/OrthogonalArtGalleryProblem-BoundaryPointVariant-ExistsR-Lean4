module

public import ArtGallery.Orthogonal.BoundaryPoint.WitnessView
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalPrivacy

/-! # Same-wing role separation transported to the joined gallery

`Separated t args anc` is a statement about one isolated wing chart. Each role
record `[c,a,b,u,v,w]` designates one of its three witnesses `u,v,w` as anchor
(entry `i` of `anc`, read modulo three).
No boundary point of the wing sees the anchor of one role together with any
witness of a different role of the same wing.

`transport` shows that this local statement gives the same exclusion for every
boundary point of the complete emitted polygon. A viewer of the anchor is
confined behind the closed door of its own wing, lies on the wing boundary, and
its full-polygon sightlines to points of that wing are wing sightlines. This is
the `privateSeparate` field of `JoinedBudget.Geometry`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoleSeparation
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize
open ShapeRefs WingMarks PinTransport Geometry Hardening.Invariance
open CatalogPlan CatalogRanks CompiledAddresses

/-- The witness with index `a` (`0`, `1` or `2`) of a role record. -/
def witness (r : List Vertex) (a : Nat) : Vertex := (r.drop 3).getD a (0,0)

/-- Local separation for one wing chart with role anchors `anc`. -/
def Separated (t : Template) (args : List ℚ) (anc : List Nat) : Prop :=
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (MarginCert.getRat args 0))
  let L := BoundaryChart.actual t.chart data
  (∀ (i : Nat) (r : List Vertex), data.2[i]?=some r → r.length=6) ∧
  ∀ i k : Nat, i≠k → ∀ ri rk, data.2[i]?=some ri → data.2[k]?=some rk →
    ∀ y∈L.boundary, L.Sees y (ratPoint (witness ri (anc.getD i 0 % 3))) →
      ∀ h∈rk.drop 3, ¬L.Sees y (ratPoint h)

theorem witness_mem {r : List Vertex} (hr : r.length=6) {a : Nat} (ha : a<3) :
    witness r a∈r.drop 3 := by
  unfold witness
  have lt : a<(r.drop 3).length := by simp [hr]; omega
  rw [List.getD_eq_getElem _ _ lt]
  exact List.getElem_mem lt

theorem request_mem {r : List Vertex} (hr : r.length=6) {h : Vertex} (hh : h∈r.drop 3) :
    (h,h)∈perRole r := by
  rcases r with _|⟨c,_|⟨a,_|⟨b,_|⟨u,_|⟨v,_|⟨w,_|⟨x,r⟩⟩⟩⟩⟩⟩⟩ <;> simp at hr
  simp only [List.drop_succ_cons,List.drop_zero,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl <;> simp [perRole]

theorem transport {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {vs g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (vs,g))
    {t : Template} {args : List ℚ} (reciprocal : MarginCert.getRat args 0=1/(scale eqs:ℚ))
    (eligible : WingMarks.Holds t args) (hidden : WingPrivacy.AllHidden t args)
    {anc : List Nat} (sep : Separated t args anc)
    (opened : atDoor (door j) (W (scale eqs))
      (t.chart.draw (ShapeRefs.join (t.corridor.coords args) (t.room.coords (MarginCert.getRat args 0))))=some e.2)
    {i k : Nat} (hik : i≠k) {ri rk : List Vertex}
    (hi : ((t.corridor.coords args).2++(t.room.coords (MarginCert.getRat args 0)).2)[i]?=some ri)
    (hk : ((t.corridor.coords args).2++(t.room.coords (MarginCert.getRat args 0)).2)[k]?=some rk)
    {z : Point} (bd : z∈(Polygon.mk (vs.map ratPoint)).boundary)
    (seen : (Polygon.mk (vs.map ratPoint)).Sees z (HighStep.moved (door j) (witness ri (anc.getD i 0 % 3))))
    {h : Vertex} (hh : h∈rk.drop 3) :
    ¬(Polygon.mk (vs.map ratPoint)).Sees z (HighStep.moved (door j) h) := by
  intro other
  let d := door j
  let s := MarginCert.getRat args 0
  let A := shift d
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
  let L := BoundaryChart.actual t.chart data
  let R := RealizedDoors.wing e
  have memI : ri∈data.2 := List.mem_of_getElem? hi
  have memK : rk∈data.2 := List.mem_of_getElem? hk
  have li := sep.1 i ri hi
  have lk := sep.1 k rk hk
  obtain ⟨m,rot⟩ := placed opened
  change R=(mapPoly A L).rotate m at rot
  have filled : R.filled=A '' L.filled := by rw [rot,Existence.filled_rotate,filled_mapPoly]
  have boundary : R.boundary=A '' L.boundary := by rw [rot,Existence.boundary_rotate,boundary_mapPoly]
  have sees (p q : Point) : R.Sees (A p) (A q) ↔ L.Sees p q := by
    change ArtGallery.segment (A p) (A q) ⊆ R.filled ↔ ArtGallery.segment p q ⊆ L.filled
    rw [filled,←image_segment',Set.image_subset_image_iff A.injective]
  have at_vertex (p : Vertex) : A (ratPoint p)=HighStep.moved d p := shift_vertex _ _
  have inside {rr : List Vertex} (mem : rr∈data.2) (len : rr.length=6) {p : Vertex} (hp : p∈rr.drop 3) :
      ratPoint p∈L.filled := by
    apply Jordan.boundary_subset_filled
    apply eligible (p,p) _ (Geometry.left_mem_segment _ _)
    exact List.mem_flatMap.mpr ⟨rr,mem,request_mem len hp⟩
  let a := witness ri (anc.getD i 0 % 3)
  have aw : a∈ri.drop 3 := witness_mem li (Nat.mod_lt _ (by norm_num))
  let join := GalleryBoundary.joined path out
  have source : A (ratPoint a)∈R.filled := filled ▸ Set.mem_image_of_mem _ (inside memI li aw)
  have target : A (ratPoint h)∈R.filled := filled ▸ Set.mem_image_of_mem _ (inside memK lk hh)
  have vis : (Polygon.mk (vs.map ratPoint)).Sees z (A (ratPoint a)) := by rw [at_vertex]; exact seen
  have miss : ∀ q∈RealizedDoors.seam (scale eqs) j,¬R.Sees (A (ratPoint a)) q := by
    intro q inSeam sight
    let x := A.symm q
    have eqx : A x=q := A.apply_symm_apply q
    apply hidden ri memI a aw x ?_ ((sees _ _).mp (by rwa [eqx]))
    have door := WitnessView.unshift_door inSeam
    show PortalGate.Door ((MarginCert.getRat args 0:ℚ):ℝ) x
    rw [reciprocal,Rat.cast_div]; exact door
  have confined := join.local_view source miss vis
  have ne : eqs≠[] := by intro h; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have gallery := GlobalShape.decomposition ne out
  have tree := gallery.from_wing r j e path
  have rb : z∈R.boundary :=
    WindowBoundary.restrict_guard (RealizedWings.simple path) gallery.simple tree.subset bd confined.1
  rw [boundary] at rb
  obtain ⟨y,hy,rfl⟩ := rb
  have sightA : L.Sees y (ratPoint a) := by
    apply (sees _ _).mp
    exact (tree.sees_iff confined.1 source).mp vis
  have sightH : L.Sees y (ratPoint h) := by
    apply (sees _ _).mp
    apply (tree.sees_iff confined.1 target).mp
    rw [at_vertex]; exact other
  exact sep.2 i k hik ri rk hi hk y hy sightA h hh sightH

/-- Separation for every admissible size and rank vector of one profile. -/
def Profile (anc : List Nat) (t : Template) (arity : Nat) : Prop := ∀ (rs : List Nat),rs.length=arity →
  ∀ n j : Nat,65≤n → j≤n → (∀ i∈rs,i≤n) →
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    Separated t args anc

private theorem selected {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {vs g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (vs,g))
    (hn : 65≤scale eqs) (hj : j≤scale eqs) (hr : ∀ i∈r.2,i≤scale eqs)
    {ts : List Template} {ar : List Nat} {ancs : List (List Nat)}
    (all : List.Forall₂ PrivacyCatalogue.Profile ts ar)
    (sepAll : ∀ tag t, ts[tag]?=some t → ∀ a, ar[tag]?=some a → Profile (ancs.getD tag []) t a)
    (tag : Nat) (arity : ar[tag]?=some r.2.length)
    (hit : (choose ts (fun t => drawOne t (scale eqs) j r.2) tag (none,0)).1=some e)
    {i k : Nat} (hik : i≠k) {ri rk : List Vertex}
    (hi : (choose ts (fun t => GlobalPins.records t (scale eqs) j r.2) tag [])[i]?=some ri)
    (hk : (choose ts (fun t => GlobalPins.records t (scale eqs) j r.2) tag [])[k]?=some rk)
    {z : Point} (bd : z∈(Polygon.mk (vs.map ratPoint)).boundary)
    (seen : (Polygon.mk (vs.map ratPoint)).Sees z
      (HighStep.moved (door j) (witness ri ((ancs.getD tag []).getD i 0 % 3))))
    {h : Vertex} (hh : h∈rk.drop 3) :
    ¬(Polygon.mk (vs.map ratPoint)).Sees z (HighStep.moved (door j) h) := by
  induction all generalizing tag ancs with
  | nil => simp at arity
  | @cons t n ts ar cert _ ih =>
    cases tag with
    | zero =>
      have size : r.2.length=n := by simpa using (Option.some.inj arity).symm
      have ⟨marked,hidden⟩ := cert r.2 size _ _ hn hj hr
      have sep := sepAll 0 t rfl n rfl r.2 size _ _ hn hj hr
      change (atDoor (door j) (W (scale eqs)) (t.chart.draw _)).map (fun x => (door j,x))=some e at hit
      obtain ⟨l,opened,eq⟩ := Option.map_eq_some_iff.mp hit
      rw [show l=e.2 from congrArg Prod.snd eq] at opened
      exact transport path out rfl marked hidden sep opened hik hi hk bd seen hh
    | succ m =>
      apply ih (ancs:=ancs.tail) (fun tag t ht a ha => by
          have := sepAll (tag+1) t (by simpa using ht) a (by simpa using ha)
          simpa [List.getD_eq_getElem?_getD] using this) m (by simpa using arity) (by simpa [choose] using hit)
        (by simpa [choose] using hi) (by simpa [choose] using hk) ?_
      simpa [List.getD_eq_getElem?_getD] using seen

/-- Role separation inside every emitted wing of the actual gallery. -/
theorem separate {ancs : List (List Nat)}
    (sepAll : ∀ tag t, catalog[tag]?=some t → ∀ a, WingSeparation.arities[tag]?=some a →
      Profile (ancs.getD tag []) t a)
    {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {vs g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (vs,g))
    {i k : Nat} (hik : i≠k) {ri rk : List Vertex}
    (hi : (GlobalPins.emitted eqs r j)[i]?=some ri) (hk : (GlobalPins.emitted eqs r j)[k]?=some rk)
    {z : Point} (bd : z∈(Polygon.mk (vs.map ratPoint)).boundary)
    (seen : (Polygon.mk (vs.map ratPoint)).Sees z
      (HighStep.moved (door j) (witness ri ((ancs.getD r.1 []).getD i 0 % 3))))
    {h : Vertex} (hh : h∈rk.drop 3) :
    ¬(Polygon.mk (vs.map ratPoint)).Sees z (HighStep.moved (door j) h) := by
  have ne : eqs≠[] := by intro h; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  have member := List.fst_mem_of_mem_zipIdx path.1
  obtain ⟨valid,arity⟩ := CandidateTotal.valid_row member
  have sizes : WingSeparation.arities[r.1]?=some (profileBanks r.1).length := by
    generalize hi : r.1=i at valid ⊢; interval_cases i <;> rfl
  exact selected path out (scale_bounds ne).1 (program_door eqs path.1).le
    (fun i hi => (program_ranks eqs member hi).le) PrivacyCatalogue.catalogue sepAll r.1 (arity ▸ sizes)
    path.2 hik hi hk bd seen hh

end ArtGallery.Orthogonal.BoundaryPoint.RoleSeparation
end
