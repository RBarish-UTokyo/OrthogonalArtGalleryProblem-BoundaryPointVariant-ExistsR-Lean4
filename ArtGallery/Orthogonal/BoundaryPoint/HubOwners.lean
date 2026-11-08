module

public import ArtGallery.Orthogonal.BoundaryPoint.HubRoles
public import ArtGallery.Orthogonal.BoundaryPoint.PrivateRoles

/-! # The hub roles of the emitted gallery

One role per base slot and one per door step. A base role has the two far
corners of its shaft as witnesses (the left one is its anchor and its buried
witness); its spot is the part of the polygon boundary in the shaft's mouth
interval. A step role has the two bottom corners of its foot, and its spot is
the part of the boundary in the foot's mouth interval. The hub is the
complement of the wings. `HubOwners.side` proves every field of
`PrivateRoles.HubSide` for the actual polygon. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubOwners
open Set RectContour BoundaryChart BankCoordinates Geometry HubColumns HubWindows HubRoles CompiledSize CatalogPlan

section Defs
variable (eqs : List ETRINV.Constraint)

abbrev slots := PlacedSlots.starts eqs

/-- Hub roles: base slots and door steps. -/
abbrev HubRole := Fin (slots eqs).length ⊕ Fin (compile eqs).1.length

/-- The slot of base role `k`. -/
def sx (k : Fin (slots eqs).length) : ℚ := (slots eqs)[(k:Nat)]

theorem sx_mem (k : Fin (slots eqs).length) : sx eqs k∈slots eqs := List.getElem_mem k.isLt

def tipL : HubRole eqs → Point
  | .inl k => (((sx eqs k:ℚ):ℝ),((top eqs:ℚ):ℝ))
  | .inr j => (((fl j:ℚ):ℝ),((2*flo eqs:ℚ):ℝ))

def tipR : HubRole eqs → Point
  | .inl k => (((sx eqs k+3/2:ℚ):ℝ),((top eqs:ℚ):ℝ))
  | .inr j => (((fr j:ℚ):ℝ),((2*flo eqs:ℚ):ℝ))

def lo : HubRole eqs → ℝ
  | .inl k => ((sx eqs k:ℚ):ℝ)
  | .inr j => ((fl j:ℚ):ℝ)

def hi : HubRole eqs → ℝ
  | .inl k => ((sx eqs k+3/2:ℚ):ℝ)
  | .inr j => ((fr j:ℚ):ℝ)

def group (P : Polygon) : JoinedBudget.Group (HubRole eqs) where
  w i t := if t.val=1 then tipR eqs i else tipL eqs i
  anc _ := 0
  spot i := {z | z∈P.boundary ∧ lo eqs i≤z.1 ∧ z.1≤hi eqs i}

end Defs

section Emitted
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,g))
include ne out

/-- Bands of the viewers of the two witnesses of a hub role. -/
theorem left_band {i : HubRole eqs} {z : Point} (hz : z∈(Polygon.mk (v.map ratPoint)).filled)
    (sees : (Polygon.mk (v.map ratPoint)).Sees (tipL eqs i) z) :
    lo eqs i≤z.1 ∧ z.1≤lo eqs i+9/2 := by
  rcases i with k|j
  · exact shaft_left ne out (sx_mem eqs k) hz sees
  · have b := foot_left ne out hz sees
    exact ⟨b.1,by simp only [lo]; linarith [b.2]⟩

theorem right_band {i : HubRole eqs} {z : Point} (hz : z∈(Polygon.mk (v.map ratPoint)).filled)
    (sees : (Polygon.mk (v.map ratPoint)).Sees (tipR eqs i) z) :
    lo eqs i-3≤z.1 ∧ z.1≤hi eqs i := by
  rcases i with k|j
  · have b := shaft_right ne out (sx_mem eqs k) hz sees
    simp only [lo,hi]; push_cast; constructor <;> linarith [b.1,b.2]
  · have b := foot_right ne out hz sees
    have wid : ((fr j:ℚ):ℝ)=((fl j:ℚ):ℝ)+2/1000 := by unfold fl fr; push_cast; ring
    exact ⟨by simp only [lo]; linarith [b.1],b.2⟩

omit ne out in
theorem width (i : HubRole eqs) : lo eqs i≤hi eqs i ∧ hi eqs i≤lo eqs i+3/2 := by
  rcases i with k|j
  · simp only [lo,hi]; push_cast; constructor <;> linarith
  · simp only [lo,hi,fl,fr]; push_cast; constructor <;> linarith

/-- Distinct hub roles have mouth intervals at least eight units apart. -/
theorem apart {a b : HubRole eqs} (ne' : a≠b) : hi eqs a+8≤lo eqs b ∨ hi eqs b+8≤lo eqs a := by
  have placed := RealizedHub.placed ne
  have doorNeg (j : Nat) : (door j:ℝ)≤0 := by unfold door; push_cast; nlinarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]
  rcases a with k|j <;> rcases b with k'|j'
  · have d : sx eqs k≠sx eqs k' := by
      intro e
      have nd : (slots eqs).Nodup := placed.sorted.imp (fun h e => by subst e; linarith)
      exact ne' (congrArg Sum.inl (Fin.ext ((List.Nodup.getElem_inj_iff nd).mp e)))
    rcases placed_apart placed.sorted (sx_mem eqs k) (sx_mem eqs k') d with h|h
    · left; have : ((sx eqs k+10:ℚ):ℝ)≤sx eqs k' := by exact_mod_cast h
      simp only [hi,lo]; push_cast at this ⊢; linarith
    · right; have : ((sx eqs k'+10:ℚ):ℝ)≤sx eqs k := by exact_mod_cast h
      simp only [hi,lo]; push_cast at this ⊢; linarith
  · right
    have far : (1970:ℝ)<sx eqs k := by exact_mod_cast placed.far _ (sx_mem eqs k)
    simp only [hi,lo,fr]; push_cast; linarith [doorNeg j']
  · left
    have far : (1970:ℝ)<sx eqs k' := by exact_mod_cast placed.far _ (sx_mem eqs k')
    simp only [hi,lo,fr]; push_cast; linarith [doorNeg j]
  · have d : (j:Nat)≠j' := fun e => ne' (congrArg Sum.inr (Fin.ext e))
    rcases doors_apart d with h|h
    · left; simp only [hi,lo,fl,fr]; push_cast; linarith
    · right; simp only [hi,lo,fl,fr]; push_cast; linarith

/-- No wing point sees a witness of a hub role. -/
theorem wing_free {i : HubRole eqs} {t : Point} (ht : t=tipL eqs i ∨ t=tipR eqs i) {z : Point}
    (hz : z∈EmittedGallery.unionWings eqs) (sees : (Polygon.mk (v.map ratPoint)).Sees t z) : False := by
  have strip := wing_strip hz
  have zf : z∈(Polygon.mk (v.map ratPoint)).filled := by
    rw [(GlobalShape.decomposition ne out).filled]; exact Or.inr hz
  rcases i with k|j
  · have far : (1970:ℝ)<sx eqs k := by exact_mod_cast (RealizedHub.placed ne).far _ (sx_mem eqs k)
    rcases ht with rfl|rfl
    · have := (left_band ne out zf sees).1; simp only [lo] at this; linarith [strip.1]
    · have := (right_band ne out zf sees).1; simp only [lo] at this; linarith [strip.1]
  ·
    obtain ⟨e,he,hzw⟩ := hz
    obtain ⟨r,j',path⟩ := SourceEntrances.present.mp he
    let d := GalleryBoundary.joined path out
    have hf := flo_lt ne
    have tFilled : t∈(Polygon.mk (v.map ratPoint)).filled := sees (Geometry.left_mem_segment _ _)
    have tOut : t∉(RealizedDoors.wing e).filled := by
      intro h
      have s := (WingSeparation.placement path).2 t h
      rcases ht with rfl|rfl <;> simp only [tipL,tipR] at s <;> push_cast at s hf <;> linarith [s.2.2.1]
    have tRest : t∈d.rest := by
      have := d.fill ▸ tFilled
      exact this.resolve_left tOut
    obtain ⟨q,hq,hqi⟩ := SingleWindow.segment_meets_window (Jordan.isClosed_filled _) d.closed hzw tRest
      (fun y hy => d.fill ▸ (Polygon.sees_comm.mp sees) hy)
    rw [d.contact] at hqi
    have seg : ArtGallery.segment q t⊆ArtGallery.segment z t :=
      Geometry.segment_subset_of_convex (Geometry.segment_convex z t) hq (Geometry.right_mem_segment _ _)
    have qSees : (Polygon.mk (v.map ratPoint)).Sees t q :=
      Polygon.sees_comm.mp (fun y hy => (Polygon.sees_comm.mp sees) (seg hy))
    have qFilled := qSees (Geometry.right_mem_segment _ _)
    have Wpos : (0:ℝ)≤(W (scale eqs):ℝ) := by unfold W; positivity
    have W1 : (W (scale eqs):ℝ)≤1 := by
      have hn : (65:ℝ)≤scale eqs := by exact_mod_cast (scale_bounds ne).1
      unfold W; push_cast
      rw [div_le_one (by positivity)]; nlinarith
    obtain ⟨s,s0,s1,hs⟩ := hqi
    have qx : (door j':ℝ)≤q.1 ∧ q.1≤(door j':ℝ)+1 := by
      rw [hs]; simp only
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right s1 Wpos]
    have band : (door (j:Nat):ℝ)+95≤q.1 ∧ q.1≤(door (j:Nat):ℝ)+105 := by
      rcases ht with rfl|rfl
      · have b := left_band ne out qFilled qSees
        simp only [lo,fl] at b; push_cast at b; constructor <;> linarith [b.1,b.2]
      · have b := right_band ne out qFilled qSees
        simp only [lo,hi,fl,fr] at b; push_cast at b; constructor <;> linarith [b.1,b.2]
    simp only [door] at qx band; push_cast at qx band
    rcases lt_trichotomy j' (j:Nat) with l|e|l
    · have : (j':ℝ)+1 ≤ ((j:Nat):ℝ) := by exact_mod_cast l
      linarith [qx.1,band.2]
    · subst e; linarith [qx.2,band.1]
    · have : ((j:Nat):ℝ)+1 ≤ (j':ℝ) := by exact_mod_cast l
      linarith [qx.2,band.1]

end Emitted

/-! ## Hub witnesses are filled; private spots lie in their wings -/

theorem vertex_boundary {l : List Vertex} {u : Vertex} (hu : u∈l) :
    ratPoint u∈(Polygon.mk (l.map ratPoint)).boundary := by
  obtain ⟨i,hi,e⟩ := List.getElem_of_mem hu
  have hi' : i<(Polygon.mk (l.map ratPoint)).n := by simpa [Polygon.n] using hi
  refine ⟨i,hi',?_⟩
  have v : (Polygon.mk (l.map ratPoint)).vtx i=ratPoint u := by
    simp only [Polygon.vtx]; rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,e]
  show ratPoint u∈ArtGallery.segment ((Polygon.mk (l.map ratPoint)).vtx i) ((Polygon.mk (l.map ratPoint)).vtx ((i+1)%(Polygon.mk (l.map ratPoint)).n))
  rw [v]; exact Geometry.left_mem_segment _ _

section Filled
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,g))
include ne out

theorem hub_vertex_filled {u : Vertex}
    (hu : u∈hubCycle (scale eqs) (compile eqs).1.length (PlacedSlots.starts eqs)) :
    ratPoint u∈(Polygon.mk (v.map ratPoint)).filled := by
  rw [(GlobalShape.decomposition ne out).filled]
  left
  exact Jordan.boundary_subset_filled _ (vertex_boundary hu)

theorem tip_filled (i : HubRole eqs) :
    tipL eqs i∈(Polygon.mk (v.map ratPoint)).filled ∧ tipR eqs i∈(Polygon.mk (v.map ratPoint)).filled := by
  rcases i with k|j
  · have m : ∀ u∈shaft (1-D (scale eqs)) (sx eqs k),
        u∈hubCycle (scale eqs) (compile eqs).1.length (PlacedSlots.starts eqs) := by
      intro u hu
      unfold hubCycle; dsimp only
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨_,List.mem_reverse.mpr (sx_mem eqs k),hu⟩
    constructor
    · have := hub_vertex_filled ne out (m (sx eqs k,-6-(1-D (scale eqs))) (by simp [shaft]))
      simpa [tipL,ratPoint,top,flo] using this
    · have := hub_vertex_filled ne out (m (sx eqs k+3/2,-6-(1-D (scale eqs))) (by simp [shaft]))
      simpa [tipR,ratPoint,top,flo] using this
  · have m : ∀ u∈foot (1-D (scale eqs)) (j:Nat),
        u∈hubCycle (scale eqs) (compile eqs).1.length (PlacedSlots.starts eqs) := by
      intro u hu
      unfold hubCycle; dsimp only
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨_,List.mem_reverse.mpr (List.mem_range.mpr j.isLt),hu⟩
    constructor
    · have := hub_vertex_filled ne out (m (door (j:Nat)+100-1/1000,2*(1-D (scale eqs))) (by simp [foot]))
      simpa [tipL,ratPoint,fl,flo] using this
    · have := hub_vertex_filled ne out (m (door (j:Nat)+100+1/1000,2*(1-D (scale eqs))) (by simp [foot]))
      simpa [tipR,ratPoint,fr,flo] using this

end Filled

end ArtGallery.Orthogonal.BoundaryPoint.HubOwners
end
