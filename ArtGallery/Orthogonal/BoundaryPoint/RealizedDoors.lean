module

public import ArtGallery.Orthogonal.BoundaryPoint.DoorSegment
public import ArtGallery.Orthogonal.BoundaryPoint.WingStep
public import ArtGallery.Orthogonal.BoundaryPoint.HubSky
public import ArtGallery.Orthogonal.BoundaryPoint.PlacedSlots

/-! # Exact intersections of the generated hub and its wings
These are statements about the actual Jordan-filled polygons traced by the
raw-word generator for every source row and every input size. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RealizedDoors
open WingEnvelope WingSeparation HighStep BoundaryChart ChartDrawing RectContour ContourJoin BankCoordinates
open CompiledSize CatalogPlan DoorSegment

def hub (eqs : List ETRINV.Constraint) : Polygon :=
  ⟨(hubCycle (scale eqs) (compile eqs).1.length (PlacedSlots.starts eqs)).map ratPoint⟩

def wing (e : Entrance) : Polygon := ⟨e.2.map ratPoint⟩
def seam (n j : Nat) : Set Point := ArtGallery.segment ((door j:ℝ),1) ((door j:ℝ)+(W n:ℝ),1)

theorem extraction (ts : List Template) (n j tag : Nat) (rs : List Nat) {e : Entrance}
    (hit : (choose ts (fun t => drawOne t n j rs) tag (none,0)).1=some e) :
    ∃ l,atDoor (door j) (W n) l=some e.2 := by
  induction ts generalizing tag with
  | nil => contradiction
  | cons t ts ih =>
    cases tag with
    | zero =>
      change (atDoor (door j) (W n) _).map (fun v => (door j,v))=some e at hit
      obtain ⟨path,ok,rfl⟩ := Option.map_eq_some_iff.mp hit
      exact ⟨_,ok⟩
    | succ tag => exact ih _ (by simpa [choose] using hit)

private theorem mouth_iff {n j : Nat} (wpos : 0<(W n:ℝ)) (p : Point) :
    Mouth (door j) (W n) p ↔ p∈seam n j := by
  constructor
  · rintro ⟨Y,L,R⟩
    obtain ⟨x,y⟩ := p
    change y=1 at Y
    subst y
    exact horizontal (by linarith) L R
  · rintro ⟨t,ht,hu,rfl⟩
    simp only [Mouth,sub_self,mul_zero,add_zero,add_sub_cancel_left]
    constructor
    · trivial
    · exact ⟨le_add_of_nonneg_right (mul_nonneg ht wpos.le),
        add_le_add_right (by simpa using mul_le_mul_of_nonneg_right hu wpos.le) _⟩

private theorem same_cap {j k : Nat} {p : Point} (wingPos : InStrip j p) (cap : HubSky.AtCap k p) : j=k := by
  unfold InStrip HubSky.AtCap door at *
  push_cast at *
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|gt
  · have gap : (j:ℝ)+1≤k := by exact_mod_cast lt
    linarith [wingPos.1,cap.2.1]
  · have gap : (k:ℝ)+1≤j := by exact_mod_cast gt
    linarith [wingPos.2.1,cap.1]

theorem intersection {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance}
    (path : emitted eqs r j e) : (hub eqs).filled ∩ (wing e).filled=seam (scale eqs) j := by
  have ne : eqs≠[] := by intro z; subst eqs; exact (List.not_mem_nil (a:=(r,j))) path.1
  let n := scale eqs
  have hn : 65≤n := (scale_bounds ne).1
  have pos : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have Wpos : 0<W n := by unfold W; positivity
  have irows := (List.mem_zipIdx' path.1).1
  have wreal : (0:ℝ)<W n := by exact_mod_cast Wpos
  ext p
  constructor
  · rintro ⟨inHub,inWing⟩
    have strip := (placement path).2 p inWing
    have west : p.1<1970 := by
      have d0 : (door j:ℝ)≤0 := by simp [door]
      linarith [strip.2.1]
    obtain ⟨k,hk,cap⟩ := HubSky.upper (n:=n) (ss:=PlacedSlots.starts eqs) (Nat.zero_lt_of_lt irows) hn
      (fun x hx => (PlacedSlots.right_of_all_wings ne hx).le) inHub strip.2.2.1 west
    obtain rfl := same_cap strip cap
    exact (mouth_iff wreal p).mp (WingStep.sole_contact path p inWing cap.2.1 cap.2.2)
  · intro hp
    have m := (mouth_iff wreal p).mpr hp
    obtain ⟨l,chosen⟩ := extraction catalog n j r.1 r.2 path.2
    exact ⟨in_hub n _ _ _ hn irows m,in_wing Wpos chosen m⟩

end ArtGallery.Orthogonal.BoundaryPoint.RealizedDoors
end
