module

public import ArtGallery.Orthogonal.BoundaryPoint.HubWindows
public import ArtGallery.Orthogonal.BoundaryPoint.GalleryBoundary

/-! # Viewers of the hub witnesses in the emitted gallery

The hub witnesses are the two far corners of every base shaft and the two
bottom corners of every foot. In the complete emitted polygon:

* a viewer of a far shaft corner lies within a band of the shaft's mouth of
  width at most three mouth widths, and a viewer of both corners lies in the
  mouth interval; likewise for the feet;
* no point of a wing sees any hub witness. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubRoles
open Set RectContour BoundaryChart BankCoordinates Geometry HubColumns HubWindows CompiledSize CatalogPlan

/-- Floor height and shaft top of the emitted hub. -/
def flo (eqs : List ETRINV.Constraint) : ℚ := 1-D (scale eqs)
def top (eqs : List ETRINV.Constraint) : ℚ := -6-flo eqs
def fl (j : Nat) : ℚ := door j+100-1/1000
def fr (j : Nat) : ℚ := door j+100+1/1000

section Emitted
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}

theorem rows_pos (ne : eqs≠[]) : 0<(compile eqs).1.length := by
  have count := (row_bounds eqs).1
  have len := List.length_pos_iff.mpr ne
  omega

theorem flo_lt (ne : eqs≠[]) : ((flo eqs:ℚ):ℝ)< -7 := f_lt (scale_bounds ne).1

theorem flo_le (ne : eqs≠[]) : ((flo eqs:ℚ):ℝ)≤ -100 := by
  have hn : (65:ℚ)≤scale eqs := by exact_mod_cast (scale_bounds ne).1
  have : flo eqs≤ -100 := by
    unfold flo D BankCoordinates.k; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) hn]
  exact_mod_cast this

theorem closed_fst_ge (a : ℝ) : IsClosed {q : Point | a≤q.1} :=
  isClosed_le (f:=fun _ : Point => a) (g:=fun q : Point => q.1) continuous_const continuous_fst
theorem closed_fst_le (a : ℝ) : IsClosed {q : Point | q.1≤a} :=
  isClosed_le (f:=fun q : Point => q.1) (g:=fun _ : Point => a) continuous_fst continuous_const
theorem closed_snd_ge (a : ℝ) : IsClosed {q : Point | a≤q.2} :=
  isClosed_le (f:=fun _ : Point => a) (g:=fun q : Point => q.2) continuous_const continuous_snd
theorem closed_snd_le (a : ℝ) : IsClosed {q : Point | q.2≤a} :=
  isClosed_le (f:=fun q : Point => q.2) (g:=fun _ : Point => a) continuous_snd continuous_const

theorem hub_eq (eqs : List ETRINV.Constraint) : RealizedDoors.hub eqs=
    Polygon.mk ((hubCycle (scale eqs) (compile eqs).1.length (PlacedSlots.starts eqs)).map ratPoint) := rfl

theorem wing_strip {q : Point} (hq : q∈EmittedGallery.unionWings eqs) : q.1≤1500 ∧ -5≤q.2 := by
  obtain ⟨e,he,hq⟩ := hq
  obtain ⟨r,j,path⟩ := SourceEntrances.present.mp he
  have s := (WingSeparation.placement path).2 q hq
  have d : (door j:ℝ)≤0 := by unfold door; push_cast; nlinarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]
  exact ⟨by linarith [s.2.1],s.2.2.1⟩

variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,g))
include ne out

theorem split_filled {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).filled) :
    q∈(RealizedDoors.hub eqs).filled ∨ q∈EmittedGallery.unionWings eqs := by
  rw [(GlobalShape.decomposition ne out).filled] at hq; exact hq

theorem P_range {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).filled) :
    ((2*flo eqs:ℚ):ℝ)≤q.2 ∧ q.2≤((top eqs:ℚ):ℝ) := by
  have hf := flo_lt ne
  rcases split_filled ne out hq with h|h
  · rw [hub_eq] at h; exact hub_range (rows_pos ne) (scale_bounds ne).1 h
  · have hl := flo_le ne
    obtain ⟨e,he,hq'⟩ := h
    obtain ⟨r,j,path⟩ := SourceEntrances.present.mp he
    have s2 := (WingSeparation.placement path).2 q hq'
    unfold top; push_cast at hf hl ⊢
    constructor <;> linarith [s2.2.2.1,s2.2.2.2]

theorem P_shaft_column {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).filled) (high : -6<q.2) (east : 1500<q.1) :
    ∃ x∈PlacedSlots.starts eqs, (x:ℝ)≤q.1 ∧ q.1≤((x+3/2:ℚ):ℝ) ∧ q.2≤((top eqs:ℚ):ℝ) := by
  rcases split_filled ne out hq with h|h
  · rw [hub_eq] at h; exact shaft_column (rows_pos ne) (scale_bounds ne).1 h high (by linarith)
  · linarith [(wing_strip h).1]

theorem P_foot_column {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).filled) (deep : q.2<((flo eqs:ℚ):ℝ)) :
    ∃ j<(compile eqs).1.length, ((fl j:ℚ):ℝ)≤q.1 ∧ q.1≤((fr j:ℚ):ℝ) := by
  rcases split_filled ne out hq with h|h
  · rw [hub_eq] at h
    obtain ⟨j,hj,a,b,_⟩ := foot_column (rows_pos ne) (scale_bounds ne).1 h deep
    exact ⟨j,hj,a,b⟩
  · have := flo_lt ne; linarith [(wing_strip h).2]

/-! ## Shaft decomposition -/

def SF (eqs : List ETRINV.Constraint) (x : ℚ) : Set Point :=
  {q | (x:ℝ)≤q.1 ∧ q.1≤((x+3/2:ℚ):ℝ) ∧ -6≤q.2 ∧ q.2≤((top eqs:ℚ):ℝ)}
def SR (P : Polygon) (x : ℚ) : Set Point :=
  P.filled∩{q | q.2≤ -6 ∨ q.1≤(x:ℝ)-1 ∨ ((x+5/2:ℚ):ℝ)≤q.1}

omit ne out in
theorem SF_closed (eqs : List ETRINV.Constraint) (x : ℚ) : IsClosed (SF eqs x) := by
  have e : SF eqs x={q : Point | (x:ℝ)≤q.1}∩{q : Point | q.1≤((x+3/2:ℚ):ℝ)}∩
      ({q : Point | -6≤q.2}∩{q : Point | q.2≤((top eqs:ℚ):ℝ)}) := by
    ext q; simp [SF,and_assoc]
  rw [e]
  exact ((closed_fst_ge _).inter (closed_fst_le _)).inter ((closed_snd_ge _).inter (closed_snd_le _))

omit ne out in
theorem SR_closed (P : Polygon) (x : ℚ) : IsClosed (SR P x) := by
  have e : SR P x=P.filled∩({q : Point | q.2≤ -6}∪({q : Point | q.1≤(x:ℝ)-1}∪{q : Point | ((x+5/2:ℚ):ℝ)≤q.1})) := by
    ext q; simp [SR]
  rw [e]
  exact (Jordan.isClosed_filled P).inter ((closed_snd_le _).union ((closed_fst_le _).union (closed_fst_ge _)))

theorem shaft_cover {x : ℚ} (hx : x∈PlacedSlots.starts eqs) :
    (Polygon.mk (v.map ratPoint)).filled⊆SF eqs x ∪ SR (Polygon.mk (v.map ratPoint)) x := by
  intro q hq
  have placed := RealizedHub.placed ne
  have far := placed.far x hx
  by_cases low : q.2≤ -6
  · exact Or.inr ⟨hq,Or.inl low⟩
  by_cases side : q.1≤(x:ℝ)-1 ∨ ((x+5/2:ℚ):ℝ)≤q.1
  · exact Or.inr ⟨hq,Or.inr side⟩
  push Not at low side
  have farR : (1970:ℝ)<x := by exact_mod_cast far
  obtain ⟨y,hy,a,b,c⟩ := P_shaft_column ne out hq low (by linarith [side.1])
  have same : y=x := by
    by_contra d
    have apart := placed_apart placed.sorted hy hx d
    rcases apart with h|h
    · have : ((y+10:ℚ):ℝ)≤x := by exact_mod_cast h
      push_cast at this b side; linarith [side.1]
    · have : ((x+10:ℚ):ℝ)≤y := by exact_mod_cast h
      push_cast at this side; linarith [side.2]
  subst same
  exact Or.inl ⟨a,b,low.le,c⟩

omit ne out in
theorem shaft_mouth (eqs : List ETRINV.Constraint) (P : Polygon) (x : ℚ) :
    SF eqs x∩SR P x⊆mouth (x:ℝ) ((x+3/2:ℚ):ℝ) (-6) := by
  rintro q ⟨⟨a,b,c,d⟩,_,h|h|h⟩
  · exact ⟨a,b,le_antisymm h c⟩
  · linarith
  · push_cast at b h; linarith

/-- Bands of the two far shaft corners. -/
theorem shaft_left {x : ℚ} (hx : x∈PlacedSlots.starts eqs) {z : Point}
    (hz : z∈(Polygon.mk (v.map ratPoint)).filled)
    (sees : (Polygon.mk (v.map ratPoint)).Sees ((x:ℝ),((top eqs:ℚ):ℝ)) z) :
    (x:ℝ)≤z.1 ∧ z.1≤(x:ℝ)+9/2 := by
  have hf := flo_lt ne
  have range := P_range ne out hz
  rcases shaft_cover ne out hx hz with h|h
  · obtain ⟨a,b,_⟩ := h; push_cast at b; constructor <;> linarith
  · have tip := left_tip (SF_closed eqs x) (SR_closed _ x) (shaft_cover ne out hx)
      (r:=((x+3/2:ℚ):ℝ)) (h:=-6) (by unfold top at *; push_cast at hf ⊢; linarith) (shaft_mouth eqs _ x)
      ⟨le_refl _,by push_cast; linarith,by unfold top at *; push_cast at hf ⊢; linarith,le_refl _⟩ h sees
    refine ⟨tip.1,?_⟩
    have depth : |z.2-((top eqs:ℚ):ℝ)|≤3*|(-6:ℝ)-((top eqs:ℚ):ℝ)| := by
      unfold top at *; push_cast at hf range ⊢
      rw [abs_of_nonpos (by linarith [range.2]),abs_of_neg (by linarith)]
      linarith [range.1]
    have := tip.2 depth
    push_cast at this; linarith

theorem shaft_right {x : ℚ} (hx : x∈PlacedSlots.starts eqs) {z : Point}
    (hz : z∈(Polygon.mk (v.map ratPoint)).filled)
    (sees : (Polygon.mk (v.map ratPoint)).Sees (((x+3/2:ℚ):ℝ),((top eqs:ℚ):ℝ)) z) :
    (x:ℝ)-3≤z.1 ∧ z.1≤(x:ℝ)+3/2 := by
  have hf := flo_lt ne
  have range := P_range ne out hz
  rcases shaft_cover ne out hx hz with h|h
  · obtain ⟨a,b,_⟩ := h; push_cast at b; constructor <;> linarith
  · have tip := right_tip (SF_closed eqs x) (SR_closed _ x) (shaft_cover ne out hx)
      (l:=(x:ℝ)) (h:=-6) (by unfold top at *; push_cast at hf ⊢; linarith) (shaft_mouth eqs _ x)
      ⟨by push_cast; linarith,le_refl _,by unfold top at *; push_cast at hf ⊢; linarith,le_refl _⟩ h sees
    have depth : |z.2-((top eqs:ℚ):ℝ)|≤3*|(-6:ℝ)-((top eqs:ℚ):ℝ)| := by
      unfold top at *; push_cast at hf range ⊢
      rw [abs_of_nonpos (by linarith [range.2]),abs_of_neg (by linarith)]
      linarith [range.1]
    have := tip.2 depth
    push_cast at this tip; constructor <;> linarith [tip.1]

/-! ## Foot decomposition -/

def FF (eqs : List ETRINV.Constraint) (j : Nat) : Set Point :=
  {q | ((fl j:ℚ):ℝ)≤q.1 ∧ q.1≤((fr j:ℚ):ℝ) ∧ ((2*flo eqs:ℚ):ℝ)≤q.2 ∧ q.2≤((flo eqs:ℚ):ℝ)}
def FR (eqs : List ETRINV.Constraint) (P : Polygon) (j : Nat) : Set Point :=
  P.filled∩{q | ((flo eqs:ℚ):ℝ)≤q.2 ∨ q.1≤((fl j:ℚ):ℝ)-1 ∨ ((fr j:ℚ):ℝ)+1≤q.1}

omit ne out in
theorem FF_closed (eqs : List ETRINV.Constraint) (j : Nat) : IsClosed (FF eqs j) := by
  have e : FF eqs j={q : Point | ((fl j:ℚ):ℝ)≤q.1}∩{q : Point | q.1≤((fr j:ℚ):ℝ)}∩
      ({q : Point | ((2*flo eqs:ℚ):ℝ)≤q.2}∩{q : Point | q.2≤((flo eqs:ℚ):ℝ)}) := by
    ext q; simp [FF,and_assoc]
  rw [e]
  exact ((closed_fst_ge _).inter (closed_fst_le _)).inter ((closed_snd_ge _).inter (closed_snd_le _))

omit ne out in
theorem FR_closed (eqs : List ETRINV.Constraint) (P : Polygon) (j : Nat) : IsClosed (FR eqs P j) := by
  have e : FR eqs P j=P.filled∩({q : Point | ((flo eqs:ℚ):ℝ)≤q.2}∪({q : Point | q.1≤((fl j:ℚ):ℝ)-1}∪
      {q : Point | ((fr j:ℚ):ℝ)+1≤q.1})) := by
    ext q; simp [FR]
  rw [e]
  exact (Jordan.isClosed_filled P).inter ((closed_snd_ge _).union ((closed_fst_le _).union (closed_fst_ge _)))

omit ne out in
theorem doors_apart {i j : Nat} (h : i≠j) : (door i:ℝ)+2000≤door j ∨ (door j:ℝ)+2000≤door i := by
  unfold door; push_cast
  rcases lt_or_gt_of_ne h with l|l
  · have : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast l
    right; linarith
  · have : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast l
    left; linarith

theorem foot_cover {j : Nat} :
    (Polygon.mk (v.map ratPoint)).filled⊆FF eqs j ∪ FR eqs (Polygon.mk (v.map ratPoint)) j := by
  intro q hq
  by_cases up : ((flo eqs:ℚ):ℝ)≤q.2
  · exact Or.inr ⟨hq,Or.inl up⟩
  by_cases side : q.1≤((fl j:ℚ):ℝ)-1 ∨ ((fr j:ℚ):ℝ)+1≤q.1
  · exact Or.inr ⟨hq,Or.inr side⟩
  push Not at up side
  obtain ⟨i,hi,a,b⟩ := P_foot_column ne out hq up
  have same : i=j := by
    by_contra d
    have apart := doors_apart d
    simp only [fl,fr] at a b side; push_cast at a b side
    rcases apart with h|h <;> linarith [side.1,side.2]
  subst same
  exact Or.inl ⟨a,b,(P_range ne out hq).1,up.le⟩

omit ne out in
theorem foot_mouth (eqs : List ETRINV.Constraint) (P : Polygon) (j : Nat) :
    FF eqs j∩FR eqs P j⊆mouth ((fl j:ℚ):ℝ) ((fr j:ℚ):ℝ) ((flo eqs:ℚ):ℝ) := by
  rintro q ⟨⟨a,b,c,d⟩,_,h|h|h⟩
  · exact ⟨a,b,le_antisymm d h⟩
  · linarith
  · linarith

theorem foot_left {j : Nat} {z : Point} (hz : z∈(Polygon.mk (v.map ratPoint)).filled)
    (sees : (Polygon.mk (v.map ratPoint)).Sees (((fl j:ℚ):ℝ),((2*flo eqs:ℚ):ℝ)) z) :
    ((fl j:ℚ):ℝ)≤z.1 ∧ z.1≤((fl j:ℚ):ℝ)+6/1000 := by
  have hf := flo_lt ne
  have range := P_range ne out hz
  have wid : ((fr j:ℚ):ℝ)=((fl j:ℚ):ℝ)+2/1000 := by unfold fl fr; push_cast; ring
  rcases foot_cover ne out hz with h|h
  · obtain ⟨a,b,_⟩ := h; rw [wid] at b; constructor <;> linarith
  · have tip := left_tip (FF_closed eqs j) (FR_closed eqs _ j) (foot_cover ne out)
      (r:=((fr j:ℚ):ℝ)) (h:=((flo eqs:ℚ):ℝ)) (by push_cast at hf ⊢; linarith) (foot_mouth eqs _ j)
      ⟨le_refl _,by rw [wid]; linarith,le_refl _,by push_cast at hf ⊢; linarith⟩ h sees
    refine ⟨tip.1,?_⟩
    have depth : |z.2-((2*flo eqs:ℚ):ℝ)|≤3*|((flo eqs:ℚ):ℝ)-((2*flo eqs:ℚ):ℝ)| := by
      unfold top at range; push_cast at hf range ⊢
      rw [abs_of_nonneg (by linarith [range.1]),abs_of_pos (by linarith)]
      linarith [range.2]
    have := tip.2 depth
    rw [wid] at this; linarith

theorem foot_right {j : Nat} {z : Point} (hz : z∈(Polygon.mk (v.map ratPoint)).filled)
    (sees : (Polygon.mk (v.map ratPoint)).Sees (((fr j:ℚ):ℝ),((2*flo eqs:ℚ):ℝ)) z) :
    ((fr j:ℚ):ℝ)-6/1000≤z.1 ∧ z.1≤((fr j:ℚ):ℝ) := by
  have hf := flo_lt ne
  have range := P_range ne out hz
  have wid : ((fr j:ℚ):ℝ)=((fl j:ℚ):ℝ)+2/1000 := by unfold fl fr; push_cast; ring
  rcases foot_cover ne out hz with h|h
  · obtain ⟨a,b,_⟩ := h; rw [wid] at b ⊢; constructor <;> linarith
  · have tip := right_tip (FF_closed eqs j) (FR_closed eqs _ j) (foot_cover ne out)
      (l:=((fl j:ℚ):ℝ)) (h:=((flo eqs:ℚ):ℝ)) (by push_cast at hf ⊢; linarith) (foot_mouth eqs _ j)
      ⟨by rw [wid]; linarith,le_refl _,le_refl _,by push_cast at hf ⊢; linarith⟩ h sees
    have depth : |z.2-((2*flo eqs:ℚ):ℝ)|≤3*|((flo eqs:ℚ):ℝ)-((2*flo eqs:ℚ):ℝ)| := by
      unfold top at range; push_cast at hf range ⊢
      rw [abs_of_nonneg (by linarith [range.1]),abs_of_pos (by linarith)]
      linarith [range.2]
    have := tip.2 depth
    rw [wid] at this ⊢; constructor <;> linarith [tip.1]

end Emitted

end ArtGallery.Orthogonal.BoundaryPoint.HubRoles
end
