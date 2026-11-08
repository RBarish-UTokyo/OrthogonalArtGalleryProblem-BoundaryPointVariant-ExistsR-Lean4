module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyFloor
public import ArtGallery.Orthogonal.BoundaryPoint.HubSpots
public import ArtGallery.Orthogonal.BoundaryPoint.HubOwners
public import ArtGallery.Orthogonal.BoundaryPoint.OwnerAssembly
public import ArtGallery.Orthogonal.BoundaryPoint.BankPitch

/-! # Outside guards are blind to the copy targets of a wing

A copy target of row `i` lies above height `7/3` on a sight line from a base
position `x0+τ` of the floor (`x0` the slot of the copied variable) through a
point of the row's door. A guard of any other role cannot see it:

* a guard of another row's private role stands in that row's wing (two seams);
* a guard of another base slot is on the floor (pitch margin) or at least at the
  low roof of its shaft column (blind to every wing);
* a guard of a door step is below the floor (its sight line would cross the floor
  far west of the slots), on the low roof near its door, or on a cap top. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GlobalBlind
open BankCoordinates CompiledSize CatalogPlan HubRoles HubOwners

section Numbers

theorem W_le (n : Nat) (hn : 1≤n) : (0:ℝ)≤W n ∧ (W n:ℝ)≤1 := by
  unfold W; have : (1:ℝ)≤n := by exact_mod_cast hn
  push_cast; constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

theorem D_ge (n : Nat) (hn : 1≤n) : (1:ℝ)≤D n := by
  unfold D k; have : (1:ℝ)≤n := by exact_mod_cast hn
  push_cast; nlinarith

/-- A slot of bank at least one lies far east: beyond `40*n^2`. -/
theorem slot_far (n bank rank : Nat) (hb : 1≤bank) : 40*(n:ℝ)^2≤slotX n bank rank := by
  unfold slotX k delta W
  have : (1:ℝ)≤bank := by exact_mod_cast hb
  push_cast
  have h1 : (0:ℝ)≤1/(320*n) := by positivity
  have h2 : (0:ℝ)≤rank*(125*n) := by positivity
  nlinarith [sq_nonneg (n:ℝ)]

/-- The base rate of an address and a row lies in `[0,2]`. -/
theorem rate_bounds {n bank rank row : Nat} (hn : 1≤n) (hb : bank∈banks) (hr : rank≤n) (hrow : row≤n) :
    (0:ℝ)≤baseRate n bank rank row ∧ (baseRate n bank rank row:ℝ)≤2 := by
  have hb' : 1≤bank ∧ bank≤1000 := by simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at hb; omega
  have := BankPitch.base_rate_bound (n:=n) (bank:=bank) (rank:=rank) (row:=row) (by exact_mod_cast hn)
    ⟨by exact_mod_cast hb'.1,by exact_mod_cast hb'.2⟩ ⟨by positivity,by exact_mod_cast hr⟩ ⟨by positivity,by exact_mod_cast hrow⟩
  unfold baseRate; push_cast
  rw [cast_slotX,cast_W,cast_D]
  unfold door; push_cast
  have e : BankPitch.slot n bank rank-(-2000*(row:ℝ))-BankPitch.width n=BankPitch.slot n bank rank+2000*row-BankPitch.width n := by ring
  rw [e]; exact this

end Numbers

section Blind
variable {eqs : List ETRINV.Constraint} {v : List RectContour.Vertex} {g : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,g))
include ne out

/-- The copy target of a row: above height `7/3` on a base sight line through the door. -/
noncomputable def target (n i bank rank : Nat) (τ c y : ℝ) : Point :=
  ((door i:ℝ)+c+(c-((W n:ℝ)+(baseRate n bank rank i:ℝ)*(D n:ℝ)+τ))*(y-1)/(D n:ℝ),y)

theorem in_wings {r : CatalogPlan.Row} {i : Nat} {e : ContourJoin.Entrance} (path : WingSeparation.emitted eqs r i e)
    {z : Point} (hz : z∈(RealizedDoors.wing e).filled) : z∈EmittedGallery.unionWings eqs :=
  ⟨e,SourceEntrances.present.mpr ⟨r,i,path⟩,hz⟩

/-- A hub point below the wings' lowest height belongs to the rest of every wing's join. -/
theorem low_rest {r : CatalogPlan.Row} {i : Nat} {e : ContourJoin.Entrance} (path : WingSeparation.emitted eqs r i e)
    {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).filled) (low : q.2< -5) :
    q∈(GalleryBoundary.joined path out).rest := by
  have f := (GalleryBoundary.joined path out).fill
  rw [f] at hq
  rcases hq with h|h
  · exfalso; linarith [(wing_strip (in_wings ne out path h)).2]
  · exact h

/-- A guard of another base slot sees no copy target of the row. -/
theorem slot_blind {r : CatalogPlan.Row} {i : Nat} {e : ContourJoin.Entrance} (path : WingSeparation.emitted eqs r i e)
    {a0 : Nat × Nat} (ha0 : a0∈(compile eqs).2) {x : ℚ} (hx : x∈PlacedSlots.starts eqs)
    (hne : x≠slotX (scale eqs) a0.1 a0.2) {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).boundary)
    (h0 : (x:ℝ)≤q.1) (h1 : q.1≤((x+3/2:ℚ):ℝ))
    {τ c y : ℝ} (τ0 : 0≤τ) (τ1 : τ≤3/2) (c0 : 0≤c) (c1 : c≤(W (scale eqs):ℝ)) (hy : 7/3≤y)
    (hz : target (scale eqs) i a0.1 a0.2 τ c y∈(RealizedDoors.wing e).filled) :
    ¬(Polygon.mk (v.map ratPoint)).Sees q (target (scale eqs) i a0.1 a0.2 τ c y) := by
  intro sees
  set n := scale eqs
  have hn : 65≤n := (scale_bounds ne).1
  have hn1 : 1≤n := by omega
  rcases HubSpots.column ne out hq hx h0 h1 with hf|hhigh
  · let J := GalleryBoundary.joined path out
    have hqR : q∈J.rest := low_rest ne out path (Jordan.boundary_subset_filled _ hq)
      (by rw [hf]; have := flo_lt ne; linarith)
    have hD := D_ge n hn1
    have hW := W_le n hn1
    have hgf : q.2=1-(D n:ℝ) := by rw [hf]; unfold flo; push_cast; rfl
    have near := CopyFloor.floor_near hW.1 J (by linarith) (by linarith : (0:ℝ)<y-1) c0 c1 hqR hgf
      (by simpa [target,add_sub_cancel] using hz) (by simpa [target,add_sub_cancel] using sees)
    -- the own slot
    have own : (door i:ℝ)+(W n:ℝ)+(baseRate n a0.1 a0.2 i:ℝ)*(D n:ℝ)=slotX n a0.1 a0.2 := by
      have : (D n:ℝ)≠0 := by linarith
      unfold baseRate; push_cast; field_simp; ring
    rw [show (door i:ℝ)+(W n:ℝ)+(baseRate n a0.1 a0.2 i:ℝ)*(D n:ℝ)+τ=(slotX n a0.1 a0.2:ℝ)+τ by rw [←own]] at near
    -- the pitch margin
    have margin := BankPitch.projected_margin (n:=n) (h:=y-1) (by exact_mod_cast hn1) (by linarith)
    rw [←cast_W,←cast_D] at margin
    have hpitch : (BankPitch.pitch n:ℝ)=(delta n:ℝ) := by simp [delta,BankPitch.pitch]
    rw [hpitch] at margin
    have bound : (W n:ℝ)*((y-1)+(D n:ℝ))/(y-1)<(delta n:ℝ)-3/2 := by
      rw [div_lt_iff₀ (by linarith)]; linarith
    have own_mem : slotX n a0.1 a0.2∈PlacedSlots.starts eqs := List.mem_map.mpr ⟨a0,ha0,rfl⟩
    rcases HubFloor.pw_cases (PlacedSlots.increasing ne) hx own_mem with e|lt|gt
    · exact hne e
    · have : (x:ℝ)+(delta n:ℝ)≤slotX n a0.1 a0.2 := by exact_mod_cast lt
      push_cast at h1
      have := (abs_le.mp near).1
      linarith
    · have : (slotX n a0.1 a0.2:ℝ)+(delta n:ℝ)≤x := by exact_mod_cast gt
      have := (abs_le.mp near).2
      linarith
  · exact HubSpots.high_blind ne out hx h0 hhigh (in_wings ne out path hz) sees


theorem hub_rest {r : CatalogPlan.Row} {i : Nat} {e : ContourJoin.Entrance} (path : WingSeparation.emitted eqs r i e)
    {q : Point} (hq : q∈(RealizedDoors.hub eqs).filled) : q∈(GalleryBoundary.joined path out).rest := by
  show q∈(RealizedDoors.hub eqs).filled∪_
  exact Or.inl hq

/-- A guard of a door step sees no copy target of the row. -/
theorem step_blind {r : CatalogPlan.Row} {i : Nat} {e : ContourJoin.Entrance} (path : WingSeparation.emitted eqs r i e)
    (hi : i<scale eqs) {a0 : Nat × Nat} (ha0 : a0∈(compile eqs).2) {m : Nat} (hm : m<(compile eqs).1.length)
    {q : Point} (hq : q∈(Polygon.mk (v.map ratPoint)).boundary) (hub : q∈(RealizedDoors.hub eqs).filled)
    (h0 : ((fl m:ℚ):ℝ)≤q.1) (h1 : q.1≤((fr m:ℚ):ℝ))
    {τ c y : ℝ} (τ0 : 0≤τ) (τ1 : τ≤3/2) (c0 : 0≤c) (c1 : c≤(W (scale eqs):ℝ)) (hy : 7/3≤y)
    (hz : target (scale eqs) i a0.1 a0.2 τ c y∈(RealizedDoors.wing e).filled) :
    ¬(Polygon.mk (v.map ratPoint)).Sees q (target (scale eqs) i a0.1 a0.2 τ c y) := by
  intro sees
  set n := scale eqs
  have hn : 65≤n := (scale_bounds ne).1
  have hn1 : 1≤n := by omega
  let J := GalleryBoundary.joined path out
  have hD := D_ge n hn1
  have hW := W_le n hn1
  have spec := CompiledAddresses.address_spec eqs ha0
  have hb := rate_bounds (row:=i) hn1 spec.1 spec.2.le hi.le
  have dm : (door m:ℝ)≤0 := by unfold door; push_cast; nlinarith [(Nat.cast_nonneg m : (0:ℝ)≤m)]
  have di : (door i:ℝ)≤0 := by unfold door; push_cast; nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have gap : m=i ∨ (door m:ℝ)+2000≤door i ∨ (door i:ℝ)+2000≤door m := by
    rcases lt_trichotomy m i with h|h|h
    · right; right; have : (m:ℝ)+1 ≤ i := by exact_mod_cast h
      unfold door; push_cast; linarith
    · left; exact h
    · right; left; have : (i:ℝ)+1≤m := by exact_mod_cast h
      unfold door; push_cast; linarith
  have hfl : ((fl m:ℚ):ℝ)=(door m:ℝ)+100-1/1000 := by unfold HubRoles.fl; push_cast; ring
  have hfr : ((fr m:ℚ):ℝ)=(door m:ℝ)+100+1/1000 := by unfold HubRoles.fr; push_cast; ring
  rcases HubSpots.foot ne out hq hub hm h0 h1 with low|roof|top
  all_goals rw [hfl] at h0; rw [hfr] at h1
  · -- below the floor: the sight line crosses the floor far west of every slot
    have zy : (target n i a0.1 a0.2 τ c y).2=y := rfl
    have hf := flo_lt ne
    obtain ⟨p,hp,py,px⟩ := CopyFloor.at_height (z:=target n i a0.1 a0.2 τ c y) low (by rw [zy]; linarith) (by rw [zy]; linarith)
    have pP : p∈(Polygon.mk (v.map ratPoint)).filled := sees hp
    have pR : p∈J.rest := low_rest ne out path pP (by rw [py]; linarith)
    have psees : (Polygon.mk (v.map ratPoint)).Sees p (target n i a0.1 a0.2 τ c y) :=
      Set.Subset.trans (CopyOutside.sub_segment hp) sees
    have pf : p.2=1-(D n:ℝ) := by rw [py]; unfold flo; push_cast; rfl
    have near := CopyFloor.floor_near hW.1 J (by linarith) (by linarith : (0:ℝ)<y-1) c0 c1 pR pf
      (by simpa [target,add_sub_cancel] using hz) (by simpa [target,add_sub_cancel] using psees)
    have own : (door i:ℝ)+(W n:ℝ)+(baseRate n a0.1 a0.2 i:ℝ)*(D n:ℝ)=slotX n a0.1 a0.2 := by
      have : (D n:ℝ)≠0 := by linarith
      unfold baseRate; push_cast; field_simp; ring
    rw [show (door i:ℝ)+(W n:ℝ)+(baseRate n a0.1 a0.2 i:ℝ)*(D n:ℝ)+τ=(slotX n a0.1 a0.2:ℝ)+τ by rw [←own]] at near
    have margin := BankPitch.projected_margin (n:=n) (h:=y-1) (by exact_mod_cast hn1) (by linarith)
    rw [←cast_W,←cast_D] at margin
    have bound : (W n:ℝ)*((y-1)+(D n:ℝ))/(y-1)<125*(n:ℝ) := by
      rw [div_lt_iff₀ (by linarith)]; unfold BankPitch.pitch at margin; nlinarith
    have far := slot_far n a0.1 a0.2 (by simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at spec; omega)
    have zx := (wing_strip (in_wings ne out path hz)).1
    have hnr : (65:ℝ)≤n := by exact_mod_cast hn
    have pxle : p.1≤1500 := le_trans px (max_le (by linarith) zx)
    have := (abs_le.mp near).1
    nlinarith
  · -- on the low roof: near the row's door, far from the foot
    have qR : q∈J.rest := hub_rest ne out path hub
    have near := CopyFloor.roof_near hW.1 hW.2 J hD (by linarith : (4/3:ℝ)≤y-1) c0 c1 τ0 τ1 hb.1 hb.2 qR roof
      (by simpa [target,add_sub_cancel] using hz) (by simpa [target,add_sub_cancel] using sees)
    rcases gap with rfl|g1|g2
    · linarith [near.2]
    · linarith [near.1]
    · linarith [near.2]
  · -- on a cap top: a level guard off the door
    have qR : q∈J.rest := hub_rest ne out path hub
    apply CopyOutside.level_guard J rfl rfl qR hz (by show 1<y; linarith) (by rw [top]) _ sees
    intro hs
    obtain ⟨t,t0,t1,ht⟩ := hs
    have hx : q.1=(door i:ℝ)+t*((door i:ℝ)+(W n:ℝ)-(door i:ℝ)) := by rw [ht]
    have : q.1≤(door i:ℝ)+1 := by rw [hx]; nlinarith [hW.2]
    have : (door i:ℝ)≤q.1 := by rw [hx]; nlinarith [hW.1]
    rcases gap with rfl|g1|g2 <;> linarith


/-- A guard standing in another row's wing sees no copy target of the row. -/
theorem private_blind {r r' : CatalogPlan.Row} {i i' : Nat} {e e' : ContourJoin.Entrance}
    (path : WingSeparation.emitted eqs r i e) (path' : WingSeparation.emitted eqs r' i' e') (hii : i'≠i)
    {q : Point} (hq : q∈(RealizedDoors.wing e').filled) {n bank rank : Nat} {τ c y : ℝ} (hy : 7/3≤y)
    (hz : target n i bank rank τ c y∈(RealizedDoors.wing e).filled) :
    ¬(Polygon.mk (v.map ratPoint)).Sees q (target n i bank rank τ c y) :=
  CopyOutside.two_seams (GalleryBoundary.joined path out) (GalleryBoundary.joined path' out) rfl rfl rfl rfl
    (WingSeparation.disjoint path path' hii.symm) hq hz (by show y≠1; intro h; linarith)

end Blind

end ArtGallery.Orthogonal.BoundaryPoint.GlobalBlind
end
