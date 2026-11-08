module

public import ArtGallery.Orthogonal.BoundaryPoint.WingSpec
public import ArtGallery.Orthogonal.BoundaryPoint.ForwardHub
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalMarks
public import ArtGallery.Orthogonal.BoundaryPoint.BudgetCount
public import ArtGallery.Orthogonal.BoundaryPoint.GuardPad
public import ArtGallery.Orthogonal.BoundaryPoint.CopyGlobal
public import ArtGallery.Orthogonal.BoundaryPoint.GlobalShape

/-! # Completeness: a satisfying assignment gives a boundary guard set of `g` guards

Given values `val a ∈ [1/2,2]` for the addresses of the compiled source satisfying every row
relation, place one guard per role: a base guard on the floor of each slot at offset
`val a - 1/2`, a step guard on each cap top at `door j + 100`, and in each wing the stationary
roles at their record point and the moving roles on their spot at the offset of their channel.
The hub is covered by `HubCover.hub_cover`; each wing, moved to its local frame, by its
catalogue entry (`WingSpec.Cover`), whose base guards see the door segment through the hub. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.Forward
open Set RectContour BoundaryChart BankCoordinates CompiledSize CatalogPlan CatalogRanks HubOwners
open ChartDrawing PinTransport Hardening.Invariance RoomGrid ContourJoin CompiledAddresses ArtGallery.Orthogonal.Hard

section Place
variable (eqs : List ETRINV.Constraint) (val : Addr → ℝ) (mvOf : Nat → List (Nat × Nat × Index × Index))

/-- The floor offset of the base guard of a slot: the value of its address, minus `1/2`. -/
noncomputable def tOf (p : ℚ) : ℝ := val ((compile eqs).2.getD ((slots eqs).idxOf p) (0,0))-1/2

/-- The offset of channel `c` of a row. -/
noncomputable def rowτ (r : CatalogPlan.Row) (c : Nat) : ℝ := val (((profileBanks r.1).zip r.2).getD c (0,0))-1/2

/-- The canonical guard of a role. -/
noncomputable def place : HubRole eqs ⊕ PrivateRoles.Role eqs → Point
  | .inl (.inl k) => (((sx eqs k:ℚ):ℝ)+tOf eqs val (sx eqs k),((1-D (scale eqs):ℚ):ℝ))
  | .inl (.inr j) => (((door (j:Nat):ℚ):ℝ)+100,1)
  | .inr x =>
    match (mvOf ((PrivateRoles.rows eqs)[x.1]).1).lookup (x.2:Nat) with
    | some m => shift (door (x.1:Nat)) (Geometry.lerp (ratPoint ((PrivateRoles.record eqs x).getD 1 (0,0)))
        (ratPoint ((PrivateRoles.record eqs x).getD 2 (0,0))) (rowτ val ((PrivateRoles.rows eqs)[x.1]) m.1*(2/3)))
    | none => HighStep.moved (door (x.1:Nat)) ((PrivateRoles.record eqs x).getD 0 (0,0))

end Place

section Facts
variable {eqs : List ETRINV.Constraint} {val : Addr → ℝ}

theorem slots_eq : slots eqs=(compile eqs).2.map fun a => slotX (scale eqs) a.1 a.2 := rfl

theorem nodup (ne : eqs≠[]) : (slots eqs).Nodup :=
  (RealizedHub.placed ne).sorted.imp (fun h e => by subst e; linarith)

/-- The base guard of the slot of an address has the address's offset. -/
theorem tOf_slot (ne : eqs≠[]) {a : Addr} (ha : a∈(compile eqs).2) :
    tOf eqs val (slotX (scale eqs) a.1 a.2)=val a-1/2 := by
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem ha
  have hj' : j<(slots eqs).length := by simpa [slots_eq] using hj
  have e : (slots eqs)[j]=slotX (scale eqs) ((compile eqs).2[j]).1 ((compile eqs).2[j]).2 := by
    simp [slots_eq]
  have i : (slots eqs).idxOf (slotX (scale eqs) ((compile eqs).2[j]).1 ((compile eqs).2[j]).2)=j := by
    rw [← e]; exact List.Nodup.idxOf_getElem (nodup ne) j hj'
  simp only [tOf,i,List.getD_eq_getElem _ _ hj]

theorem tOf_range (hv : ∀ a, DerivedAlgebra.InRange (val a)) (p : ℚ) : 0≤tOf eqs val p ∧ tOf eqs val p≤3/2 := by
  have := hv ((compile eqs).2.getD ((slots eqs).idxOf p) (0,0))
  unfold tOf; constructor <;> linarith [this.1,this.2]

theorem rowτ_range (hv : ∀ a, DerivedAlgebra.InRange (val a)) (r : CatalogPlan.Row) (c : Nat) :
    0≤rowτ val r c ∧ rowτ val r c≤3/2 := by
  have := hv (((profileBanks r.1).zip r.2).getD c (0,0))
  unfold rowτ; constructor <;> linarith [this.1,this.2]

/-- The hub polygon with its number of doors. -/
theorem hub_eq (ne : eqs≠[]) : ∃ K, (compile eqs).1.length=K+1 ∧
    RealizedDoors.hub eqs=HubPoints.HP (scale eqs) K (PlacedSlots.starts eqs) := by
  obtain ⟨K,hK⟩ := Nat.exists_eq_add_of_lt (HubRoles.rows_pos ne)
  refine ⟨K,by omega,?_⟩
  simp only [RealizedDoors.hub,HubPoints.HP]; rw [hK,Nat.zero_add]

theorem big (ne : eqs≠[]) : ∀ x∈PlacedSlots.starts eqs, (x:ℝ)+20≤11/10*(D (scale eqs):ℝ) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨hb,hr⟩ := CompiledAddresses.address_spec eqs ha
  have b1000 : a.1≤1000 := by
    simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at hb; omega
  exact ForwardHub.big (by have := (scale_bounds ne).1; omega) b1000 hr.le

/-- Points of a door segment. -/
theorem seam_pt {n j : Nat} {p : Point} (hp : p∈RealizedDoors.seam n j) :
    p.2=1 ∧ (door j:ℝ)≤p.1 ∧ p.1≤(door j:ℝ)+(W n:ℝ) := by
  obtain ⟨t,t0,t1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hp
  have hW : (0:ℝ)≤W n := by unfold W; positivity
  simp only [Geometry.lerp_fst,Geometry.lerp_snd]
  refine ⟨by ring,by nlinarith,by nlinarith⟩

end Facts

section Cover
variable {eqs : List ETRINV.Constraint} {val : Addr → ℝ} (mvOf : Nat → List (Nat × Nat × Index × Index))

/-- Every filled point of the hub is seen in the hub by a base or step guard. -/
theorem hub_part (ne : eqs≠[]) (hv : ∀ a, DerivedAlgebra.InRange (val a)) {z : Point}
    (hz : z∈(RealizedDoors.hub eqs).filled) : ∃ ρ, (RealizedDoors.hub eqs).Sees (place eqs val mvOf ρ) z := by
  obtain ⟨K,hK,he⟩ := hub_eq ne
  rw [he] at hz ⊢
  rcases HubCover.hub_cover (scale_bounds ne).1 (RealizedHub.placed ne) (big ne) (tOf eqs val)
    (fun p _ => tOf_range hv p) hz with ⟨p,hp,h⟩|⟨j,hj,h⟩
  · have hi : (slots eqs).idxOf p<(slots eqs).length := List.idxOf_lt_length_iff.mpr hp
    refine ⟨.inl (.inl ⟨_,hi⟩),?_⟩
    have e : sx eqs ⟨_,hi⟩=p := List.getElem_idxOf hi
    simp only [place,e]; exact h
  · refine ⟨.inl (.inr ⟨j,by omega⟩),?_⟩
    simpa [place] using h

/-- The hub guards stand on the boundary of the gallery. -/
theorem hub_on (ne : eqs≠[]) {v : List Vertex} {g : Nat} (out : CandidateWord.vertices eqs=some (v,g))
    (hv : ∀ a, DerivedAlgebra.InRange (val a)) (ρ : HubRole eqs) :
    place eqs val mvOf (.inl ρ)∈(Polygon.mk (v.map ratPoint)).boundary := by
  obtain ⟨K,hK,he⟩ := hub_eq ne
  have onHub : place eqs val mvOf (.inl ρ)∈(RealizedDoors.hub eqs).boundary := by
    rw [he]
    rcases ρ with k|j
    · exact ForwardHub.base_on (RealizedHub.placed ne) (sx_mem eqs k) (tOf_range hv _)
    · exact ForwardHub.step_on (by have := j.isLt; omega)
  refine (GalleryBoundary.hub_iff ne out (Jordan.boundary_subset_filled _ onHub) ?_).mpr onHub
  intro r j' e path hs
  obtain ⟨y1,x0,x1⟩ := seam_pt hs
  have hW := ForwardHub.W_le (scale_bounds ne).1
  rcases ρ with k|j
  · have F7 := HubCells.F_lt (scale_bounds ne).1
    simp only [place] at y1; linarith
  · simp only [place] at x0 x1
    unfold door at x0 x1; push_cast at x0 x1
    rcases lt_trichotomy (j:Nat) j' with h|h|h
    · have : ((j:Nat):ℝ)+1≤j' := by exact_mod_cast h
      linarith
    · subst h; linarith
    · have : (j':ℝ)+1≤((j:Nat):ℝ) := by exact_mod_cast h
      linarith

end Cover

section Private
variable {eqs : List ETRINV.Constraint} {val : Addr → ℝ} (mvOf : Nat → List (Nat × Nat × Index × Index))

theorem shift_lerp (d : ℚ) (p q : Point) (θ : ℝ) :
    shift d (Geometry.lerp p q θ)=Geometry.lerp (shift d p) (shift d q) θ := by
  simp only [shift_pt,Geometry.lerp]; ext <;> simp; ring

theorem shift_rat (d : ℚ) (v : Vertex) : shift d (ratPoint v)=HighStep.moved d v := by
  simp only [shift_pt,HighStep.moved,ratPoint]; ext <;> simp

theorem catalog_get {tag : Nat} (h : tag<14) : ∃ t, catalog[tag]?=some t :=
  ⟨catalog[tag]'(by simpa [catalog] using h),List.getElem?_eq_getElem _⟩

/-- The records of a row are the template records at the row's door. -/
theorem records_eq {r : CatalogPlan.Row} {j : Nat} {t : Template} (ht : catalog[r.1]?=some t) :
    GlobalPins.emitted eqs r j=GlobalPins.records t (scale eqs) j r.2 :=
  CopyGlobal.choose_get catalog _ r.1 [] ht

/-- The guards of the private roles stand on the boundary of the gallery. -/
theorem private_on {v : List Vertex} {g : Nat} (out : CandidateWord.vertices eqs=some (v,g))
    (hv : ∀ a, DerivedAlgebra.InRange (val a)) (x : PrivateRoles.Role eqs) :
    place eqs val mvOf (.inr x)∈(Polygon.mk (v.map ratPoint)).boundary := by
  have path := PrivateRoles.entrance_spec eqs x.1
  have member := List.fst_mem_of_mem_zipIdx path.1
  obtain ⟨t,ht⟩ := catalog_get (CandidateTotal.valid_row member).1
  have hrec : PrivateRoles.record eqs x∈GlobalPins.records t (scale eqs) x.1 ((PrivateRoles.rows eqs)[x.1]).2 := by
    rw [← records_eq ht]; exact List.getElem_mem _
  have len : (PrivateRoles.record eqs x).length=6 := PrivateRoles.six (List.getElem_mem _)
  obtain ⟨c,a,b,u,w,y,hl⟩ := PrivateRoles.destruct len
  have req (e : Vertex × Vertex) (he : e∈WingMarks.perRole (PrivateRoles.record eqs x)) :
      e∈GlobalMarks.emitted eqs (PrivateRoles.rows eqs)[x.1] x.1 := by
    unfold GlobalMarks.emitted
    rw [CopyGlobal.choose_get catalog _ _ [] ht]
    exact List.mem_flatMap.mpr ⟨_,hrec,he⟩
  dsimp only [place]
  split
  · next m hm =>
    have hb := GlobalMarks.boundary path out (req (a,b) (by rw [hl]; simp [WingMarks.perRole]))
    apply hb
    rw [hl]; simp only [List.getD_cons_succ,List.getD_cons_zero]
    rw [shift_lerp,shift_rat,shift_rat]
    have := rowτ_range hv ((PrivateRoles.rows eqs)[x.1]) m.1
    exact Geometry.lerp_mem_segment _ _ (by linarith) (by linarith)
  · next hm =>
    have hb := GlobalMarks.boundary path out (req (c,c) (by rw [hl]; simp [WingMarks.perRole]))
    apply hb
    rw [hl]; simp only [List.getD_cons_zero]
    exact ⟨0,le_rfl,zero_le_one,by simp [Geometry.lerp]⟩

end Private

section Wing
variable {eqs : List ETRINV.Constraint} {val : Addr → ℝ} {mvOf : Nat → List (Nat × Nat × Index × Index)}

theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β}, l.lookup a=some b → (a,b)∈l
  | [],_,_,h => by simp at h
  | (x,y)::l,a,b,h => by
    simp only [List.lookup] at h
    split at h
    · next e =>
      have : a=x := by simpa using e
      subst this; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem range_map {α β : Type} (f : α → β) (d : α) (l : List α) :
    (List.range l.length).map (fun c => f (l.getD c d))=l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map,List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem cast_getD (xs : List ℚ) (a : Nat) : (xs.map (fun q : ℚ => (q:ℝ))).getD a 0=((xs.getD a 0:ℚ):ℝ) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases xs[a]? <;> simp

/-- Every filled point of a wing is seen by a canonical guard. -/
theorem wing_part (ne : eqs≠[]) {v : List Vertex} {g : Nat} (out : CandidateWord.vertices eqs=some (v,g))
    (hv : ∀ a, DerivedAlgebra.InRange (val a)) (phys : Physical (compile eqs) val)
    (cat : ∀ tag t, catalog[tag]?=some t → WingSpec.Entry t tag (mvOf tag))
    {r : CatalogPlan.Row} {j : Nat} {e : Entrance} (path : WingSeparation.emitted eqs r j e)
    {z : Point} (hz : z∈(RealizedDoors.wing e).filled) :
    ∃ ρ, (Polygon.mk (v.map ratPoint)).Sees (place eqs val mvOf ρ) z := by
  have member := List.fst_mem_of_mem_zipIdx path.1
  obtain ⟨tag14,size⟩ := CandidateTotal.valid_row member
  obtain ⟨t,ht⟩ := catalog_get tag14
  obtain ⟨idx,cov,rec,six,mvf⟩ := cat r.1 t ht
  have hn := (scale_bounds ne).1
  have hj := (program_door eqs path.1).le
  have hr : ∀ i∈r.2,i≤scale eqs := fun i hi => (program_ranks eqs member hi).le
  obtain ⟨fill,-,-,Lw⟩ := CopyGlobal.frame2 path out ht
  have shape := GlobalShape.decomposition ne out
  have hubSub : (RealizedDoors.hub eqs).filled⊆(Polygon.mk (v.map ratPoint)).filled := by
    rw [shape.filled]; exact subset_union_left
  obtain ⟨K,hK,he⟩ := hub_eq ne
  have hjK : j<K+1 := by rw [← hK]; exact (List.mem_zipIdx' path.1).1
  set n := scale eqs with hn_def
  set d := door j with hd
  have hn0 : 0<n := by omega
  have hz' : shift (-d) z∈(BoundaryChart.actual t.chart (ShapeRefs.join (t.corridor.coords
      ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n)))) (t.room.coords (1/n)))).filled := by
    rw [Lw]; exact ⟨z,hz,rfl⟩
  have sub : (BoundaryChart.actual t.chart (ShapeRefs.join (t.corridor.coords
      ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n)))) (t.room.coords (1/n)))).filled ⊆
      (mapPoly (shift (-d)) (Polygon.mk (v.map ratPoint))).filled := by
    rw [fill]; exact subset_union_left
  have hl : ((profileBanks r.1).zip r.2).length=(profileBanks r.1).length := by simp [size]
  -- the base guard of channel `c` in the local frame
  have hbase : ∀ c<(profileBanks r.1).length, ∃ k : Fin (slots eqs).length,
      ((sx eqs k:ℚ):ℝ)=(slotX n (((profileBanks r.1).zip r.2).getD c (0,0)).1 (((profileBanks r.1).zip r.2).getD c (0,0)).2:ℚ) ∧
      WingSpec.base r.1 ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) (rowτ val r) c=
        shift (-d) (place eqs val mvOf (.inl (.inl k))) := by
    intro c hc
    set a := ((profileBanks r.1).zip r.2).getD c (0,0) with ha_def
    have hcz : c<((profileBanks r.1).zip r.2).length := by rw [hl]; exact hc
    have ea : a=((profileBanks r.1)[c],r.2[c]'(by rw [size]; exact hc)) := by
      rw [ha_def,List.getD_eq_getElem _ _ hcz,List.getElem_zip]
    have ha : a∈(compile eqs).2 := ValueChain.zip_mem eqs member a (by rw [ha_def,List.getD_eq_getElem _ _ hcz]; exact List.getElem_mem _)
    have hp : slotX n a.1 a.2∈slots eqs := List.mem_map.mpr ⟨a,ha,rfl⟩
    have hi : (slots eqs).idxOf (slotX n a.1 a.2)<(slots eqs).length := List.idxOf_lt_length_iff.mpr hp
    refine ⟨⟨_,hi⟩,by rw [show sx eqs ⟨_,hi⟩=slotX n a.1 a.2 from List.getElem_idxOf hi],?_⟩
    have esx : sx eqs ⟨_,hi⟩=slotX n a.1 a.2 := List.getElem_idxOf hi
    obtain ⟨cW,cD,cB⟩ := CopyGlobal.consts n a.1 a.2 j hn0
    have hDn : (0:ℝ)<D n := by unfold D BankCoordinates.k; positivity
    have rate : (slotX n a.1 a.2:ℝ)-d=(W n:ℝ)+(baseRate n a.1 a.2 j:ℝ)*(D n:ℝ) := by
      simp only [baseRate,hd]; push_cast; field_simp; ring
    have g1 : (MarginCert.getRat ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) 1:ℝ)=
        (((j:ℚ)*(1/n:ℚ):ℚ):ℝ) := by simp [MarginCert.getRat]
    have g2 : (MarginCert.getRat ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) (c+2):ℝ)=
        (((a.2:ℚ)*(1/n:ℚ):ℚ):ℝ) := by
      rw [ea]; simp [MarginCert.getRat,List.getElem?_map,List.getElem?_eq_getElem (by rw [size]; exact hc : c<r.2.length)]
    have g0 : (MarginCert.getRat ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) 0:ℝ)=
        ((1/n:ℚ):ℝ) := by simp [MarginCert.getRat]
    have gb : (((profileBanks r.1).getD c 0:Nat):ℝ)=(a.1:ℝ) := by
      rw [ea,List.getD_eq_getElem _ _ hc]
    have tq : tOf eqs val (slotX n a.1 a.2)=val a-1/2 := tOf_slot ne ha
    simp only [WingSpec.base,place,esx,tq,rowτ,← ha_def,shift_pt,g0,g1,g2,gb]
    ext
    · simp only
      rw [← cW,← cD,← cB]
      push_cast at rate ⊢
      linarith
    · simp only
      rw [← cD]; push_cast; ring
  have key := cov size n j hn hj hr sub (rowτ val r) (fun c _ => rowτ_range hv r c) ?rel ?door (shift (-d) z) hz'
  case rel =>
    have hp := phys r member
    rw [← range_map val (0,0),hl] at hp
    simpa only [rowτ,sub_add_cancel] using hp
  case door =>
    intro c hc dd hdd
    obtain ⟨k,ek,eb⟩ := hbase c hc
    rw [eb,← LocalWing.shift_cancel d dd,ArtGallery.Vis.Cert.sees_mapPoly_iff]
    obtain ⟨θ,θ0,θ1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hdd
    refine Set.Subset.trans ?_ hubSub
    rw [he]
    have hW : (W n:ℝ)=((1/n:ℚ):ℝ)/320 := (CopyGlobal.consts n 0 0 j hn0).1
    have hW0 : (0:ℝ)≤W n := by unfold W; positivity
    have hpk : sx eqs k∈PlacedSlots.starts eqs := sx_mem eqs k
    have ex : shift d (Geometry.lerp ((0:ℝ),(1:ℝ)) (((1/n:ℚ):ℝ)/320,1) θ)=((d:ℝ)+θ*(W n:ℝ),1) := by
      rw [shift_pt,← hW]; simp [Geometry.lerp]; ring
    rw [ex]
    simp only [place]
    apply ForwardHub.door_sees hn (RealizedHub.placed ne) hpk (tOf_range hv _) hjK
      ⟨by nlinarith,by nlinarith⟩
    have bk := big ne _ hpk
    have dj : -(2000:ℝ)*n≤d := by
      simp only [hd,door]; push_cast; have : (j:ℝ)≤n := by exact_mod_cast hj
      linarith
    have tr := tOf_range hv (val:=val) (eqs:=eqs) (sx eqs k)
    have hDn : (D n:ℝ)=50050*(n:ℝ)^2 := by unfold D BankCoordinates.k; push_cast; ring
    have n65 : (65:ℝ)≤n := by exact_mod_cast hn
    nlinarith [mul_nonneg θ0 hW0]
  -- transport the seeing guard back
  have hjlt : j<(PrivateRoles.rows eqs).length := (List.mem_zipIdx' path.1).1
  have hri : (PrivateRoles.rows eqs)[j]=r := ((List.mem_zipIdx' path.1).2).symm
  rcases key with ⟨r',hr',sees⟩|⟨c,hc,sees⟩
  · have hrecs : PrivateRoles.records eqs ⟨j,hjlt⟩=idx.2.map (fun l => l.map fun p =>
        ((IndexedWing.grid t ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) false).getD p.1 0,
          (IndexedWing.grid t ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) true).getD p.2 0)) := by
      show GlobalPins.emitted eqs (PrivateRoles.rows eqs)[j] j=_
      rw [hri]
      exact CopyGlobal.emitted_eq ht rec size hn hj hr
    have hk : r'<(PrivateRoles.records eqs ⟨j,hjlt⟩).length := by rw [hrecs]; simpa using hr'
    refine ⟨.inr ⟨⟨j,hjlt⟩,⟨r',hk⟩⟩,?_⟩
    rw [← ArtGallery.Vis.Cert.sees_mapPoly_iff (shift (-d))]
    convert sees using 1
    have hrec : PrivateRoles.record eqs ⟨⟨j,hjlt⟩,⟨r',hk⟩⟩=(idx.2[r']).map fun p =>
        ((IndexedWing.grid t ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) false).getD p.1 0,
          (IndexedWing.grid t ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) true).getD p.2 0) := by
      simp only [PrivateRoles.record,Fin.getElem_fin]
      rw [List.getElem_of_eq hrecs,List.getElem_map]
    have hlen := six _ (List.getElem_mem hr')
    have pt (q : Nat) (hq : q<6) : ratPoint ((PrivateRoles.record eqs ⟨⟨j,hjlt⟩,⟨r',hk⟩⟩).getD q (0,0))=
        gridPt ((IndexedWing.grid t ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) false).map (fun q : ℚ => (q:ℝ)))
          ((IndexedWing.grid t ((1/n:ℚ)::((j:ℚ)*(1/n))::(r.2.map fun (i:Nat) => (i:ℚ)*(1/n))) true).map (fun q : ℚ => (q:ℝ)))
          ((idx.2[r']).getD q (0,0)) := by
      rw [hrec,List.getD_eq_getElem _ _ (by simp [hlen]; omega),List.getElem_map,
        List.getD_eq_getElem (l:=idx.2[r']) _ (by omega)]
      simp only [ratPoint,gridPt,cast_getD]
    simp only [place,Fin.getElem_fin,hri,WingSpec.guardOf]
    rw [List.getD_eq_getElem _ _ hr']
    split
    · next m hm =>
      simp only [hm]
      obtain ⟨-,sa,sb,sy,-⟩ := mvf _ (lookup_mem hm)
      simp only at sy
      simp only [List.getD_eq_getElem _ _ hr'] at sa sb
      rw [LocalWing.shift_cancel,pt 1 (by omega),pt 2 (by omega)]
      simp only [CellRoles.spotA,CellRoles.spotB] at sa sb
      rw [sa,sb]
      simp only [CopyLower.receiver,Geometry.lerp,gridPt,sy]
      ext <;> simp only <;> ring
    · next hm =>
      simp only [hm]
      rw [← shift_rat,LocalWing.shift_cancel,pt 0 (by omega)]
  · obtain ⟨k,ek,eb⟩ := hbase c hc
    refine ⟨.inl (.inl k),?_⟩
    rw [← ArtGallery.Vis.Cert.sees_mapPoly_iff (shift (-d)),← eb]
    exact sees

end Wing

section Main
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {g : Nat}
variable {mvOf : Nat → List (Nat × Nat × Index × Index)}

theorem forward_ne (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,g)) {val : Addr → ℝ}
    (hv : ∀ a, DerivedAlgebra.InRange (val a)) (phys : Physical (compile eqs) val)
    (cat : ∀ tag t, catalog[tag]?=some t → WingSpec.Entry t tag (mvOf tag)) :
    (Polygon.mk (v.map ratPoint)).HasGuardSetOnBoundaryOfCard g := by
  classical
  have shape := GlobalShape.decomposition ne out
  let S : Finset Point := Finset.univ.image (place eqs val mvOf)
  have mem (ρ) : place eqs val mvOf ρ∈(S:Set Point) := Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ ρ))
  have hS : (Polygon.mk (v.map ratPoint)).IsGuardSetOnBoundary (S:Set Point) := by
    constructor
    · intro p hp
      obtain ⟨ρ,-,rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
      rcases ρ with h|x
      · exact hub_on mvOf ne out hv h
      · exact private_on mvOf out hv x
    · intro z hz
      rw [shape.filled] at hz
      rcases hz with hz|⟨e,he,hz⟩
      · obtain ⟨ρ,h⟩ := hub_part mvOf ne hv hz
        exact ⟨_,mem ρ,h.trans (by rw [shape.filled]; exact subset_union_left)⟩
      · obtain ⟨r,j,path⟩ := SourceEntrances.present.mp he
        obtain ⟨ρ,h⟩ := wing_part ne out hv phys cat path hz
        exact ⟨_,mem ρ,h⟩
  have card : S.card≤g := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ,Fintype.card_sum,BudgetCount.card_eq ne out]
  exact GuardPad.pad (GlobalShape.simple out) hS card

/-- **Completeness.** A satisfiable source gives a boundary guard set of exactly `g` guards for
the emitted polygon, given the wing catalogue. -/
theorem forward (out : CandidateWord.vertices eqs=some (v,g)) (sat : ETRINV.Satisfiable eqs)
    (cat : ∀ tag t, catalog[tag]?=some t → WingSpec.Entry t tag (mvOf tag)) :
    (Polygon.mk (v.map ratPoint)).HasGuardSetOnBoundaryOfCard g := by
  by_cases ne : eqs=[]
  · subst eqs
    have accepted := EmptySource.accepted
    rw [CandidateWord.word_of_output EmptySource.emitted] at accepted
    rw [EmptySource.emitted] at out
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj out)
    exact ((CandidateWord.encoded_iff _ _).mp accepted).2.2
  · obtain ⟨val,hv,phys⟩ := (compile_correct eqs).mpr sat
    exact forward_ne ne out hv phys cat

end Main

end ArtGallery.Orthogonal.BoundaryPoint.Forward
end
