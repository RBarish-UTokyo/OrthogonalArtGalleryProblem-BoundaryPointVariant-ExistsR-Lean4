module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomGlobal

/-! # From owned guards to values

Each address of the compiled source is a base slot of the hub; its value is the floor offset of
the guard owning the slot, plus `1/2`. The receivers of a row's copy channels are room roles;
their copy parameter and their room parameter coincide, since both describe the same guard on the
same role segment (the wing grid and the room grid agree on room role nodes). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ValueChain
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport Hardening.Invariance
open CatalogPlan CatalogLogic CatalogRanks HubOwners HubRoles CopyGlobal ArtGallery.Orthogonal.Hard RoomGlobal CorridorProgram

/-- Every address used by a compiled row is an address of the source. -/
theorem zip_mem (eqs : List ETRINV.Constraint) {r : CatalogPlan.Row} (hr : r∈(compile eqs).1) :
    ∀ a∈(profileBanks r.1).zip r.2, a∈(compile eqs).2 := by
  change r∈(expanded eqs).map (fun q => (q.1,q.2.map (CatalogPlan.rank (keysOf eqs)))) at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  simp only
  rw [expanded_banks eqs q hq]
  intro a ha
  have e : (q.2.map (fun k => k.headD 0)).zip (q.2.map (CatalogPlan.rank (keysOf eqs)))=q.2.map (loc (keysOf eqs)) := by
    induction q.2 with
    | nil => rfl
    | cons k ks ih => simp only [List.map_cons,List.zip_cons_cons,ih]; rfl
  rw [e] at ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  apply address_used eqs k
  exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨q,hq,hk⟩)

/-- A compiled row has one rank per bank of its profile. -/
theorem row_arity (eqs : List ETRINV.Constraint) {r : CatalogPlan.Row} (hr : r∈(compile eqs).1) :
    r.2.length=(profileBanks r.1).length := by
  change r∈(expanded eqs).map (fun q => (q.1,q.2.map (CatalogPlan.rank (keysOf eqs)))) at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  simp only [List.length_map,expanded_banks eqs q hq]

/-- The slot of an address is a base slot of the hub. -/
theorem slot_index (eqs : List ETRINV.Constraint) {a : Addr} (ha : a∈(compile eqs).2) :
    ∃ k : Fin (slots eqs).length, sx eqs k=slotX (scale eqs) a.1 a.2 := by
  have : slotX (scale eqs) a.1 a.2∈slots eqs := List.mem_map.mpr ⟨a,ha,rfl⟩
  obtain ⟨k,hk,e⟩ := List.getElem_of_mem this
  exact ⟨⟨k,hk⟩,e⟩

section Values
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {gN : Nat}

/-- The value of an address: the floor offset of the owner of its slot, plus `1/2`. -/
noncomputable def value (ownerB : Fin (slots eqs).length → Point) (a : Addr) : ℝ :=
  open Classical in
  if h : ∃ k : Fin (slots eqs).length, sx eqs k=slotX (scale eqs) a.1 a.2 then
    CopyMain.baseValue eqs (slotX (scale eqs) a.1 a.2) (ownerB (Classical.choose h))+1/2
  else 1

theorem value_eq (ne : eqs≠[]) (ownerB : Fin (slots eqs).length → Point) {a : Addr} (k : Fin (slots eqs).length)
    (hk : sx eqs k=slotX (scale eqs) a.1 a.2) :
    value ownerB a=CopyMain.baseValue eqs (slotX (scale eqs) a.1 a.2) (ownerB k)+1/2 := by
  have h : ∃ k : Fin (slots eqs).length, sx eqs k=slotX (scale eqs) a.1 a.2 := ⟨k,hk⟩
  have nd : (slots eqs).Nodup := (RealizedHub.placed ne).sorted.imp (fun h e => by subst e; linarith)
  have e : Classical.choose h=k := by
    have c := Classical.choose_spec h
    exact Fin.ext ((List.Nodup.getElem_inj_iff nd).mp (c.trans hk.symm))
  simp only [value,dif_pos h,e]

theorem value_range (ownerB : Fin (slots eqs).length → Point)
    (hspot : ∀ k, ((sx eqs k:ℚ):ℝ)≤(ownerB k).1 ∧ (ownerB k).1≤((sx eqs k:ℚ):ℝ)+3/2) (a : Addr) :
    1/2≤value ownerB a ∧ value ownerB a≤2 := by
  unfold value
  split
  · next h =>
    have c := Classical.choose_spec h
    have sp := hspot (Classical.choose h)
    rw [c] at sp
    unfold CopyMain.baseValue
    split <;> constructor <;> push_cast at sp ⊢ <;> linarith [sp.1,sp.2]
  · norm_num

end Values

section Channel
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {gN : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,gN))
include ne out

local notation "PP" => Polygon.mk (v.map ratPoint)

/-- One copy channel of a row, read through the owners of the hub slots and the private roles. -/
theorem channel (ancs : List (List Nat)) (G : Finset Point) (hcov : (PP).IsGuardSetOnBoundary (G:Set Point))
    (hall : ∀ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs, ∃ p∈G,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ ∧
      ∀ q∈G, (PP).Sees q (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) → q=p)
    (hevery : ∀ p∈G, ∃ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ)
    (i : Fin (PrivateRoles.rows eqs).length)
    {t : Template} (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t)
    {idx : CorridorProgram.Data Nat} {arity qk bank : Nat} {ra rb : RoomGrid.Index} {rr : Nat} {up : Bool}
    (rec : CopySpec.Records t idx arity) (test : CopySpec.Test t idx arity qk bank ra rb rr up)
    (size : ((PrivateRoles.rows eqs)[i]).2.length=arity) (hqk : 2≤qk)
    (harg : qk-2<((PrivateRoles.rows eqs)[i]).2.length)
    (hbank : (profileBanks ((PrivateRoles.rows eqs)[i]).1)[qk-2]?=some bank)
    (hrr : rr < idx.2.length) (hra : CellRoles.spotA idx.2[rr]=ra) (hrb : CellRoles.spotB idx.2[rr]=rb)
    (hyab : rb.2=ra.2) (hlen : ∀ l∈idx.2, 2<l.length) (hrrF : rr<(PrivateRoles.records eqs i).length) :
    let s : ℚ := 1/(scale eqs)
    let args := s::(((i:Nat):ℚ)*s)::(((PrivateRoles.rows eqs)[i]).2.map fun (k:Nat) => (k:ℚ)*s)
    let ownerB := fun (k : Fin (slots eqs).length) => Classical.choose (hall (.inl (.inl k)))
    let pR := Classical.choose (hall (.inr ⟨i,⟨rr,hrrF⟩⟩))
    ∃ tR : ℝ, (0≤tR ∧ tR≤3/2) ∧
      shift (-(door (i:Nat))) pR=CopyLower.receiver ((IndexedWing.grid t args false).map (fun q : ℚ => (q:ℝ)))
        ((IndexedWing.grid t args true).map (fun q : ℚ => (q:ℝ))) ra rb tR ∧
      CopySpec.dir up (value ownerB (bank,((PrivateRoles.rows eqs)[i]).2[qk-2])-1/2) tR := by
  intro s args ownerB pR
  set rank := ((PrivateRoles.rows eqs)[i]).2[qk-2]
  have hrank : ((PrivateRoles.rows eqs)[i]).2[qk-2]?=some rank := List.getElem?_eq_getElem harg
  have hz : ((profileBanks ((PrivateRoles.rows eqs)[i]).1).zip ((PrivateRoles.rows eqs)[i]).2)[qk-2]?=some (bank,rank) :=
    List.getElem?_zip_eq_some.mpr ⟨hbank,hrank⟩
  have ha0 : (bank,rank)∈(compile eqs).2 := zip_mem eqs (List.getElem_mem _) _ (List.mem_of_getElem? hz)
  obtain ⟨k0,hk0⟩ := slot_index eqs ha0
  have sB := Classical.choose_spec (hall (.inl (.inl k0)))
  have sR := Classical.choose_spec (hall (.inr ⟨i,⟨rr,hrrF⟩⟩))
  simp only [Sum.elim_inl,Sum.elim_inr] at sB sR
  obtain ⟨tR,hR,eR,dR⟩ := CopyMain.copy ne out ancs G hcov hevery i ht rec test size hrank hqk hrr hra hrb hyab hlen
    ha0 k0 hk0 (pB:=ownerB k0) sB ⟨rr,hrrF⟩ rfl (pR:=pR) sR
  refine ⟨tR,hR,eR,?_⟩
  rw [value_eq ne ownerB k0 hk0]
  simpa using dR

end Channel

/-- Wing grid and room grid agree on the nodes of room roles. -/
theorem room_node {t : Template} {idx : Data Nat} {arity : Nat} (rec : CopySpec.Records t idx arity)
    {rs : List Nat} (size : rs.length=arity) {n j : Nat} (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n)
    {m : Nat} (hm : m<t.room.roles.length) {q : Nat} (hq : q<(t.room.roles[m]).length) :
    let s : ℚ := 1/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    ∃ h : t.corridor.roles.length+m < idx.2.length,
      ((IndexedWing.grid t args false).getD ((idx.2[t.corridor.roles.length+m]).getD q (0,0)).1 0,
        (IndexedWing.grid t args true).getD ((idx.2[t.corridor.roles.length+m]).getD q (0,0)).2 0)=
      ((t.room.x.coordsQ s).getD ((t.room.roles[m]).getD q (0,0)).1 0,
        (t.room.y.coordsQ s).getD ((t.room.roles[m]).getD q (0,0)).2 0) := by
  intro s args
  have e := rec size n j hn hj hr
  simp only [GlobalPins.records] at e
  change (t.corridor.coords args).2++(t.room.coords s).2=_ at e
  have hc : (t.corridor.coords args).2.length=t.corridor.roles.length := by simp [Layout.coords]
  have hlen := congrArg List.length e
  simp only [List.length_append,List.length_map,hc,PlanGeometry.ArithmeticRoom.coords] at hlen
  have hi : t.corridor.roles.length+m < idx.2.length := by omega
  refine ⟨hi,?_⟩
  have g := List.getElem_of_eq e (i:=t.corridor.roles.length+m) (by simp [hc,PlanGeometry.ArithmeticRoom.coords]; omega)
  rw [List.getElem_append_right (by omega)] at g
  simp only [List.getElem_map,PlanGeometry.ArithmeticRoom.coords,hc,Nat.add_sub_cancel_left] at g
  have hq' : q<(idx.2[t.corridor.roles.length+m]).length := by
    have := congrArg List.length g; simp only [List.length_map] at this; omega
  have g' := congrArg (fun l => l[q]?) g
  simp only [List.getElem?_map] at g'
  rw [List.getElem?_eq_getElem hq,List.getElem?_eq_getElem hq'] at g'
  simp only [Option.map_some,Option.some.injEq] at g'
  rw [List.getD_eq_getElem _ _ hq,List.getD_eq_getElem _ _ hq']
  exact g'.symm

/-- A guard on a room role segment has one parameter: the copy receiver parameter and the room
guard parameter agree. -/
theorem param_eq {A B : Point} {u v : ℝ} (hAB : A.1≠B.1)
    (h : ((A.1+2/3*(B.1-A.1)*u,A.2):Point)=Geometry.lerp A B (v*(2/3))) : u=v := by
  have h1 := congrArg Prod.fst h
  simp only [Geometry.lerp] at h1
  have : (B.1-A.1)*(u-v)=0 := by linarith
  rcases mul_eq_zero.mp this with h0|h0
  · exact absurd (by linarith) hAB
  · linarith

/-- The copy parameter of a room-role receiver equals its room guard parameter. -/
theorem link {t : Template} {idx : Data Nat} {arity : Nat} (rec : CopySpec.Records t idx arity)
    {rs : List Nat} (size : rs.length=arity) {n j : Nat} (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n)
    {m : Nat} (hm : m<t.room.roles.length) (h6 : 2<(t.room.roles[m]).length)
    (hi : t.corridor.roles.length+m < idx.2.length) {ra rb : RoomGrid.Index}
    (hra : CellRoles.spotA (idx.2[t.corridor.roles.length+m])=ra)
    (hrb : CellRoles.spotB (idx.2[t.corridor.roles.length+m])=rb)
    (hx : (t.room.x.coordsR (1/(n:ℝ))).getD ((t.room.roles[m]).getD 1 (0,0)).1 0≠
      (t.room.x.coordsR (1/(n:ℝ))).getD ((t.room.roles[m]).getD 2 (0,0)).1 0)
    {tR τ : ℝ} :
    let s : ℚ := 1/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    CopyLower.receiver ((IndexedWing.grid t args false).map (fun q : ℚ => (q:ℝ)))
      ((IndexedWing.grid t args true).map (fun q : ℚ => (q:ℝ))) ra rb tR=
      SlotLines.slot (gridPt (t.room.x.coordsR (1/(n:ℝ))) (t.room.y.coordsR (1/(n:ℝ)))) t.room.roles m τ → tR=τ := by
  intro s args h
  have r1 := room_node rec size hn hj hr hm (q:=1) (by omega)
  have r2 := room_node rec size hn hj hr hm (q:=2) h6
  obtain ⟨i1,e1⟩ := r1
  obtain ⟨i2,e2⟩ := r2
  have cast (xs : List ℚ) (a : Nat) : (xs.map (fun q : ℚ => (q:ℝ))).getD a 0=((xs.getD a 0:ℚ):ℝ) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases xs[a]? <;> simp
  have hs : ((s:ℚ):ℝ)=1/(n:ℝ) := by simp [s]
  have cx : t.room.x.coordsR (1/(n:ℝ))=(t.room.x.coordsQ s).map (fun q : ℚ => (q:ℝ)) := by
    rw [←hs,RoomCoordinates.cast_coords]
  have cy : t.room.y.coordsR (1/(n:ℝ))=(t.room.y.coordsQ s).map (fun q : ℚ => (q:ℝ)) := by
    rw [←hs,RoomCoordinates.cast_coords]
  subst hra hrb
  have A : gridPt ((IndexedWing.grid t args false).map (fun q : ℚ => (q:ℝ)))
      ((IndexedWing.grid t args true).map (fun q : ℚ => (q:ℝ))) (CellRoles.spotA idx.2[t.corridor.roles.length+m])=
      gridPt (t.room.x.coordsR (1/(n:ℝ))) (t.room.y.coordsR (1/(n:ℝ))) ((t.room.roles[m]).getD 1 (0,0)) := by
    simp only [gridPt,CellRoles.spotA,cast,cx,cy]
    have ex := congrArg Prod.fst e1
    have ey := congrArg Prod.snd e1
    simp only at ex ey
    ext
    · exact congrArg (fun q : ℚ => (q:ℝ)) ex
    · exact congrArg (fun q : ℚ => (q:ℝ)) ey
  have B : gridPt ((IndexedWing.grid t args false).map (fun q : ℚ => (q:ℝ)))
      ((IndexedWing.grid t args true).map (fun q : ℚ => (q:ℝ))) (CellRoles.spotB idx.2[t.corridor.roles.length+m])=
      gridPt (t.room.x.coordsR (1/(n:ℝ))) (t.room.y.coordsR (1/(n:ℝ))) ((t.room.roles[m]).getD 2 (0,0)) := by
    simp only [gridPt,CellRoles.spotB,cast,cx,cy]
    have ex := congrArg Prod.fst e2
    have ey := congrArg Prod.snd e2
    simp only at ex ey
    ext
    · exact congrArg (fun q : ℚ => (q:ℝ)) ex
    · exact congrArg (fun q : ℚ => (q:ℝ)) ey
  unfold CopyLower.receiver at h
  rw [A,B] at h
  simp only [SlotLines.slot,List.getD_eq_getElem _ _ hm] at h
  exact param_eq (by simpa [gridPt] using hx) h

end ArtGallery.Orthogonal.BoundaryPoint.ValueChain
end
