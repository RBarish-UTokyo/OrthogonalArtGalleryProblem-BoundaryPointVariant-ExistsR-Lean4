module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyGlobal

/-! # The copy inequality of a channel in the emitted gallery

For a boundary guard set within the budget, the owner `pB` of the copied
variable's base slot and the owner `pR` of the channel's receiver role satisfy the
channel's copy inequality, with the base value read from the floor position of
`pB` (a base off the floor reads `0`) and the receiver value from the position of
`pR` on its spot. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyMain
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport Hardening.Invariance
open CatalogPlan HubOwners HubRoles CopyGlobal ArtGallery.Orthogonal.Hard

theorem six_cases {α : Type} : ∀ {l : List α}, l.length=6 → ∃ c a b u v w, l=[c,a,b,u,v,w]
  | [c,a,b,u,v,w],_ => ⟨c,a,b,u,v,w,rfl⟩

/-- A private role's spot lies in its row's wing. -/
theorem spot_wing {eqs : List ETRINV.Constraint} (ancs : List (List Nat)) (x : PrivateRoles.Role eqs) :
    (PrivateRoles.group eqs ancs).spot x⊆(RealizedDoors.wing (PrivateRoles.entrance eqs x.1)).filled := by
  obtain ⟨c,a,b,u,w,z,hrec⟩ := six_cases (PrivateRoles.record_six eqs x)
  have hm := PrivateRoles.record_mem eqs x
  rw [hrec] at hm
  simp only [PrivateRoles.group,hrec]
  exact OwnerAssembly.spot_in_wing (PrivateRoles.entrance_spec eqs x.1) hm

section Main
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {gN : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,gN))
include ne out

local notation "PP" => Polygon.mk (v.map ratPoint)

/-- The base value of a slot guard: its offset on the floor, `0` off the floor. -/
noncomputable def baseValue (eqs : List ETRINV.Constraint) (x0 : ℚ) (p : Point) : ℝ :=
  open Classical in if p.2=((flo eqs:ℚ):ℝ) then p.1-x0 else 0

theorem copy (ancs : List (List Nat)) (G : Finset Point) (hcov : (PP).IsGuardSetOnBoundary (G:Set Point))
    (hevery : ∀ p∈G, ∃ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ)
    (i : Fin (PrivateRoles.rows eqs).length)
    {t : Template} (ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some t)
    {idx : CorridorProgram.Data Nat} {arity qk bank rank : Nat} {ra rb : RoomGrid.Index} {rr : Nat} {up : Bool}
    (rec : CopySpec.Records t idx arity) (test : CopySpec.Test t idx arity qk bank ra rb rr up)
    (size : ((PrivateRoles.rows eqs)[i]).2.length=arity)
    (hrank : ((PrivateRoles.rows eqs)[i]).2[qk-2]?=some rank) (hqk : 2≤qk)
    (hrr : rr < idx.2.length) (hra : CellRoles.spotA idx.2[rr]=ra) (hrb : CellRoles.spotB idx.2[rr]=rb)
    (hyab : rb.2=ra.2) (hlen : ∀ l∈idx.2, 2<l.length)
    (ha0 : (bank,rank)∈(compile eqs).2)
    (k0 : Fin (HubOwners.slots eqs).length) (hk0 : sx eqs k0=slotX (scale eqs) bank rank)
    {pB : Point} (hpB : pB∈G ∧ (PP).Sees pB ((HubOwners.group eqs PP).mark (.inl k0)) ∧
      pB∈(HubOwners.group eqs PP).spot (.inl k0) ∧ ∀ q∈G, (PP).Sees q ((HubOwners.group eqs PP).mark (.inl k0)) → q=pB)
    (rrF : Fin (PrivateRoles.records eqs i).length) (hrrF : (rrF:Nat)=rr)
    {pR : Point} (hpR : pR∈G ∧ (PP).Sees pR ((PrivateRoles.group eqs ancs).mark ⟨i,rrF⟩) ∧
      pR∈(PrivateRoles.group eqs ancs).spot ⟨i,rrF⟩ ∧
      ∀ q∈G, (PP).Sees q ((PrivateRoles.group eqs ancs).mark ⟨i,rrF⟩) → q=pR) :
    let s : ℚ := 1/(scale eqs)
    let args := s::(((i:Nat):ℚ)*s)::(((PrivateRoles.rows eqs)[i]).2.map fun (k:Nat) => (k:ℚ)*s)
    ∃ tR : ℝ, (0≤tR ∧ tR≤3/2) ∧
      shift (-(door (i:Nat))) pR=CopyLower.receiver ((IndexedWing.grid t args false).map (fun q : ℚ => (q:ℝ)))
        ((IndexedWing.grid t args true).map (fun q : ℚ => (q:ℝ))) ra rb tR ∧
      CopySpec.dir up (baseValue eqs (slotX (scale eqs) bank rank) pB) tR := by
  intro s0 args0
  -- the row, its wing and its frame
  set n := scale eqs with hn_def
  have hn : 65≤n := (scale_bounds ne).1
  have hn0 : 0<n := by omega
  have path := PrivateRoles.entrance_spec eqs i
  set e := PrivateRoles.entrance eqs i
  set d : ℚ := door (i:Nat)
  have rmem : (PrivateRoles.rows eqs)[i]∈(compile eqs).1 := List.getElem_mem _
  have hiN : (i:Nat)≤n := (CompiledAddresses.program_door eqs path.1).le
  have hrk : ∀ k∈((PrivateRoles.rows eqs)[i]).2,k≤n := fun k hk => (CompiledAddresses.program_ranks eqs rmem hk).le
  obtain ⟨fill,closed,contact,Lw⟩ := frame2 path out ht
  obtain ⟨cW,cD,cb⟩ := consts n bank rank i hn0
  set x0 : ℚ := slotX n bank rank
  let J := GalleryBoundary.joined path out
  -- the grid of the wing
  let s : ℚ := 1/n
  let args := s::(((i:Nat):ℚ)*s)::(((PrivateRoles.rows eqs)[i]).2.map fun (k:Nat) => (k:ℚ)*s)
  let gx := IndexedWing.grid t args false
  let gy := IndexedWing.grid t args true
  let X := gx.map (fun q : ℚ => (q:ℝ))
  let Y := gy.map (fun q : ℚ => (q:ℝ))
  have em := emitted_eq (i:=(i:Nat)) ht rec size hn hiN hrk
  -- the spot of a role of the row, in the frame
  have spotRow (k : Fin (PrivateRoles.records eqs i).length) :
      ∃ hk : (k:Nat) < idx.2.length, shift (-d) '' (PrivateRoles.group eqs ancs).spot ⟨i,k⟩=
        ArtGallery.segment (gridPt X Y (CellRoles.spotA idx.2[(k:Nat)])) (gridPt X Y (CellRoles.spotB idx.2[(k:Nat)])) := by
    have hk : (k:Nat) < idx.2.length := by
      have := k.isLt; simp only [PrivateRoles.records,em,List.length_map] at this; exact this
    refine ⟨hk,?_⟩
    have recq : PrivateRoles.record eqs ⟨i,k⟩=idx.2[(k:Nat)].map (fun p => (gx.getD p.1 0,gy.getD p.2 0)) := by
      simp only [PrivateRoles.record,PrivateRoles.records,em]
      exact List.getElem_map ..
    simp only [PrivateRoles.group,recq]
    exact spot_local rfl rfl d _ (hlen _ (List.getElem_mem hk))
  -- the receiver: its parameter on the spot
  obtain ⟨hkR,spR⟩ := spotRow rrF
  have pRspot : shift (-d) pR∈ArtGallery.segment (gridPt X Y ra) (gridPt X Y rb) := by
    have := Set.mem_image_of_mem (shift (-d)) hpR.2.2.1
    rw [spR] at this
    simpa [hrrF,hra,hrb] using this
  obtain ⟨lam,l0,l1,hlam⟩ := pRspot
  have hrecv : shift (-d) pR=CopyLower.receiver X Y ra rb (3/2*lam) := by
    rw [hlam]; unfold CopyLower.receiver; simp only [gridPt,hyab]; ext <;> simp <;> ring
  refine ⟨3/2*lam,⟨by linarith,by linarith⟩,hrecv,?_⟩
  -- the receiver lies in the wing
  have pRwing : pR∈(RealizedDoors.wing e).filled := spot_wing ancs ⟨i,rrF⟩ hpR.2.2.1
  -- the arguments of the program
  have hQ : (MarginCert.getRat args qk:ℝ)=(((rank:ℚ)*(1/n:ℚ):ℚ):ℝ) := by
    obtain ⟨m,rfl⟩ : ∃ m, qk=m+2 := ⟨qk-2,by omega⟩
    simp only [args,MarginCert.getRat,List.getElem?_cons_succ,List.getElem?_map]
    simp only [Nat.add_sub_cancel] at hrank
    rw [hrank]; simp [s]
  have hJ : (MarginCert.getRat args 1:ℝ)=((((i:Nat):ℚ)*(1/n:ℚ):ℚ):ℝ) := by
    simp [args,MarginCert.getRat,s]
  -- the base slot
  have spB := hpB.2.2.1
  simp only [HubOwners.group,HubOwners.lo,HubOwners.hi] at spB
  obtain ⟨pBb,pB0,pB1⟩ := spB
  rw [hk0] at pB0 pB1
  have hx0 : x0∈PlacedSlots.starts eqs := List.mem_map.mpr ⟨(bank,rank),ha0,rfl⟩
  have col := HubSpots.column ne out pBb hx0 pB0 pB1
  have htB : 0≤baseValue eqs x0 pB ∧ baseValue eqs x0 pB≤3/2 := by
    unfold baseValue; split
    · push_cast at pB1; constructor <;> linarith
    · norm_num
  refine test size n i hn hiN hrk (P:=mapPoly (shift (-d)) PP) (rest:=shift (-d) '' J.rest) fill closed
    (by rw [contact,cW]) (cover_shift hcov d) (tB:=baseValue eqs x0 pB) (tR:=3/2*lam) (Bg:=shift (-d) pB) htB ⟨by linarith,by linarith⟩ ?_ ?_ ?_
  · -- the base: on the floor in the hub, or blind to the wing
    by_cases hfl : pB.2=((flo eqs:ℚ):ℝ)
    · left
      have own : (d:ℝ)+(W n:ℝ)+(baseRate n bank rank (i:Nat):ℝ)*(D n:ℝ)=(x0:ℝ) := by
        have : (D n:ℝ)≠0 := by have := GlobalBlind.D_ge n (by omega); linarith
        simp only [d,x0]; unfold baseRate; push_cast; field_simp; ring
      have hf' : ((flo eqs:ℚ):ℝ)=1-(D n:ℝ) := by unfold flo; push_cast; rfl
      refine ⟨?_,⟨pB,GlobalBlind.low_rest ne out path (Jordan.boundary_subset_filled _ pBb)
        (by rw [hfl]; have := flo_lt ne; linarith),rfl⟩⟩
      rw [shift_pt]
      have hQ' := hQ; have hJ' := hJ
      simp only [args,s] at hQ' hJ'
      simp only [hQ',hJ']
      rw [←cW,←cD,←cb]
      unfold baseValue; rw [if_pos hfl]
      ext
      · simp only; push_cast; linarith
      · simp only; rw [hfl,hf']
    · right
      intro z hz sees
      rw [Lw] at hz
      obtain ⟨z0,hz0,rfl⟩ := hz
      rw [ArtGallery.Vis.Cert.sees_mapPoly_iff] at sees
      exact HubSpots.high_blind ne out hx0 pB0 (col.resolve_left hfl) (GlobalBlind.in_wings ne out path hz0) sees
  · -- the receiver lies in the wing
    rw [←hrecv,Lw]; exact Set.mem_image_of_mem _ pRwing
  · -- every other guard: another role of the row, or blind
    intro g' hg' e1 e2
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hg'
    have gB : g∈(PP).boundary := hcov.1 hg
    have ne1 : g≠pB := fun h => e1 (by rw [h])
    have ne2 : g≠pR := fun h => e2 (by rw [h,hrecv])
    have hQ' := hQ; have hJ' := hJ
    simp only [args,s] at hQ' hJ'
    have toBlind (h : ∀ τ c y : ℝ, 0≤τ → τ≤3/2 → 0≤c → c≤(W n:ℝ) → 7/3≤y →
        GlobalBlind.target n i bank rank τ c y∈(RealizedDoors.wing e).filled →
        ¬(PP).Sees g (GlobalBlind.target n i bank rank τ c y)) :=
      blind_shift (d:=d) (W:=(W n:ℝ)) (b:=(baseRate n bank rank (i:Nat):ℝ)) (D:=(D n:ℝ))
        (Wg:=RealizedDoors.wing e) (P:=PP) (g:=g) (fun τ c y τ0 τ1 c0 c1 hy hz => h τ c y τ0 τ1 c0 c1 hy hz)
    rw [←Lw,cW,cD,cb] at toBlind
    obtain ⟨ρ,hsees,hspot⟩ := hevery g hg
    rcases ρ with (k|m)|x
    · -- another base slot
      simp only [Sum.elim_inl,HubOwners.group,HubOwners.lo,HubOwners.hi] at hspot hsees
      obtain ⟨-,h0,h1⟩ := hspot
      by_cases hk : sx eqs k=x0
      · exfalso
        have nd : (HubOwners.slots eqs).Nodup := (RealizedHub.placed ne).sorted.imp (fun h e => by subst e; linarith)
        have : k=k0 := Fin.ext ((List.Nodup.getElem_inj_iff nd).mp (hk.trans hk0.symm))
        subst this
        exact ne1 (hpB.2.2.2 g hg hsees)
      · right
        simp only [hQ',hJ']
        exact toBlind (fun τ c y τ0 τ1 c0 c1 hy hz =>
          GlobalBlind.slot_blind ne out path ha0 (sx_mem eqs k) hk gB h0 h1 τ0 τ1 c0 (by rw [cW]; exact c1) hy hz)
    · -- a door step
      simp only [Sum.elim_inl,HubOwners.group,HubOwners.lo,HubOwners.hi] at hspot
      try simp only [Sum.elim_inl] at hsees
      obtain ⟨-,h0,h1⟩ := hspot
      have hub : g∈(RealizedDoors.hub eqs).filled := by
        rcases split_filled ne out (Jordan.boundary_subset_filled _ gB) with h|h
        · exact h
        · exfalso
          apply HubOwners.wing_free ne out (i:=.inr m) (t:=tipL eqs (.inr m)) (Or.inl rfl) h
          have : (PP).Sees g (tipL eqs (.inr m)) := by simpa [JoinedBudget.Group.mark,HubOwners.group] using hsees
          exact Vis.sees_comm.mp this
      right
      simp only [hQ',hJ']
      exact toBlind (fun τ c y τ0 τ1 c0 c1 hy hz =>
        GlobalBlind.step_blind ne out path (CompiledAddresses.program_door eqs path.1) ha0 m.isLt gB hub h0 h1
          τ0 τ1 c0 (by rw [cW]; exact c1) hy hz)
    · -- a private role
      by_cases hx : x.1=i
      · obtain ⟨xi,xk⟩ := x
        simp only at hx
        subst hx
        obtain ⟨hk,spk⟩ := spotRow xk
        left
        refine ⟨xk,hk,?_,?_,?_⟩
        · intro e3
          have : xk=rrF := Fin.ext (e3.trans hrrF.symm)
          subst this
          exact ne2 (hpR.2.2.2 g hg hsees)
        · rw [←spk]; exact Set.mem_image_of_mem _ hspot
        · rw [Lw]; exact Set.mem_image_of_mem _ (spot_wing ancs ⟨xi,xk⟩ hspot)
      · right
        have hii : ((x.1:Nat))≠(i:Nat) := fun h => hx (Fin.ext h)
        simp only [hQ',hJ']
        exact toBlind (fun τ c y τ0 τ1 c0 c1 hy hz =>
          GlobalBlind.private_blind ne out path (PrivateRoles.entrance_spec eqs x.1) hii
            (spot_wing ancs x hspot) hy hz)

end Main

end ArtGallery.Orthogonal.BoundaryPoint.CopyMain
end
