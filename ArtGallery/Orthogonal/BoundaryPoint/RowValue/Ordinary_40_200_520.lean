module

public import ArtGallery.Orthogonal.BoundaryPoint.ValueChain
public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.Ordinary_40_200_520

/-! The relation of a `Ordinary_40_200_520` row between the values of its slots (generated): the copy channels
and the room relation of the row. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RowValue.Ordinary_40_200_520
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport
open CatalogPlan CatalogRanks HubOwners ValueChain WingOrder.Ordinary_40_200_520

section Main
variable {eqs : List ETRINV.Constraint} {v : List Vertex} {gN : Nat}
variable (ne : eqs≠[]) (out : CandidateWord.vertices eqs=some (v,gN))
include ne out

local notation "PP" => Polygon.mk (v.map ratPoint)

theorem row (ancs : List (List Nat)) (G : Finset Point) (hcov : (PP).IsGuardSetOnBoundary (G:Set Point))
    (hall : ∀ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs, ∃ p∈G,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ ∧
      ∀ q∈G, (PP).Sees q (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) → q=p)
    (hevery : ∀ p∈G, ∃ ρ : HubRole eqs ⊕ PrivateRoles.Role eqs,
      (PP).Sees p (Sum.elim (HubOwners.group eqs PP).mark (PrivateRoles.group eqs ancs).mark ρ) ∧
      p∈Sum.elim (HubOwners.group eqs PP).spot (PrivateRoles.group eqs ancs).spot ρ)
    (i : Fin (PrivateRoles.rows eqs).length) (htag : ((PrivateRoles.rows eqs)[i]).1=0) :
    CatalogLogic.relation 0 (((profileBanks 0).zip ((PrivateRoles.rows eqs)[i]).2).map
      (value (fun k => Classical.choose (hall (.inl (.inl k)))))) := by
  set n := scale eqs
  have hn : 65≤n := (scale_bounds ne).1
  have path := PrivateRoles.entrance_spec eqs i
  have rmem : (PrivateRoles.rows eqs)[i]∈(compile eqs).1 := List.getElem_mem _
  have hiN : (i:Nat)≤n := (CompiledAddresses.program_door eqs path.1).le
  have hrk : ∀ k∈((PrivateRoles.rows eqs)[i]).2,k≤n := fun k hk => (CompiledAddresses.program_ranks eqs rmem hk).le
  have ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some template := by rw [htag]; exact RoomCheck.Ordinary_40_200_520.tag_eq
  have size : ((PrivateRoles.rows eqs)[i]).2.length=3 := by rw [row_arity eqs rmem,htag]; rfl
  have hlen : (PrivateRoles.records eqs i).length=19 := by rw [RoomGlobal.records_length i ht]; rfl
  have hb : (profileBanks ((PrivateRoles.rows eqs)[i]).1)=[40,200,520] := by rw [htag]; rfl
  have hrec : CopySpec.Records template WingRecords.Ordinary_40_200_520.index 3 := CopyLocal.Ordinary_40_200_520.records
  have hspot (k : Fin (slots eqs).length) : ((sx eqs k:ℚ):ℝ)≤(Classical.choose (hall (.inl (.inl k)))).1 ∧
      (Classical.choose (hall (.inl (.inl k)))).1≤((sx eqs k:ℚ):ℝ)+3/2 := by
    have sp := (Classical.choose_spec (hall (.inl (.inl k)))).2.2.1
    generalize Classical.choose (hall (.inl (.inl k)))=p at sp ⊢
    simp only [Sum.elim_inl,HubOwners.group,HubOwners.lo,HubOwners.hi] at sp
    obtain ⟨-,a,b⟩ := sp; exact ⟨a,by push_cast at b ⊢; linarith⟩
  have vr := value_range (fun k => Classical.choose (hall (.inl (.inl k)))) hspot
  obtain ⟨t2,h2,e2,d2⟩ := channel ne out ancs G hcov hall hevery i ht hrec CopyLocal.Ordinary_40_200_520.lower2 size
    (by norm_num) (by rw [size]; norm_num) (by rw [hb]; rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hlen]; norm_num)
  obtain ⟨t0,h0,e0,d0⟩ := channel ne out ancs G hcov hall hevery i ht hrec CopyLocal.Ordinary_40_200_520.upper0 size
    (by norm_num) (by rw [size]; norm_num) (by rw [hb]; rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hlen]; norm_num)
  obtain ⟨t1,h1,e1,d1⟩ := channel ne out ancs G hcov hall hevery i ht hrec CopyLocal.Ordinary_40_200_520.upper1 size
    (by norm_num) (by rw [size]; norm_num) (by rw [hb]; rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hlen]; norm_num)
  obtain ⟨tq,tr,tx,tz,hq,hr,hx,hz,own,rel⟩ := RoomRow.Ordinary.relation ne out ancs G hcov hall hevery i ht
    RoomCheck.Ordinary_40_200_520.room_eq (size ▸ RoomCheck.Ordinary_40_200_520.program_ok)
    (RoomSplit.Ordinary_40_200_520.split size n i hn hiN hrk)
    RoomCheck.Ordinary_40_200_520.clear1 RoomCheck.Ordinary_40_200_520.clear2
    (by rw [RoomGlobal.records_length i ht]; rfl)
  have own0 := own ⟨15,by rw [hlen]; norm_num⟩ 3 _ rfl (Or.inl ⟨rfl,rfl⟩) _
    (Classical.choose_spec (hall (.inr ⟨i,⟨15,by rw [hlen]; norm_num⟩⟩))).1
    (by simpa using (Classical.choose_spec (hall (.inr ⟨i,⟨15,by rw [hlen]; norm_num⟩⟩))).2.1)
  have q0 := link (t:=template) hrec size hn hiN hrk (m:=3) (by decide) (by decide) (by decide)
    (ra:=(63,6)) (rb:=(64,6)) (by decide) (by decide) (by
      show (RoomFamily.Ordinary.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.Ordinary.roles.getD 3 []).getD 1 (0,0)).1 0≠
        (RoomFamily.Ordinary.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.Ordinary.roles.getD 3 []).getD 2 (0,0)).1 0
      apply ne_of_lt
      apply SepGeom.level_lt (RoomCoordinates.Axis.for_size RoomFamily.Ordinary.x_ok hn) _ (by decide)
      rw [RoomCoordinates.length_coords]; decide) (e0.symm.trans own0)
  have own1 := own ⟨17,by rw [hlen]; norm_num⟩ 5 _ rfl (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))) _
    (Classical.choose_spec (hall (.inr ⟨i,⟨17,by rw [hlen]; norm_num⟩⟩))).1
    (by simpa using (Classical.choose_spec (hall (.inr ⟨i,⟨17,by rw [hlen]; norm_num⟩⟩))).2.1)
  have q1 := link (t:=template) hrec size hn hiN hrk (m:=5) (by decide) (by decide) (by decide)
    (ra:=(67,4)) (rb:=(68,4)) (by decide) (by decide) (by
      show (RoomFamily.Ordinary.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.Ordinary.roles.getD 5 []).getD 1 (0,0)).1 0≠
        (RoomFamily.Ordinary.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.Ordinary.roles.getD 5 []).getD 2 (0,0)).1 0
      apply ne_of_lt
      apply SepGeom.level_lt (RoomCoordinates.Axis.for_size RoomFamily.Ordinary.x_ok hn) _ (by decide)
      rw [RoomCoordinates.length_coords]; decide) (e1.symm.trans own1)
  have own2 := own ⟨18,by rw [hlen]; norm_num⟩ 6 _ rfl (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))) _
    (Classical.choose_spec (hall (.inr ⟨i,⟨18,by rw [hlen]; norm_num⟩⟩))).1
    (by simpa using (Classical.choose_spec (hall (.inr ⟨i,⟨18,by rw [hlen]; norm_num⟩⟩))).2.1)
  have q2 := link (t:=template) hrec size hn hiN hrk (m:=6) (by decide) (by decide) (by decide)
    (ra:=(71,2)) (rb:=(72,2)) (by decide) (by decide) (by
      show (RoomFamily.Ordinary.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.Ordinary.roles.getD 6 []).getD 1 (0,0)).1 0≠
        (RoomFamily.Ordinary.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.Ordinary.roles.getD 6 []).getD 2 (0,0)).1 0
      apply ne_of_lt
      apply SepGeom.level_lt (RoomCoordinates.Axis.for_size RoomFamily.Ordinary.x_ok hn) _ (by decide)
      rw [RoomCoordinates.length_coords]; decide) (e2.symm.trans own2)
  obtain ⟨a,b,c,hrs⟩ : ∃ a b c, ((PrivateRoles.rows eqs)[i]).2=[a,b,c] := by
    match h : ((PrivateRoles.rows eqs)[i]).2, size with
    | [a,b,c], _ => exact ⟨a,b,c,rfl⟩
  simp only [hrs,CopySpec.dir,List.getElem_cons_zero,List.getElem_cons_succ,
    show (3:Nat)-2=1 from rfl,show (4:Nat)-2=2 from rfl,show (2:Nat)-2=0 from rfl] at d0 d1 d2
  simp only [CatalogLogic.relation,hrs,profileBanks,List.zip_cons_cons,List.zip_nil_right,List.map_cons,
    List.map_nil,List.getD_cons_zero,List.getD_cons_succ,DerivedAlgebra.InvLe,DerivedAlgebra.InvRevGe,
    DerivedAlgebra.ShiftedAddGe,ite_true,ite_false,Nat.succ_ne_zero,OfNat.ofNat_ne_zero,
    show (0:Nat)=0 ↔ 0=0 from Iff.rfl]
  generalize hW : value (fun k => Classical.choose (hall (.inl (.inl k))))=W at d0 d1 d2 vr ⊢
  norm_num
  linarith

end Main

end ArtGallery.Orthogonal.BoundaryPoint.RowValue.Ordinary_40_200_520
end
