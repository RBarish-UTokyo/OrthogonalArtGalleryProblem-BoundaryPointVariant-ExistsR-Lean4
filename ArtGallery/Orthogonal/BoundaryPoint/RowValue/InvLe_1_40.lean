module

public import ArtGallery.Orthogonal.BoundaryPoint.ValueChain
public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.InvLe_1_40

/-! The relation of a `InvLe_1_40` row between the values of its slots (generated): the copy channels
and the room relation of the row. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvLe_1_40
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport
open CatalogPlan CatalogRanks HubOwners ValueChain WingOrder.InvLe_1_40

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
    (i : Fin (PrivateRoles.rows eqs).length) (htag : ((PrivateRoles.rows eqs)[i]).1=7) :
    CatalogLogic.relation 7 (((profileBanks 7).zip ((PrivateRoles.rows eqs)[i]).2).map
      (value (fun k => Classical.choose (hall (.inl (.inl k)))))) := by
  set n := scale eqs
  have hn : 65≤n := (scale_bounds ne).1
  have path := PrivateRoles.entrance_spec eqs i
  have rmem : (PrivateRoles.rows eqs)[i]∈(compile eqs).1 := List.getElem_mem _
  have hiN : (i:Nat)≤n := (CompiledAddresses.program_door eqs path.1).le
  have hrk : ∀ k∈((PrivateRoles.rows eqs)[i]).2,k≤n := fun k hk => (CompiledAddresses.program_ranks eqs rmem hk).le
  have ht : catalog[((PrivateRoles.rows eqs)[i]).1]?=some template := by rw [htag]; exact RoomCheck.InvLe_1_40.tag_eq
  have size : ((PrivateRoles.rows eqs)[i]).2.length=2 := by rw [row_arity eqs rmem,htag]; rfl
  have hlen : (PrivateRoles.records eqs i).length=12 := by rw [RoomGlobal.records_length i ht]; rfl
  have hb : (profileBanks ((PrivateRoles.rows eqs)[i]).1)=[1,40] := by rw [htag]; rfl
  have hrec : CopySpec.Records template WingRecords.InvLe_1_40.index 2 := CopyLocal.InvLe_1_40.records
  have hspot (k : Fin (slots eqs).length) : ((sx eqs k:ℚ):ℝ)≤(Classical.choose (hall (.inl (.inl k)))).1 ∧
      (Classical.choose (hall (.inl (.inl k)))).1≤((sx eqs k:ℚ):ℝ)+3/2 := by
    have sp := (Classical.choose_spec (hall (.inl (.inl k)))).2.2.1
    generalize Classical.choose (hall (.inl (.inl k)))=p at sp ⊢
    simp only [Sum.elim_inl,HubOwners.group,HubOwners.lo,HubOwners.hi] at sp
    obtain ⟨-,a,b⟩ := sp; exact ⟨a,by push_cast at b ⊢; linarith⟩
  have vr := value_range (fun k => Classical.choose (hall (.inl (.inl k)))) hspot
  obtain ⟨t0,h0,e0,d0⟩ := channel ne out ancs G hcov hall hevery i ht hrec CopyLocal.InvLe_1_40.lower0 size
    (by norm_num) (by rw [size]; norm_num) (by rw [hb]; rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hlen]; norm_num)
  obtain ⟨t1,h1,e1,d1⟩ := channel ne out ancs G hcov hall hevery i ht hrec CopyLocal.InvLe_1_40.lower1 size
    (by norm_num) (by rw [size]; norm_num) (by rw [hb]; rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hlen]; norm_num)
  obtain ⟨x,y,rx,ry,own,rel⟩ := RoomRow.InvLe.relation ne out ancs G hcov hall hevery i ht
    RoomCheck.InvLe_1_40.room_eq (size ▸ RoomCheck.InvLe_1_40.program_ok)
    (RoomSplit.InvLe_1_40.split size n i hn hiN hrk)
    RoomCheck.InvLe_1_40.clear1
    (by rw [RoomGlobal.records_length i ht]; rfl)
  have own0 := own ⟨8,by rw [hlen]; norm_num⟩ 0 _ rfl (Or.inl ⟨rfl,rfl⟩) _
    (Classical.choose_spec (hall (.inr ⟨i,⟨8,by rw [hlen]; norm_num⟩⟩))).1
    (by simpa using (Classical.choose_spec (hall (.inr ⟨i,⟨8,by rw [hlen]; norm_num⟩⟩))).2.1)
  have q0 := link (t:=template) hrec size hn hiN hrk (m:=0) (by decide) (by decide) (by decide)
    (ra:=(45,1)) (rb:=(46,1)) (by decide) (by decide) (by
      show (RoomFamily.InvLe.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.InvLe.roles.getD 0 []).getD 1 (0,0)).1 0≠
        (RoomFamily.InvLe.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.InvLe.roles.getD 0 []).getD 2 (0,0)).1 0
      apply ne_of_lt
      apply SepGeom.level_lt (RoomCoordinates.Axis.for_size RoomFamily.InvLe.x_ok hn) _ (by decide)
      rw [RoomCoordinates.length_coords]; decide) (e0.symm.trans own0)
  have own1 := own ⟨9,by rw [hlen]; norm_num⟩ 1 _ rfl (Or.inr ⟨rfl,rfl⟩) _
    (Classical.choose_spec (hall (.inr ⟨i,⟨9,by rw [hlen]; norm_num⟩⟩))).1
    (by simpa using (Classical.choose_spec (hall (.inr ⟨i,⟨9,by rw [hlen]; norm_num⟩⟩))).2.1)
  have q1 := link (t:=template) hrec size hn hiN hrk (m:=1) (by decide) (by decide) (by decide)
    (ra:=(55,1)) (rb:=(56,1)) (by decide) (by decide) (by
      show (RoomFamily.InvLe.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.InvLe.roles.getD 1 []).getD 1 (0,0)).1 0≠
        (RoomFamily.InvLe.xAxis.coordsR (1/(n:ℝ))).getD ((RoomFamily.InvLe.roles.getD 1 []).getD 2 (0,0)).1 0
      apply ne_of_lt
      apply SepGeom.level_lt (RoomCoordinates.Axis.for_size RoomFamily.InvLe.x_ok hn) _ (by decide)
      rw [RoomCoordinates.length_coords]; decide) (e1.symm.trans own1)
  obtain ⟨a,b,hrs⟩ : ∃ a b, ((PrivateRoles.rows eqs)[i]).2=[a,b] := by
    match h : ((PrivateRoles.rows eqs)[i]).2, size with
    | [a,b], _ => exact ⟨a,b,rfl⟩
  simp only [hrs,CopySpec.dir,List.getElem_cons_zero,List.getElem_cons_succ,
    show (3:Nat)-2=1 from rfl,show (4:Nat)-2=2 from rfl,show (2:Nat)-2=0 from rfl] at d0 d1
  simp only [CatalogLogic.relation,hrs,profileBanks,List.zip_cons_cons,List.zip_nil_right,List.map_cons,
    List.map_nil,List.getD_cons_zero,List.getD_cons_succ,DerivedAlgebra.InvLe,DerivedAlgebra.InvRevGe,
    DerivedAlgebra.ShiftedAddGe,ite_true,ite_false,Nat.succ_ne_zero,OfNat.ofNat_ne_zero,
    show (7:Nat)=0 ↔ 7=0 from Iff.rfl]
  generalize hW : value (fun k => Classical.choose (hall (.inl (.inl k))))=W at d0 d1 vr ⊢
  rw [if_neg (by decide),if_neg (by decide),if_neg (by decide)]
  have w1 := vr (40,b)
  obtain ⟨rx0,rx1⟩ := rx; obtain ⟨ry0,ry1⟩ := ry
  have A : (W (1,a))≤x := by linarith
  have B : (W (40,b))≤y := by linarith
  nlinarith [mul_le_mul A B (by linarith [w1.1]) (by linarith)]

end Main

end ArtGallery.Orthogonal.BoundaryPoint.RowValue.InvLe_1_40
end
