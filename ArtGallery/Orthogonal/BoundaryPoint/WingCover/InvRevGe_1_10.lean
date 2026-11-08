module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.InvRevGe_1_10.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.WingAssemble
public import ArtGallery.Orthogonal.BoundaryPoint.CoverData.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.ClusterData.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.SpecialData.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCellData.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.InvRevGe
public import ArtGallery.Orthogonal.BoundaryPoint.DoorCell
public import ArtGallery.Orthogonal.BoundaryPoint.CellSplit
public import ArtGallery.Orthogonal.BoundaryPoint.UnionCell

/-! The cover of the `InvRevGe_1_10` wing chart (generated): every filled point is seen by the guard of a
role (stationary roles at their record point, moving roles on their spot at the parameter of their
copy channel) or by the base guard of a copy channel through the door. The range, incidence and
match facts of the channels, the room coordinates and the room relation are hypotheses. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingCover.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles
open WingOrder.InvRevGe_1_10 ArtGallery.Orthogonal.Hard

abbrev C : SepCert.Chart := chartOf template cache boxes WingRecords.InvRevGe_1_10.index

theorem C_lit : C=SepData.InvRevGe_1_10.Chart.CL := SepData.InvRevGe_1_10.Chart.C_eq
abbrev roles : List (List RoomGrid.Index) := (WingRecords.InvRevGe_1_10.index).2

noncomputable def gd (X Y : List ℝ) (t0 t1 : ℝ) (r : Nat) : Point :=
  if r=8 then CopyLower.receiver X Y (45,1) (46,1) t0 else
  if r=9 then CopyLower.receiver X Y (51,1) (52,1) t1 else
  gridPt X Y ((roles.getD r []).getD 0 (0,0))

theorem entries : WingAssemble.entriesOK C roles [8, 9] CoverData.InvRevGe_1_10.rects=true := by (try rw [C_lit]); decide +kernel

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem cover_of {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A) (one : A 0=1)
    {P : Polygon} (sub : (C.poly X Y).filled⊆P.filled) {D W b0 b1 t0 t1 : ℝ}
    (hD : D=50050/(s:ℝ)^2) (hW : W=(s:ℝ)/320)
    (hdl : X.getD 32 0=0) (hdr : X.getD 33 0=W) (hwy : Y.getD 12 0=1)
    (hb0 : 0≤b0 ∧ b0≤((509:ℝ)/130130)) (ht0 : 0≤t0 ∧ t0≤3/2)
    (hdoor0 : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b0*D+t0,1-D) d)
    (hrb0 : X.getD 46 0=X.getD 45 0+3/2*(1-Y.getD 1 0)/D)
    (L1_0 : 0<ArtGallery.det (X.getD 46 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 29 0,Y.getD 36 0))
    (L2_0 : ArtGallery.det (X.getD 45 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 30 0,Y.getD 36 0)<0)
    (inc0 : W-b0*(Y.getD 36 0-1)=X.getD 44 0-((X.getD 45 0-X.getD 44 0)/(1-Y.getD 1 0))*(Y.getD 36 0-1))
    (hbr0 : b0≤(X.getD 45 0-X.getD 44 0)/(1-Y.getD 1 0))
    (mt0 : CopyChannel.lineX (W+b0*D+t0,1-D) (X.getD 25 0,Y.getD 39 0) (Y.getD 42 0)=
      CopyChannel.lineX (X.getD 45 0+2/3*(X.getD 46 0-X.getD 45 0)*t0,Y.getD 1 0) (X.getD 28 0,Y.getD 38 0) (Y.getD 42 0))
    (lo0 : 1-D<Y.getD 39 0)
    (CW0_0 : ArtGallery.det (W+b0*D,1-D) (X.getD 28 0,Y.getD 42 0) (W,1)<0)
    (CW1_0 : ArtGallery.det (W+b0*D+3/2,1-D) (X.getD 28 0,Y.getD 42 0) (W,1)<0)
    (hb1 : 0≤b1 ∧ b1≤((1679:ℝ)/130130)) (ht1 : 0≤t1 ∧ t1≤3/2)
    (hdoor1 : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b1*D+t1,1-D) d)
    (hrb1 : X.getD 52 0=X.getD 51 0+3/2*(1-Y.getD 1 0)/D)
    (L1_1 : 0<ArtGallery.det (X.getD 52 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 16 0,Y.getD 18 0))
    (L2_1 : ArtGallery.det (X.getD 51 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 17 0,Y.getD 18 0)<0)
    (inc1 : W-b1*(Y.getD 18 0-1)=X.getD 44 0-((X.getD 51 0-X.getD 44 0)/(1-Y.getD 1 0))*(Y.getD 18 0-1))
    (hbr1 : b1≤(X.getD 51 0-X.getD 44 0)/(1-Y.getD 1 0))
    (mt1 : CopyChannel.lineX (W+b1*D+t1,1-D) (X.getD 12 0,Y.getD 21 0) (Y.getD 24 0)=
      CopyChannel.lineX (X.getD 51 0+2/3*(X.getD 52 0-X.getD 51 0)*t1,Y.getD 1 0) (X.getD 15 0,Y.getD 20 0) (Y.getD 24 0))
    (lo1 : 1-D<Y.getD 21 0)
    (CW0_1 : ArtGallery.det (W+b1*D,1-D) (X.getD 15 0,Y.getD 24 0) (W,1)<0)
    (CW1_1 : ArtGallery.det (W+b1*D+3/2,1-D) (X.getD 15 0,Y.getD 24 0) (W,1)<0)
    (rel : 1≤(t0+1/2)*(5/2-(t1+1/2)))
    (gA : gd X Y t0 t1 8=RoomRelation.InvRevGe.guard (s:ℝ) 0 t0) (gB : gd X Y t0 t1 9=RoomRelation.InvRevGe.guard (s:ℝ) 1 t1)
    (cAx : X.getD 50 0=497/2) (cAy : Y.getD 6 0=((-23:ℝ)/6))
    (cBx : X.getD 53 0=501/2-(s:ℝ)^4/400800400) (cBy : Y.getD 8 0=((-11:ℝ)/3))
    (cax : X.getD 55 0=501/2)
    {z : Point} (hz : z∈(C.poly X Y).filled) :
    (∃ r<roles.length, P.Sees (gd X Y t0 t1 r) z) ∨ P.Sees (W+b0*D+t0,1-D) z ∨ P.Sees (W+b1*D+t1,1-D) z := by
  have hs : (0:ℝ)<s := by exact_mod_cast G.pos
  have hs1 : (s:ℝ)≤1/65 := by
    have h : ((s:ℚ):ℝ)≤((RegisterForm.cap:ℚ):ℝ) := Rat.cast_le.mpr G.small
    simp only [RegisterForm.cap] at h; push_cast at h; linarith
  have hDp : 0<D := by rw [hD]; positivity
  have hD32 : 3/2≤D := by
    rw [hD,le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul hs1 hs1 hs.le (by norm_num : (0:ℝ)≤1/65)]
  have hW0 : 0≤W := by rw [hW]; positivity
  have e8 : gd X Y t0 t1 8=CopyLower.receiver X Y (45,1) (46,1) t0 := by simp [gd]
  have m8 : gd X Y t0 t1 8∈ArtGallery.segment (gridPt X Y (45,1)) (gridPt X Y (46,1)) := by
    rw [e8]; exact WingAssemble.receiver_mem (by rfl) ht0
  have e9 : gd X Y t0 t1 9=CopyLower.receiver X Y (51,1) (52,1) t1 := by simp [gd]
  have m9 : gd X Y t0 t1 9∈ArtGallery.segment (gridPt X Y (51,1)) (gridPt X Y (52,1)) := by
    rw [e9]; exact WingAssemble.receiver_mem (by rfl) ht1
  have hst : ∀ r, r∉[8, 9] → gd X Y t0 t1 r=gridPt X Y ((roles.getD r []).getD 0 (0,0)) := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h0,h1⟩ := hr
    simp only [gd,if_neg h0,if_neg h1]
  have hmv : ∀ r∈[8, 9], gd X Y t0 t1 r∈ArtGallery.segment (gridPt X Y (CellRoles.spotA (roles.getD r [])))
      (gridPt X Y (CellRoles.spotB (roles.getD r []))) := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · rw [show CellRoles.spotA (roles.getD 8 [])=(45,1) by decide,
        show CellRoles.spotB (roles.getD 8 [])=(46,1) by decide]; exact m8
    · rw [show CellRoles.spotA (roles.getD 9 [])=(51,1) by decide,
        show CellRoles.spotB (roles.getD 9 [])=(52,1) by decide]; exact m9
  let GS : Set Point := {p | (∃ r<roles.length, p=gd X Y t0 t1 r) ∨ p=(W+b0*D+t0,1-D) ∨ p=(W+b1*D+t1,1-D)}
  have key : ∃ g∈GS, P.Sees g z := by
    refine WingAssemble.cover G (WingAssemble.nondeg_of CoverData.InvRevGe_1_10.nondeg) CoverData.InvRevGe_1_10.rects_ok
      (fun t ht i j a b c d => WingAssemble.cell_prop (WingAssemble.comp_of CoverData.InvRevGe_1_10.complete t ht i j a b c d))
      sub (gd X Y t0 t1) (fun e he => ⟨Or.inl ⟨e.role,WingAssemble.entries_roles entries e he,rfl⟩,
        WingAssemble.guards_on G entries (gd X Y t0 t1) hst hmv e he⟩) ?_ hz
    intro c hc w hw hwf
    simp only [CoverData.InvRevGe_1_10.special,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rcases DoorCell.door G one sub SpecialData.InvRevGe_1_10.door_32_12 hD32 hdr hdl hwy hb0.1
        (by push_cast; linarith [hb0.2]) ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
      · refine ⟨_,Or.inl ⟨4,by decide,rfl⟩,?_⟩
        rw [hst 4 (by decide)]; exact h
    · rcases DoorCell.door G one sub SpecialData.InvRevGe_1_10.door_32_13 hD32 hdr hdl hwy hb0.1
        (by push_cast; linarith [hb0.2]) ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
      · refine ⟨_,Or.inl ⟨4,by decide,rfl⟩,?_⟩
        rw [hst 4 (by decide)]; exact h
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n1_12_18_0 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n1_12_19_1 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n1_15_18_3 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n1_15_19_4 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n1_16_18_5 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n1_16_19_6 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · refine ⟨_,Or.inl ⟨4,by decide,rfl⟩,WingAssemble.sees_mono sub (CellSplit.split_sound G SpecialData.InvRevGe_1_10.split_25_19 ?_ hw)⟩
      rw [hst 4 (by decide)]; exact WingAssemble.self_mem _
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n0_25_36_7 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n0_25_37_8 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n0_28_36_10 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n0_28_37_11 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n0_29_36_12 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.InvRevGe_1_10.n0_29_37_13 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c0_20_41_14 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c0_21_41_15 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c0_22_41_16 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c0_23_41_17 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c0_24_41_18 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c0_25_38_19 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c0_25_41_20 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,by rw [e8]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c1_11_23_21 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c1_12_20_22 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.InvRevGe_1_10.c1_12_23_23 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨9,by decide,rfl⟩,by rw [e9]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (rfl)),h⟩
    · rcases UnionCell.union_sound G one SpecialData.InvRevGe_1_10.union_41_14 (ga:=gd X Y t0 t1 4) (gb:=gd X Y t0 t1 8) (by rw [hst 4 (by decide)]; exact WingAssemble.self_mem _) m8 hw with h|h
      · exact ⟨_,Or.inl ⟨4,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
      · exact ⟨_,Or.inl ⟨8,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
    · rcases UnionCell.union_sound G one SpecialData.InvRevGe_1_10.union_19_35 (ga:=gd X Y t0 t1 4) (gb:=gd X Y t0 t1 4) (by rw [hst 4 (by decide)]; exact WingAssemble.self_mem _) (by rw [hst 4 (by decide)]; exact WingAssemble.self_mem _) hw with h|h
      · exact ⟨_,Or.inl ⟨4,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
      · exact ⟨_,Or.inl ⟨4,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
    · rcases UnionCell.union_sound G one SpecialData.InvRevGe_1_10.union_20_35 (ga:=gd X Y t0 t1 4) (gb:=gd X Y t0 t1 4) (by rw [hst 4 (by decide)]; exact WingAssemble.self_mem _) (by rw [hst 4 (by decide)]; exact WingAssemble.self_mem _) hw with h|h
      · exact ⟨_,Or.inl ⟨4,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
      · exact ⟨_,Or.inl ⟨4,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
    · rcases UnionCell.union_sound G one SpecialData.InvRevGe_1_10.union_41_17 (ga:=gd X Y t0 t1 5) (gb:=gd X Y t0 t1 5) (by rw [hst 5 (by decide)]; exact WingAssemble.self_mem _) (by rw [hst 5 (by decide)]; exact WingAssemble.self_mem _) hw with h|h
      · exact ⟨_,Or.inl ⟨5,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
      · exact ⟨_,Or.inl ⟨5,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
    · rcases UnionCell.union_sound G one SpecialData.InvRevGe_1_10.union_30_51 (ga:=gd X Y t0 t1 6) (gb:=gd X Y t0 t1 6) (by rw [hst 6 (by decide)]; exact WingAssemble.self_mem _) (by rw [hst 6 (by decide)]; exact WingAssemble.self_mem _) hw with h|h
      · exact ⟨_,Or.inl ⟨6,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
      · exact ⟨_,Or.inl ⟨6,by decide,rfl⟩,WingAssemble.sees_mono sub h⟩
    · have hxa : w.1≤501/2 := by
        have := CoverChain.lev_le G.hx (i:=54) (j:=55) (by rw [G.lx]; decide) (by decide)
        exact hw.2.1.trans (this.trans_eq cax)
      have hx0 : DerivedAlgebra.InRange (t0+1/2) := ⟨by linarith [ht0.1],by linarith [ht0.2]⟩
      have hx1 : DerivedAlgebra.InRange (t1+1/2) := ⟨by linarith [ht1.1],by linarith [ht1.2]⟩
      have C := RoomCellCover.InvRevGe.cell (s:=(s:ℝ)) hs hs1 hx0 hx1 rel hxa
      rw [add_sub_cancel_right,add_sub_cancel_right] at C
      rcases C with h|h
      · refine ⟨_,Or.inl ⟨8,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.InvRevGe_1_10.cert0_ok RoomCellData.InvRevGe_1_10.cert0_prim m8 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,cAx,cAy,gA]; norm_num; first | linarith [h] | nlinarith [h]
      · refine ⟨_,Or.inl ⟨9,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.InvRevGe_1_10.cert2_ok RoomCellData.InvRevGe_1_10.cert2_prim m9 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,cBx,cBy,gB]; norm_num; first | linarith [h] | nlinarith [h]
    · have hxa : w.1≤501/2 := by
        have := CoverChain.lev_le G.hx (i:=55) (j:=55) (by rw [G.lx]; decide) (by decide)
        exact hw.2.1.trans (this.trans_eq cax)
      have hx0 : DerivedAlgebra.InRange (t0+1/2) := ⟨by linarith [ht0.1],by linarith [ht0.2]⟩
      have hx1 : DerivedAlgebra.InRange (t1+1/2) := ⟨by linarith [ht1.1],by linarith [ht1.2]⟩
      have C := RoomCellCover.InvRevGe.cell (s:=(s:ℝ)) hs hs1 hx0 hx1 rel hxa
      rw [add_sub_cancel_right,add_sub_cancel_right] at C
      rcases C with h|h
      · refine ⟨_,Or.inl ⟨8,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.InvRevGe_1_10.cert1_ok RoomCellData.InvRevGe_1_10.cert1_prim m8 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,cAx,cAy,gA]; norm_num; first | linarith [h] | nlinarith [h]
      · refine ⟨_,Or.inl ⟨9,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.InvRevGe_1_10.cert3_ok RoomCellData.InvRevGe_1_10.cert3_prim m9 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,cBx,cBy,gB]; norm_num; first | linarith [h] | nlinarith [h]
  obtain ⟨g,hg,sees⟩ := key
  rcases hg with ⟨r,hr,rfl⟩|rfl|rfl
  · exact Or.inl ⟨r,hr,sees⟩
  · exact Or.inr (Or.inl sees)
  · exact Or.inr (Or.inr (sees))

end ArtGallery.Orthogonal.BoundaryPoint.WingCover.InvRevGe_1_10
end
