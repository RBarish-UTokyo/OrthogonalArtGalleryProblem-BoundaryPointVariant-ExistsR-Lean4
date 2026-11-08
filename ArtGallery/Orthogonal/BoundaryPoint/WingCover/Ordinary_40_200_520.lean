module

public import ArtGallery.Orthogonal.BoundaryPoint.SepData.Ordinary_40_200_520.Chart
public import ArtGallery.Orthogonal.BoundaryPoint.WingAssemble
public import ArtGallery.Orthogonal.BoundaryPoint.CoverData.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.ClusterData.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.SpecialData.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCellData.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.Ordinary
public import ArtGallery.Orthogonal.BoundaryPoint.DoorCell
public import ArtGallery.Orthogonal.BoundaryPoint.CellSplit
public import ArtGallery.Orthogonal.BoundaryPoint.UnionCell

/-! The cover of the `Ordinary_40_200_520` wing chart (generated): every filled point is seen by the guard of a
role (stationary roles at their record point, moving roles on their spot at the parameter of their
copy channel) or by the base guard of a copy channel through the door. The range, incidence and
match facts of the channels, the room coordinates and the room relation are hypotheses. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingCover.Ordinary_40_200_520
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles
open WingOrder.Ordinary_40_200_520 ArtGallery.Orthogonal.Hard

abbrev C : SepCert.Chart := chartOf template cache boxes WingRecords.Ordinary_40_200_520.index

theorem C_lit : C=SepData.Ordinary_40_200_520.Chart.CL := SepData.Ordinary_40_200_520.Chart.C_eq
abbrev roles : List (List RoomGrid.Index) := (WingRecords.Ordinary_40_200_520.index).2

noncomputable def gd (X Y : List ℝ) (t0 t1 t2 : ℝ) (r : Nat) : Point :=
  if r=15 then CopyLower.receiver X Y (63,6) (64,6) t0 else
  if r=16 then CopyLower.receiver X Y (94,8) (95,8) t0 else
  if r=17 then CopyLower.receiver X Y (67,4) (68,4) t1 else
  if r=18 then CopyLower.receiver X Y (71,2) (72,2) t2 else
  gridPt X Y ((roles.getD r []).getD 0 (0,0))

theorem entries : WingAssemble.entriesOK C roles [15, 16, 17, 18] CoverData.Ordinary_40_200_520.rects=true := by (try rw [C_lit]); decide +kernel

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem cover_of {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A) (one : A 0=1)
    {P : Polygon} (sub : (C.poly X Y).filled⊆P.filled) {D W b0 b1 b2 t0 t1 t2 : ℝ}
    (hD : D=50050/(s:ℝ)^2) (hW : W=(s:ℝ)/320)
    (hdl : X.getD 50 0=0) (hdr : X.getD 51 0=W) (hwy : Y.getD 20 0=1)
    (hb0 : 0≤b0 ∧ b0≤((797:ℝ)/18590)) (ht0 : 0≤t0 ∧ t0≤3/2)
    (hdoor0 : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b0*D+t0,1-D) d)
    (hrb0 : X.getD 64 0=X.getD 63 0+3/2*(1-Y.getD 6 0)/D)
    (L1_0 : 0<ArtGallery.det (X.getD 64 0,Y.getD 6 0) (X.getD 61 0,Y.getD 20 0) (X.getD 47 0,Y.getD 65 0))
    (L2_0 : ArtGallery.det (X.getD 63 0,Y.getD 6 0) (X.getD 61 0,Y.getD 20 0) (X.getD 48 0,Y.getD 65 0)<0)
    (inc0 : W-b0*(Y.getD 65 0-1)=X.getD 61 0-((X.getD 63 0-X.getD 61 0)/(1-Y.getD 6 0))*(Y.getD 65 0-1))
    (hbr0 : b0≤(X.getD 63 0-X.getD 61 0)/(1-Y.getD 6 0))
    (mt0 : CopyChannel.lineX (W+b0*D+t0,1-D) (X.getD 43 0,Y.getD 68 0) (Y.getD 71 0)=
      CopyChannel.lineX (X.getD 63 0+2/3*(X.getD 64 0-X.getD 63 0)*t0,Y.getD 6 0) (X.getD 46 0,Y.getD 67 0) (Y.getD 71 0))
    (lo0 : 1-D<Y.getD 68 0)
    (CW0_0 : ArtGallery.det (W+b0*D,1-D) (X.getD 46 0,Y.getD 71 0) (W,1)<0)
    (CW1_0 : ArtGallery.det (W+b0*D+3/2,1-D) (X.getD 46 0,Y.getD 71 0) (W,1)<0)
    (hb1 : 0≤b1 ∧ b1≤((26379:ℝ)/130130)) (ht1 : 0≤t1 ∧ t1≤3/2)
    (hdoor1 : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b1*D+t1,1-D) d)
    (hrb1 : X.getD 68 0=X.getD 67 0+3/2*(1-Y.getD 4 0)/D)
    (L1_1 : 0<ArtGallery.det (X.getD 68 0,Y.getD 4 0) (X.getD 61 0,Y.getD 20 0) (X.getD 34 0,Y.getD 47 0))
    (L2_1 : ArtGallery.det (X.getD 67 0,Y.getD 4 0) (X.getD 61 0,Y.getD 20 0) (X.getD 35 0,Y.getD 47 0)<0)
    (inc1 : W-b1*(Y.getD 47 0-1)=X.getD 61 0-((X.getD 67 0-X.getD 61 0)/(1-Y.getD 4 0))*(Y.getD 47 0-1))
    (hbr1 : b1≤(X.getD 67 0-X.getD 61 0)/(1-Y.getD 4 0))
    (mt1 : CopyChannel.lineX (W+b1*D+t1,1-D) (X.getD 30 0,Y.getD 50 0) (Y.getD 53 0)=
      CopyChannel.lineX (X.getD 67 0+2/3*(X.getD 68 0-X.getD 67 0)*t1,Y.getD 4 0) (X.getD 33 0,Y.getD 49 0) (Y.getD 53 0))
    (lo1 : 1-D<Y.getD 50 0)
    (CW0_1 : ArtGallery.det (W+b1*D,1-D) (X.getD 33 0,Y.getD 53 0) (W,1)<0)
    (CW1_1 : ArtGallery.det (W+b1*D+3/2,1-D) (X.getD 33 0,Y.getD 53 0) (W,1)<0)
    (hb2 : 0≤b2 ∧ b2≤((67979:ℝ)/130130)) (ht2 : 0≤t2 ∧ t2≤3/2)
    (hdoor2 : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b2*D+t2,1-D) d)
    (hrb2 : X.getD 72 0=X.getD 71 0+3/2*(1-Y.getD 2 0)/D)
    (L1_2 : 0<ArtGallery.det (X.getD 72 0,Y.getD 2 0) (X.getD 61 0,Y.getD 20 0) (X.getD 21 0,Y.getD 29 0))
    (L2_2 : ArtGallery.det (X.getD 71 0,Y.getD 2 0) (X.getD 61 0,Y.getD 20 0) (X.getD 22 0,Y.getD 29 0)<0)
    (inc2 : W-b2*(Y.getD 29 0-1)=X.getD 61 0-((X.getD 71 0-X.getD 61 0)/(1-Y.getD 2 0))*(Y.getD 29 0-1))
    (hbr2 : b2≤(X.getD 71 0-X.getD 61 0)/(1-Y.getD 2 0))
    (mt2 : CopyChannel.lineX (W+b2*D+t2,1-D) (X.getD 17 0,Y.getD 32 0) (Y.getD 35 0)=
      CopyChannel.lineX (X.getD 71 0+2/3*(X.getD 72 0-X.getD 71 0)*t2,Y.getD 2 0) (X.getD 20 0,Y.getD 31 0) (Y.getD 35 0))
    (lo2 : 1-D<Y.getD 32 0)
    (CW0_2 : ArtGallery.det (W+b2*D,1-D) (X.getD 20 0,Y.getD 35 0) (W,1)<0)
    (CW1_2 : ArtGallery.det (W+b2*D+3/2,1-D) (X.getD 20 0,Y.getD 35 0) (W,1)<0)
    (rel : t2≤t1+t0+(1/2))
    (g15 : gd X Y t0 t1 t2 15=RoomRelation.Ordinary.guard (s:ℝ) 3 t0) (g16 : gd X Y t0 t1 t2 16=RoomRelation.Ordinary.guard (s:ℝ) 4 t0)
    (g17 : gd X Y t0 t1 t2 17=RoomRelation.Ordinary.guard (s:ℝ) 5 t1) (g18 : gd X Y t0 t1 t2 18=RoomRelation.Ordinary.guard (s:ℝ) 6 t2)
    (c766 : X.getD 85 0=766) (c827 : X.getD 89 0=1655/2) (c1319 : X.getD 91 0=2639/2)
    (c0 : Y.getD 10 0=0) (c045 : Y.getD 14 0=45/100)
    (cL : X.getD 92 0=50352/35) (cR : X.getD 93 0=100739/70)
    (c22 : Y.getD 25 0=11/5) (ctop : Y.getD 26 0=19834298/9008765)
    {z : Point} (hz : z∈(C.poly X Y).filled) :
    (∃ r<roles.length, P.Sees (gd X Y t0 t1 t2 r) z) ∨ P.Sees (W+b0*D+t0,1-D) z ∨ P.Sees (W+b1*D+t1,1-D) z ∨ P.Sees (W+b2*D+t2,1-D) z := by
  have hs : (0:ℝ)<s := by exact_mod_cast G.pos
  have hs1 : (s:ℝ)≤1/65 := by
    have h : ((s:ℚ):ℝ)≤((RegisterForm.cap:ℚ):ℝ) := Rat.cast_le.mpr G.small
    simp only [RegisterForm.cap] at h; push_cast at h; linarith
  have hDp : 0<D := by rw [hD]; positivity
  have hD32 : 3/2≤D := by
    rw [hD,le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul hs1 hs1 hs.le (by norm_num : (0:ℝ)≤1/65)]
  have hW0 : 0≤W := by rw [hW]; positivity
  have e15 : gd X Y t0 t1 t2 15=CopyLower.receiver X Y (63,6) (64,6) t0 := by simp [gd]
  have m15 : gd X Y t0 t1 t2 15∈ArtGallery.segment (gridPt X Y (63,6)) (gridPt X Y (64,6)) := by
    rw [e15]; exact WingAssemble.receiver_mem (by rfl) ht0
  have e16 : gd X Y t0 t1 t2 16=CopyLower.receiver X Y (94,8) (95,8) t0 := by simp [gd]
  have m16 : gd X Y t0 t1 t2 16∈ArtGallery.segment (gridPt X Y (94,8)) (gridPt X Y (95,8)) := by
    rw [e16]; exact WingAssemble.receiver_mem (by rfl) ht0
  have e17 : gd X Y t0 t1 t2 17=CopyLower.receiver X Y (67,4) (68,4) t1 := by simp [gd]
  have m17 : gd X Y t0 t1 t2 17∈ArtGallery.segment (gridPt X Y (67,4)) (gridPt X Y (68,4)) := by
    rw [e17]; exact WingAssemble.receiver_mem (by rfl) ht1
  have e18 : gd X Y t0 t1 t2 18=CopyLower.receiver X Y (71,2) (72,2) t2 := by simp [gd]
  have m18 : gd X Y t0 t1 t2 18∈ArtGallery.segment (gridPt X Y (71,2)) (gridPt X Y (72,2)) := by
    rw [e18]; exact WingAssemble.receiver_mem (by rfl) ht2
  have hst : ∀ r, r∉[15, 16, 17, 18] → gd X Y t0 t1 t2 r=gridPt X Y ((roles.getD r []).getD 0 (0,0)) := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h0,h1,h2,h3⟩ := hr
    simp only [gd,if_neg h0,if_neg h1,if_neg h2,if_neg h3]
  have hmv : ∀ r∈[15, 16, 17, 18], gd X Y t0 t1 t2 r∈ArtGallery.segment (gridPt X Y (CellRoles.spotA (roles.getD r [])))
      (gridPt X Y (CellRoles.spotB (roles.getD r []))) := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · rw [show CellRoles.spotA (roles.getD 15 [])=(63,6) by decide,
        show CellRoles.spotB (roles.getD 15 [])=(64,6) by decide]; exact m15
    · rw [show CellRoles.spotA (roles.getD 16 [])=(94,8) by decide,
        show CellRoles.spotB (roles.getD 16 [])=(95,8) by decide]; exact m16
    · rw [show CellRoles.spotA (roles.getD 17 [])=(67,4) by decide,
        show CellRoles.spotB (roles.getD 17 [])=(68,4) by decide]; exact m17
    · rw [show CellRoles.spotA (roles.getD 18 [])=(71,2) by decide,
        show CellRoles.spotB (roles.getD 18 [])=(72,2) by decide]; exact m18
  let GS : Set Point := {p | (∃ r<roles.length, p=gd X Y t0 t1 t2 r) ∨ p=(W+b0*D+t0,1-D) ∨ p=(W+b1*D+t1,1-D) ∨ p=(W+b2*D+t2,1-D)}
  have key : ∃ g∈GS, P.Sees g z := by
    refine WingAssemble.cover G (WingAssemble.nondeg_of CoverData.Ordinary_40_200_520.nondeg) CoverData.Ordinary_40_200_520.rects_ok
      (fun t ht i j a b c d => WingAssemble.cell_prop (WingAssemble.comp_of CoverData.Ordinary_40_200_520.complete t ht i j a b c d))
      sub (gd X Y t0 t1 t2) (fun e he => ⟨Or.inl ⟨e.role,WingAssemble.entries_roles entries e he,rfl⟩,
        WingAssemble.guards_on G entries (gd X Y t0 t1 t2) hst hmv e he⟩) ?_ hz
    intro c hc w hw hwf
    simp only [CoverData.Ordinary_40_200_520.special,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rcases DoorCell.door G one sub SpecialData.Ordinary_40_200_520.door_50_20 hD32 hdr hdl hwy hb0.1
        (by push_cast; linarith [hb0.2]) ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
      · refine ⟨_,Or.inl ⟨6,by decide,rfl⟩,?_⟩
        rw [hst 6 (by decide)]; exact h
    · rcases DoorCell.door G one sub SpecialData.Ordinary_40_200_520.door_50_21 hD32 hdr hdl hwy hb0.1
        (by push_cast; linarith [hb0.2]) ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
      · refine ⟨_,Or.inl ⟨6,by decide,rfl⟩,?_⟩
        rw [hst 6 (by decide)]; exact h
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n2_17_29_0 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2 inc2
        hbr2 hb2.1 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n2_17_30_1 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2 inc2
        hbr2 hb2.1 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n2_20_29_3 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2 inc2
        hbr2 hb2.1 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n2_20_30_4 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2 inc2
        hbr2 hb2.1 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n2_21_29_5 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2 inc2
        hbr2 hb2.1 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n2_21_30_6 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2 inc2
        hbr2 hb2.1 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · refine ⟨_,Or.inl ⟨7,by decide,rfl⟩,WingAssemble.sees_mono sub (CellSplit.split_sound G SpecialData.Ordinary_40_200_520.split_30_30 ?_ hw)⟩
      rw [hst 7 (by decide)]; exact WingAssemble.self_mem _
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n0_43_65_7 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n0_43_66_8 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n0_46_65_10 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n0_46_66_11 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n0_47_65_12 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n0_47_66_13 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0 inc0
        hbr0 hb0.1 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n1_30_47_14 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n1_30_48_15 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n1_33_47_17 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n1_33_48_18 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n1_34_47_19 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.cell G one sub ClusterData.Ordinary_40_200_520.n1_34_48_20 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1 inc1
        hbr1 hb1.1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · refine ⟨_,Or.inl ⟨6,by decide,rfl⟩,WingAssemble.sees_mono sub (CellSplit.split_sound G SpecialData.Ordinary_40_200_520.split_43_48 ?_ hw)⟩
      rw [hst 6 (by decide)]; exact WingAssemble.self_mem _
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c0_38_70_21 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c0_39_70_22 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c0_40_70_23 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c0_41_70_24 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c0_42_70_25 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c0_43_67_26 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c0_43_70_27 hDp hW0 hD hdr hdl hwy hrb0 L1_0 L2_0
        inc0 mt0 hb0.1 (by push_cast; linarith [hb0.2]) lo0 CW0_0 CW1_0 ht0 hdoor0 hw with h|h
      · exact ⟨_,Or.inl ⟨15,by decide,rfl⟩,by rw [e15]; exact h⟩
      · exact ⟨_,Or.inr (Or.inl rfl),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c1_25_52_28 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c1_26_52_29 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c1_27_52_30 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c1_28_52_31 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c1_29_52_32 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c1_30_49_33 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c1_30_52_34 hDp hW0 hD hdr hdl hwy hrb1 L1_1 L2_1
        inc1 mt1 hb1.1 (by push_cast; linarith [hb1.2]) lo1 CW0_1 CW1_1 ht1 hdoor1 hw with h|h
      · exact ⟨_,Or.inl ⟨17,by decide,rfl⟩,by rw [e17]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c2_16_34_35 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2
        inc2 mt2 hb2.1 (by push_cast; linarith [hb2.2]) lo2 CW0_2 CW1_2 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c2_17_31_36 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2
        inc2 mt2 hb2.1 (by push_cast; linarith [hb2.2]) lo2 CW0_2 CW1_2 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · rcases NookCell.chamber_cell G one sub ClusterData.Ordinary_40_200_520.c2_17_34_37 hDp hW0 hD hdr hdl hwy hrb2 L1_2 L2_2
        inc2 mt2 hb2.1 (by push_cast; linarith [hb2.2]) lo2 CW0_2 CW1_2 ht2 hdoor2 hw with h|h
      · exact ⟨_,Or.inl ⟨18,by decide,rfl⟩,by rw [e18]; exact h⟩
      · exact ⟨_,Or.inr (Or.inr (Or.inr (rfl))),h⟩
    · have hy : (45:ℝ)/100≤w.2 := by rw [← c045]; exact hw.2.2.1
      rcases RoomCellCover.Ordinary.triangle (s:=(s:ℝ)) hs hs1 ht1 ht0 rel hy with ⟨h1,h2⟩|h|h
      · refine ⟨_,Or.inl ⟨17,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.Ordinary_40_200_520.cert0_ok RoomCellData.Ordinary_40_200_520.cert0_prim m17 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl
        · simp only [CoverAssume.Holds,gridPt,c766,c0,g17]; norm_num; first | linarith [h1] | nlinarith [h1]
        · simp only [CoverAssume.Holds,gridPt,c827,c0,g17]; norm_num; first | linarith [h2] | nlinarith [h2]
      · refine ⟨_,Or.inl ⟨16,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.Ordinary_40_200_520.cert1_ok RoomCellData.Ordinary_40_200_520.cert1_prim m16 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,c1319,c0,g16]; norm_num; first | linarith [h] | nlinarith [h]
      · refine ⟨_,Or.inl ⟨18,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.Ordinary_40_200_520.cert2_ok RoomCellData.Ordinary_40_200_520.cert2_prim m18 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,c827,c0,g18]; norm_num; first | linarith [h] | nlinarith [h]
    · have top : w.2≤19834298/9008765 := by rw [← ctop]; exact hw.2.2.2
      rcases RoomCellCover.Ordinary.relay (s:=(s:ℝ)) hs hs1 ht0 rfl top with h|h
      · refine ⟨_,Or.inl ⟨15,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.Ordinary_40_200_520.cert3_ok RoomCellData.Ordinary_40_200_520.cert3_prim m15 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,cL,c22,g15]; norm_num; first | linarith [h] | nlinarith [h]
      · refine ⟨_,Or.inl ⟨16,by decide,rfl⟩,WingAssemble.sees_mono sub (RoomCell.prim_sound G
          RoomCellData.Ordinary_40_200_520.cert4_ok RoomCellData.Ordinary_40_200_520.cert4_prim m16 hw ?_)⟩
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl
        · simp only [CoverAssume.Holds,gridPt,cR,c22,g16]; norm_num; first | linarith [h] | nlinarith [h]
  obtain ⟨g,hg,sees⟩ := key
  rcases hg with ⟨r,hr,rfl⟩|rfl|rfl|rfl
  · exact Or.inl ⟨r,hr,sees⟩
  · exact Or.inr (Or.inl sees)
  · exact Or.inr (Or.inr (Or.inl sees))
  · exact Or.inr (Or.inr (Or.inr (sees)))

end ArtGallery.Orthogonal.BoundaryPoint.WingCover.Ordinary_40_200_520
end
