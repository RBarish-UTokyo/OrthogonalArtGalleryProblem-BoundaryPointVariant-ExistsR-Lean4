module

public import ArtGallery.Orthogonal.BoundaryPoint.WingSpec
public import ArtGallery.Orthogonal.BoundaryPoint.WingCover.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.X

/-! The cover of the `Shifted_40_200_520` wing in the uniform form `WingSpec.Cover` (generated): the hypotheses
of `WingCover.Shifted_40_200_520.cover_of` hold at every admissible size. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Shifted_40_200_520
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles RoomCoordinates
open WingOrder.Shifted_40_200_520 ArtGallery.Orthogonal.Hard

def mv : List (Nat × Nat × RoomGrid.Index × RoomGrid.Index) := [(15,0,(63,6),(64,6)),(16,0,(94,8),(95,8)),(17,1,(67,4),(68,4)),(18,2,(71,2),(72,2))]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem cover : WingSpec.Cover template WingRecords.Shifted_40_200_520.index 1 mv := by
  unfold WingSpec.Cover
  intro rs size n j hn hj hr s args X Y W L P sub τ hτ hrel hdoor z hz
  have size' : rs.length=3 := by simpa [CatalogRanks.profileBanks] using size
  have hn0 : 0<n := by omega
  set sr : ℝ := ((s:ℚ):ℝ) with hsr_def
  have hsr : (0:ℝ)<sr := by
    simp only [sr,s]; have : (0:ℚ)<n := by exact_mod_cast hn0
    exact_mod_cast (show (0:ℚ)<1/n by positivity)
  have hsr1 : sr≤1/65 := by
    have h65 : (65:ℝ)≤n := by exact_mod_cast hn
    have e : sr=1/(n:ℝ) := by rw [hsr_def]; simp only [s]; push_cast; ring
    rw [e]; exact one_div_le_one_div_of_le (by norm_num) h65
  have gs : getRat args 0=s := rfl
  obtain ⟨G,Leq,-⟩ := WingModel.good_at_size (t:=template) (size' ▸ WingBounds.Shifted_40_200_520.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.Shifted_40_200_520.records⟩
    (fun g hx hy => WingChart.Shifted_40_200_520.simple g hx hy) SepData.Shifted_40_200_520.cert (WingFill.Shifted_40_200_520.filled_eq size' n j hn hj hr)
  simp only [L] at hz sub
  rw [Leq] at hz sub
  have m := WingModel.model_at_size (t:=template) (size' ▸ WingBounds.Shifted_40_200_520.certificate) n j hn hj hr sizes verified
  have one : RegisterTable.atomVal (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 0=1 := rfl
  have hJ := WingModel.args_unit hn0 hj hr 0
  have hJ' : (0:ℝ)≤(getRat args 1:ℝ) ∧ (getRat args 1:ℝ)≤1 := ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  -- channel 0: bank 40
  have hQ0 := WingModel.args_unit hn0 hj hr 1
  have hQ0' : (0:ℝ)≤(getRat args 2:ℝ) ∧ (getRat args 2:ℝ)≤1 := ⟨by exact_mod_cast hQ0.1,by exact_mod_cast hQ0.2⟩
  set b0 : ℝ := ((((40:ℕ):ℝ)-1/5)/1001+5/2002*(getRat args 2:ℝ)+40/1001*(getRat args 1:ℝ)*sr : ℝ) with hb0_def
  obtain ⟨hwy_0,-,-,-,-,bLow_0,-,-,-,-,-,hdl_0,hdr_0⟩ := CopyRange.Shifted_40_200_520.ranges0 m rfl hJ hQ0
  obtain ⟨hwx_0,hrb_0,L1_0,L2_0,-,H43_0,CW0_0,CW1_0⟩ := CopyRange.Shifted_40_200_520.rangesX0 m rfl hJ hQ0
  have hb0 : 0≤b0 ∧ b0≤((797:ℝ)/18590) := by
    simp only [b0]; constructor
    · nlinarith [mul_nonneg hJ'.1 hsr.le]
    · nlinarith [mul_le_mul hJ'.2 hsr1 hsr.le zero_le_one]
  have hbase0 : WingSpec.base 1 args τ 0=(sr/320+b0*(50050/sr^2)+τ 0,1-50050/sr^2) := by
    simp [WingSpec.base,CatalogRanks.profileBanks,gs,b0,sr]
  have hdoor0 := hdoor 0 (by simp [CatalogRanks.profileBanks])
  rw [hbase0] at hdoor0
  have ht0 := hτ 0 (by simp [CatalogRanks.profileBanks])
  have inc00 := CopyInc.Shifted_40_200_520.lower0 m
  have hY0 : Y.getD 65 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 968 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 65]; rfl
  have ex0 : X.getD 63 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 63]; rfl
  have ey0 : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 6]; rfl
  have hrr0 : ((45:ℝ))=(X.getD 63 0-301/2)/(1-Y.getD 6 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex0,ey0,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have inc0 : sr/320-b0*(Y.getD 65 0-1)=X.getD 61 0-((X.getD 63 0-X.getD 61 0)/(1-Y.getD 6 0))*(Y.getD 65 0-1) := by
    rw [hwx_0,hY0,←hrr0]; exact inc00
  have hbr0 : b0≤(X.getD 63 0-X.getD 61 0)/(1-Y.getD 6 0) :=
    WingSpec.slope_le inc0 (by linarith [H43_0]) (by rw [hwx_0]; linarith)
  replace bLow_0 : 0<(1:ℝ)*(Y.getD 68 0)+(-1:ℝ)*(1-50050/sr^2) := bLow_0
  have lo0 : 1-50050/sr^2<Y.getD 68 0 := by linarith [bLow_0]
  have mt0 := CopyMatch.Shifted_40_200_520.upper0 m rfl (ne_of_gt lo0)
    (ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide) (by decide : 6<67))) (τ 0)
  -- channel 1: bank 200
  have hQ1 := WingModel.args_unit hn0 hj hr 2
  have hQ1' : (0:ℝ)≤(getRat args 3:ℝ) ∧ (getRat args 3:ℝ)≤1 := ⟨by exact_mod_cast hQ1.1,by exact_mod_cast hQ1.2⟩
  set b1 : ℝ := ((((200:ℕ):ℝ)-1/5)/1001+5/2002*(getRat args 3:ℝ)+40/1001*(getRat args 1:ℝ)*sr : ℝ) with hb1_def
  obtain ⟨hwy_1,-,-,-,-,bLow_1,-,-,-,-,-,hdl_1,hdr_1⟩ := CopyRange.Shifted_40_200_520.ranges1 m rfl hJ hQ1
  obtain ⟨hwx_1,hrb_1,L1_1,L2_1,-,H43_1,CW0_1,CW1_1⟩ := CopyRange.Shifted_40_200_520.rangesX1 m rfl hJ hQ1
  have hb1 : 0≤b1 ∧ b1≤((26379:ℝ)/130130) := by
    simp only [b1]; constructor
    · nlinarith [mul_nonneg hJ'.1 hsr.le]
    · nlinarith [mul_le_mul hJ'.2 hsr1 hsr.le zero_le_one]
  have hbase1 : WingSpec.base 1 args τ 1=(sr/320+b1*(50050/sr^2)+τ 1,1-50050/sr^2) := by
    simp [WingSpec.base,CatalogRanks.profileBanks,gs,b1,sr]
  have hdoor1 := hdoor 1 (by simp [CatalogRanks.profileBanks])
  rw [hbase1] at hdoor1
  have ht1 := hτ 1 (by simp [CatalogRanks.profileBanks])
  have inc10 := CopyInc.Shifted_40_200_520.lower1 m
  have hY1 : Y.getD 47 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 748 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 47]; rfl
  have ex1 : X.getD 67 0=((((axisOf template false).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 67]; rfl
  have ey1 : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 4]; rfl
  have hrr1 : ((415/6:ℝ))=(X.getD 67 0-301/2)/(1-Y.getD 4 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex1,ey1,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have inc1 : sr/320-b1*(Y.getD 47 0-1)=X.getD 61 0-((X.getD 67 0-X.getD 61 0)/(1-Y.getD 4 0))*(Y.getD 47 0-1) := by
    rw [hwx_1,hY1,←hrr1]; exact inc10
  have hbr1 : b1≤(X.getD 67 0-X.getD 61 0)/(1-Y.getD 4 0) :=
    WingSpec.slope_le inc1 (by linarith [H43_1]) (by rw [hwx_1]; linarith)
  replace bLow_1 : 0<(1:ℝ)*(Y.getD 50 0)+(-1:ℝ)*(1-50050/sr^2) := bLow_1
  have lo1 : 1-50050/sr^2<Y.getD 50 0 := by linarith [bLow_1]
  have mt1 := CopyMatch.Shifted_40_200_520.upper1 m rfl (ne_of_gt lo1)
    (ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide) (by decide : 4<49))) (τ 1)
  -- channel 2: bank 520
  have hQ2 := WingModel.args_unit hn0 hj hr 3
  have hQ2' : (0:ℝ)≤(getRat args 4:ℝ) ∧ (getRat args 4:ℝ)≤1 := ⟨by exact_mod_cast hQ2.1,by exact_mod_cast hQ2.2⟩
  set b2 : ℝ := ((((520:ℕ):ℝ)-1/5)/1001+5/2002*(getRat args 4:ℝ)+40/1001*(getRat args 1:ℝ)*sr : ℝ) with hb2_def
  obtain ⟨hwx_2,hwy_2,hrb_2,L1_2,L2_2,-,H43_2⟩ := CopyRange.Shifted_40_200_520.ranges2 m rfl hJ hQ2
  obtain ⟨-,-,-,-,bLow_2,-,-,-,-,-,hdl_2,hdr_2,CW0_2,CW1_2⟩ := CopyRange.Shifted_40_200_520.rangesX2 m rfl hJ hQ2
  have hb2 : 0≤b2 ∧ b2≤((67979:ℝ)/130130) := by
    simp only [b2]; constructor
    · nlinarith [mul_nonneg hJ'.1 hsr.le]
    · nlinarith [mul_le_mul hJ'.2 hsr1 hsr.le zero_le_one]
  have hbase2 : WingSpec.base 1 args τ 2=(sr/320+b2*(50050/sr^2)+τ 2,1-50050/sr^2) := by
    simp [WingSpec.base,CatalogRanks.profileBanks,gs,b2,sr]
  have hdoor2 := hdoor 2 (by simp [CatalogRanks.profileBanks])
  rw [hbase2] at hdoor2
  have ht2 := hτ 2 (by simp [CatalogRanks.profileBanks])
  have inc20 := CopyInc.Shifted_40_200_520.lower2 m
  have hY2 : Y.getD 29 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 525 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 29]; rfl
  have ex2 : X.getD 71 0=((((axisOf template false).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 71]; rfl
  have ey2 : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 2]; rfl
  have hrr2 : ((217/2:ℝ) + (1/25025:ℝ)*sr^2)=(X.getD 71 0-301/2)/(1-Y.getD 2 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex2,ey2,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have inc2 : sr/320-b2*(Y.getD 29 0-1)=X.getD 61 0-((X.getD 71 0-X.getD 61 0)/(1-Y.getD 2 0))*(Y.getD 29 0-1) := by
    rw [hwx_2,hY2,←hrr2]; exact inc20
  have hbr2 : b2≤(X.getD 71 0-X.getD 61 0)/(1-Y.getD 2 0) :=
    WingSpec.slope_le inc2 (by linarith [H43_2]) (by rw [hwx_2]; linarith)
  replace bLow_2 : 0<(1:ℝ)*(Y.getD 32 0)+(-1:ℝ)*(1-50050/sr^2) := bLow_2
  have lo2 : 1-50050/sr^2<Y.getD 32 0 := by linarith [bLow_2]
  have mt2 := CopyMatch.Shifted_40_200_520.upper2 m rfl (ne_of_gt lo2)
    (ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide) (by decide : 2<31))) (τ 2)
  have hdl : X.getD 50 0=0 := by rw [hdl_0]; norm_num
  have hwy : Y.getD 20 0=1 := by rw [hwy_0]; norm_num
  have rel : τ 2≤τ 1+τ 0+(-2) := by
    simp [CatalogLogic.relation,CatalogRanks.profileBanks,List.range_succ,DerivedAlgebra.ShiftedAddGe] at hrel; linarith
  have g15 : WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 15=RoomRelation.Shifted.guard sr 3 (τ 0) := by
    rw [show WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 15=CopyLower.receiver X Y (63,6) (64,6) (τ 0) by simp [WingCover.Shifted_40_200_520.gd]]
    exact WingSpec.receiver_slot (ra:=(63,6)) (rb:=(64,6)) CopyLocal.Shifted_40_200_520.records size' hn hj hr (m:=3) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl (τ 0)
  have g16 : WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 16=RoomRelation.Shifted.guard sr 4 (τ 0) := by
    rw [show WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 16=CopyLower.receiver X Y (94,8) (95,8) (τ 0) by simp [WingCover.Shifted_40_200_520.gd]]
    exact WingSpec.receiver_slot (ra:=(94,8)) (rb:=(95,8)) CopyLocal.Shifted_40_200_520.records size' hn hj hr (m:=4) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl (τ 0)
  have g17 : WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 17=RoomRelation.Shifted.guard sr 5 (τ 1) := by
    rw [show WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 17=CopyLower.receiver X Y (67,4) (68,4) (τ 1) by simp [WingCover.Shifted_40_200_520.gd]]
    exact WingSpec.receiver_slot (ra:=(67,4)) (rb:=(68,4)) CopyLocal.Shifted_40_200_520.records size' hn hj hr (m:=5) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl (τ 1)
  have g18 : WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 18=RoomRelation.Shifted.guard sr 6 (τ 2) := by
    rw [show WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) 18=CopyLower.receiver X Y (71,2) (72,2) (τ 2) by simp [WingCover.Shifted_40_200_520.gd]]
    exact WingSpec.receiver_slot (ra:=(71,2)) (rb:=(72,2)) CopyLocal.Shifted_40_200_520.records size' hn hj hr (m:=6) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl (τ 2)
  have c766 : X.getD 85 0=766 := by
    have e : X.getD 85 0=((((axisOf template false).coordsQ (getRat args 0)).getD 24 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 85]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have c827 : X.getD 89 0=1655/2 := by
    have e : X.getD 89 0=((((axisOf template false).coordsQ (getRat args 0)).getD 28 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 89]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have c1319 : X.getD 91 0=2639/2 := by
    have e : X.getD 91 0=((((axisOf template false).coordsQ (getRat args 0)).getD 30 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 91]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have c0 : Y.getD 10 0=0 := by
    have e : Y.getD 10 0=((((axisOf template true).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl true 10]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have c045 : Y.getD 14 0=45/100 := by
    have e : Y.getD 14 0=((((axisOf template true).coordsQ (getRat args 0)).getD 14 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl true 14]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have cL : X.getD 92 0=50352/35 := by
    have e : X.getD 92 0=((((axisOf template false).coordsQ (getRat args 0)).getD 31 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 92]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have cR : X.getD 93 0=100739/70 := by
    have e : X.getD 93 0=((((axisOf template false).coordsQ (getRat args 0)).getD 32 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 93]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have c22 : Y.getD 25 0=11/5 := by
    have e : Y.getD 25 0=((((axisOf template true).coordsQ (getRat args 0)).getD 22 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl true 25]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have ctop : Y.getD 26 0=19834298/9008765 := by
    have e : Y.getD 26 0=((((axisOf template true).coordsQ (getRat args 0)).getD 23 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl true 26]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Shifted.xAxis,RoomFamily.Shifted.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have key := WingCover.Shifted_40_200_520.cover_of G one sub
    (hD := rfl) (hW := rfl) (hdl := hdl)
    (hdr := hdr_0) (hwy := hwy)
    (hb0 := hb0) (ht0 := ht0) (hdoor0 := hdoor0) (hrb0 := hrb_0) (L1_0 := L1_0)
    (L2_0 := L2_0) (inc0 := inc0) (hbr0 := hbr0) (mt0 := mt0) (lo0 := lo0)
    (CW0_0 := CW0_0) (CW1_0 := CW1_0)
    (hb1 := hb1) (ht1 := ht1) (hdoor1 := hdoor1) (hrb1 := hrb_1) (L1_1 := L1_1)
    (L2_1 := L2_1) (inc1 := inc1) (hbr1 := hbr1) (mt1 := mt1) (lo1 := lo1)
    (CW0_1 := CW0_1) (CW1_1 := CW1_1)
    (hb2 := hb2) (ht2 := ht2) (hdoor2 := hdoor2) (hrb2 := hrb_2) (L1_2 := L1_2)
    (L2_2 := L2_2) (inc2 := inc2) (hbr2 := hbr2) (mt2 := mt2) (lo2 := lo2)
    (CW0_2 := CW0_2) (CW1_2 := CW1_2)
    (g15 := g15) (g16 := g16) (g17 := g17) (g18 := g18) (rel := rel) (c766 := c766) (c827 := c827) (c1319 := c1319) (c0 := c0) (c045 := c045) (cL := cL) (cR := cR) (c22 := c22) (ctop := ctop)
    hz
  have hg : ∀ r, WingCover.Shifted_40_200_520.gd X Y (τ 0) (τ 1) (τ 2) r=WingSpec.guardOf X Y mv τ (WingRecords.Shifted_40_200_520.index).2 r := by
    intro r
    by_cases h15 : r=15
    · subst h15; simp [WingCover.Shifted_40_200_520.gd,WingSpec.guardOf,mv,List.lookup]
    by_cases h16 : r=16
    · subst h16; simp [WingCover.Shifted_40_200_520.gd,WingSpec.guardOf,mv,List.lookup]
    by_cases h17 : r=17
    · subst h17; simp [WingCover.Shifted_40_200_520.gd,WingSpec.guardOf,mv,List.lookup]
    by_cases h18 : r=18
    · subst h18; simp [WingCover.Shifted_40_200_520.gd,WingSpec.guardOf,mv,List.lookup]
    have e15 : (r == 15)=false := by simpa using h15
    have e16 : (r == 16)=false := by simpa using h16
    have e17 : (r == 17)=false := by simpa using h17
    have e18 : (r == 18)=false := by simpa using h18
    simp [WingCover.Shifted_40_200_520.gd,WingSpec.guardOf,mv,List.lookup,h15,e15,h16,e16,h17,e17,h18,e18]
  rcases key with ⟨r,hr,h⟩|h|h|h
  · exact Or.inl ⟨r,hr,by rw [← hg]; exact h⟩
  · exact Or.inr ⟨0,by simp [CatalogRanks.profileBanks],by rw [hbase0]; exact h⟩
  · exact Or.inr ⟨1,by simp [CatalogRanks.profileBanks],by rw [hbase1]; exact h⟩
  · exact Or.inr ⟨2,by simp [CatalogRanks.profileBanks],by rw [hbase2]; exact h⟩

end ArtGallery.Orthogonal.BoundaryPoint.WingFinal.Shifted_40_200_520
end
