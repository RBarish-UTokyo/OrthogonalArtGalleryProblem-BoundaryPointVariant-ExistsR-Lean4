module

public import ArtGallery.Orthogonal.BoundaryPoint.WingSpec
public import ArtGallery.Orthogonal.BoundaryPoint.WingCover.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.X

/-! The cover of the `InvRevGe_1_10` wing in the uniform form `WingSpec.Cover` (generated): the hypotheses
of `WingCover.InvRevGe_1_10.cover_of` hold at every admissible size. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert SepWing CoverChain CoverAssume CellRoles RoomCoordinates
open WingOrder.InvRevGe_1_10 ArtGallery.Orthogonal.Hard

def mv : List (Nat × Nat × RoomGrid.Index × RoomGrid.Index) := [(8,0,(45,1),(46,1)),(9,1,(51,1),(52,1))]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem cover : WingSpec.Cover template WingRecords.InvRevGe_1_10.index 11 mv := by
  unfold WingSpec.Cover
  intro rs size n j hn hj hr s args X Y W L P sub τ hτ hrel hdoor z hz
  have size' : rs.length=2 := by simpa [CatalogRanks.profileBanks] using size
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
  obtain ⟨G,Leq,-⟩ := WingModel.good_at_size (t:=template) (size' ▸ WingBounds.InvRevGe_1_10.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.InvRevGe_1_10.records⟩
    (fun g hx hy => WingChart.InvRevGe_1_10.simple g hx hy) SepData.InvRevGe_1_10.cert (WingFill.InvRevGe_1_10.filled_eq size' n j hn hj hr)
  simp only [L] at hz sub
  rw [Leq] at hz sub
  have m := WingModel.model_at_size (t:=template) (size' ▸ WingBounds.InvRevGe_1_10.certificate) n j hn hj hr sizes verified
  have one : RegisterTable.atomVal (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 0=1 := rfl
  have hJ := WingModel.args_unit hn0 hj hr 0
  have hJ' : (0:ℝ)≤(getRat args 1:ℝ) ∧ (getRat args 1:ℝ)≤1 := ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  -- channel 0: bank 1
  have hQ0 := WingModel.args_unit hn0 hj hr 1
  have hQ0' : (0:ℝ)≤(getRat args 2:ℝ) ∧ (getRat args 2:ℝ)≤1 := ⟨by exact_mod_cast hQ0.1,by exact_mod_cast hQ0.2⟩
  set b0 : ℝ := ((((1:ℕ):ℝ)-1/5)/1001+5/2002*(getRat args 2:ℝ)+40/1001*(getRat args 1:ℝ)*sr : ℝ) with hb0_def
  obtain ⟨hwy_0,-,-,-,-,bLow_0,-,-,-,-,-,hdl_0,hdr_0⟩ := CopyRange.InvRevGe_1_10.ranges0 m rfl hJ hQ0
  obtain ⟨hwx_0,hrb_0,L1_0,L2_0,-,H43_0,CW0_0,CW1_0⟩ := CopyRange.InvRevGe_1_10.rangesX0 m rfl hJ hQ0
  have hb0 : 0≤b0 ∧ b0≤((509:ℝ)/130130) := by
    simp only [b0]; constructor
    · nlinarith [mul_nonneg hJ'.1 hsr.le]
    · nlinarith [mul_le_mul hJ'.2 hsr1 hsr.le zero_le_one]
  have hbase0 : WingSpec.base 11 args τ 0=(sr/320+b0*(50050/sr^2)+τ 0,1-50050/sr^2) := by
    simp [WingSpec.base,CatalogRanks.profileBanks,gs,b0,sr]
  have hdoor0 := hdoor 0 (by simp [CatalogRanks.profileBanks])
  rw [hbase0] at hdoor0
  have ht0 := hτ 0 (by simp [CatalogRanks.profileBanks])
  have inc00 := CopyInc.InvRevGe_1_10.lower0 m
  have hY0 : Y.getD 36 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 580 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 36]; rfl
  have ex0 : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 45]; rfl
  have ey0 : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 1]; rfl
  have hrr0 : ((96/5:ℝ) + (1/100100:ℝ)*sr^2)=(X.getD 45 0-301/2)/(1-Y.getD 1 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex0,ey0,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have inc0 : sr/320-b0*(Y.getD 36 0-1)=X.getD 44 0-((X.getD 45 0-X.getD 44 0)/(1-Y.getD 1 0))*(Y.getD 36 0-1) := by
    rw [hwx_0,hY0,←hrr0]; exact inc00
  have hbr0 : b0≤(X.getD 45 0-X.getD 44 0)/(1-Y.getD 1 0) :=
    WingSpec.slope_le inc0 (by linarith [H43_0]) (by rw [hwx_0]; linarith)
  replace bLow_0 : 0<(1:ℝ)*(Y.getD 39 0)+(-1:ℝ)*(1-50050/sr^2) := bLow_0
  have lo0 : 1-50050/sr^2<Y.getD 39 0 := by linarith [bLow_0]
  have mt0 := CopyMatch.InvRevGe_1_10.upper0 m rfl (ne_of_gt lo0)
    (ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide) (by decide : 1<38))) (τ 0)
  -- channel 1: bank 10
  have hQ1 := WingModel.args_unit hn0 hj hr 2
  have hQ1' : (0:ℝ)≤(getRat args 3:ℝ) ∧ (getRat args 3:ℝ)≤1 := ⟨by exact_mod_cast hQ1.1,by exact_mod_cast hQ1.2⟩
  set b1 : ℝ := ((((10:ℕ):ℝ)-1/5)/1001+5/2002*(getRat args 3:ℝ)+40/1001*(getRat args 1:ℝ)*sr : ℝ) with hb1_def
  obtain ⟨hwx_1,hwy_1,hrb_1,L1_1,L2_1,-,H43_1⟩ := CopyRange.InvRevGe_1_10.ranges1 m rfl hJ hQ1
  obtain ⟨-,-,-,-,bLow_1,-,-,-,-,-,hdl_1,hdr_1,CW0_1,CW1_1⟩ := CopyRange.InvRevGe_1_10.rangesX1 m rfl hJ hQ1
  have hb1 : 0≤b1 ∧ b1≤((1679:ℝ)/130130) := by
    simp only [b1]; constructor
    · nlinarith [mul_nonneg hJ'.1 hsr.le]
    · nlinarith [mul_le_mul hJ'.2 hsr1 hsr.le zero_le_one]
  have hbase1 : WingSpec.base 11 args τ 1=(sr/320+b1*(50050/sr^2)+τ 1,1-50050/sr^2) := by
    simp [WingSpec.base,CatalogRanks.profileBanks,gs,b1,sr]
  have hdoor1 := hdoor 1 (by simp [CatalogRanks.profileBanks])
  rw [hbase1] at hdoor1
  have ht1 := hτ 1 (by simp [CatalogRanks.profileBanks])
  have inc10 := CopyInc.InvRevGe_1_10.lower1 m
  have hY1 : Y.getD 18 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 369 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 18]; rfl
  have ex1 : X.getD 51 0=((((axisOf template false).coordsQ (getRat args 0)).getD 8 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 51]; rfl
  have ey1 : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 1]; rfl
  have hrr1 : ((20:ℝ) + (-1/25025:ℝ)*sr^2 + (1/2004002000:ℝ)*sr^4)=(X.getD 51 0-301/2)/(1-Y.getD 1 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex1,ey1,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have inc1 : sr/320-b1*(Y.getD 18 0-1)=X.getD 44 0-((X.getD 51 0-X.getD 44 0)/(1-Y.getD 1 0))*(Y.getD 18 0-1) := by
    rw [hwx_1,hY1,←hrr1]; exact inc10
  have hbr1 : b1≤(X.getD 51 0-X.getD 44 0)/(1-Y.getD 1 0) :=
    WingSpec.slope_le inc1 (by linarith [H43_1]) (by rw [hwx_1]; linarith)
  replace bLow_1 : 0<(1:ℝ)*(Y.getD 21 0)+(-1:ℝ)*(1-50050/sr^2) := bLow_1
  have lo1 : 1-50050/sr^2<Y.getD 21 0 := by linarith [bLow_1]
  have mt1 := CopyMatch.InvRevGe_1_10.upper1 m rfl (ne_of_gt lo1)
    (ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide) (by decide : 1<20))) (τ 1)
  have hdl : X.getD 32 0=0 := by rw [hdl_0]; norm_num
  have hwy : Y.getD 12 0=1 := by rw [hwy_0]; norm_num
  have rel : 1≤(τ 0+1/2)*(5/2-(τ 1+1/2)) := by
    simpa [CatalogLogic.relation,CatalogRanks.profileBanks,List.range_succ,DerivedAlgebra.InvRevGe] using hrel
  have gA : WingCover.InvRevGe_1_10.gd X Y (τ 0) (τ 1) 8=RoomRelation.InvRevGe.guard sr 0 (τ 0) := by
    rw [show WingCover.InvRevGe_1_10.gd X Y (τ 0) (τ 1) 8=CopyLower.receiver X Y (45,1) (46,1) (τ 0) by simp [WingCover.InvRevGe_1_10.gd]]
    exact WingSpec.receiver_slot (ra:=(45,1)) (rb:=(46,1)) CopyLocal.InvRevGe_1_10.records size' hn hj hr (m:=0) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl (τ 0)
  have gB : WingCover.InvRevGe_1_10.gd X Y (τ 0) (τ 1) 9=RoomRelation.InvRevGe.guard sr 1 (τ 1) := by
    rw [show WingCover.InvRevGe_1_10.gd X Y (τ 0) (τ 1) 9=CopyLower.receiver X Y (51,1) (52,1) (τ 1) by simp [WingCover.InvRevGe_1_10.gd]]
    exact WingSpec.receiver_slot (ra:=(51,1)) (rb:=(52,1)) CopyLocal.InvRevGe_1_10.records size' hn hj hr (m:=1) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl (τ 1)
  have cAx : X.getD 50 0=497/2 := by
    have e : X.getD 50 0=((((axisOf template false).coordsQ (getRat args 0)).getD 7 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 50]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have cAy : Y.getD 6 0=((-23:ℝ)/6) := by
    have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl true 6]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have cBx : X.getD 53 0=501/2-sr^4/400800400 := by
    have e : X.getD 53 0=((((axisOf template false).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 53]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have cBy : Y.getD 8 0=((-11:ℝ)/3) := by
    have e : Y.getD 8 0=((((axisOf template true).coordsQ (getRat args 0)).getD 8 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl true 8]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have cax : X.getD 55 0=501/2 := by
    have e : X.getD 55 0=((((axisOf template false).coordsQ (getRat args 0)).getD 12 0 : ℚ) : ℝ) := by
      rw [CopyMatch.grid_ref m rfl false 55]; rfl
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [e,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    try norm_num
    try ring
  have key := WingCover.InvRevGe_1_10.cover_of G one sub
    (hD := rfl) (hW := rfl) (hdl := hdl)
    (hdr := hdr_0) (hwy := hwy)
    (hb0 := hb0) (ht0 := ht0) (hdoor0 := hdoor0) (hrb0 := hrb_0) (L1_0 := L1_0)
    (L2_0 := L2_0) (inc0 := inc0) (hbr0 := hbr0) (mt0 := mt0) (lo0 := lo0)
    (CW0_0 := CW0_0) (CW1_0 := CW1_0)
    (hb1 := hb1) (ht1 := ht1) (hdoor1 := hdoor1) (hrb1 := hrb_1) (L1_1 := L1_1)
    (L2_1 := L2_1) (inc1 := inc1) (hbr1 := hbr1) (mt1 := mt1) (lo1 := lo1)
    (CW0_1 := CW0_1) (CW1_1 := CW1_1)
    (gA := gA) (gB := gB) (rel := rel) (cAx := cAx) (cAy := cAy) (cBx := cBx) (cBy := cBy) (cax := cax)
    hz
  have hg : ∀ r, WingCover.InvRevGe_1_10.gd X Y (τ 0) (τ 1) r=WingSpec.guardOf X Y mv τ (WingRecords.InvRevGe_1_10.index).2 r := by
    intro r
    by_cases h8 : r=8
    · subst h8; simp [WingCover.InvRevGe_1_10.gd,WingSpec.guardOf,mv,List.lookup]
    by_cases h9 : r=9
    · subst h9; simp [WingCover.InvRevGe_1_10.gd,WingSpec.guardOf,mv,List.lookup]
    have e8 : (r == 8)=false := by simpa using h8
    have e9 : (r == 9)=false := by simpa using h9
    simp [WingCover.InvRevGe_1_10.gd,WingSpec.guardOf,mv,List.lookup,h8,e8,h9,e9]
  rcases key with ⟨r,hr,h⟩|h|h
  · exact Or.inl ⟨r,hr,by rw [← hg]; exact h⟩
  · exact Or.inr ⟨0,by simp [CatalogRanks.profileBanks],by rw [hbase0]; exact h⟩
  · exact Or.inr ⟨1,by simp [CatalogRanks.profileBanks],by rw [hbase1]; exact h⟩

end ArtGallery.Orthogonal.BoundaryPoint.WingFinal.InvRevGe_1_10
end
