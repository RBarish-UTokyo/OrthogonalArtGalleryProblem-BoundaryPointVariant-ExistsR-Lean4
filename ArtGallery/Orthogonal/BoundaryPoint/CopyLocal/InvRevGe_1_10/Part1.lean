module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10.Base

/-! A nook copy test of profile `InvRevGe_1_10` in the local frame of a wing (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.InvRevGe_1_10
set_option maxRecDepth 200000
set_option maxHeartbeats 0


/-! ## Channel 0, chamber test -/

def u0es : List (Option CellRoles.CellEx) := [
  some (.half 86),
  some (.half 83),
  some (.half 116),
  some (.cross 94 false [(.zlit 1 (0,0,0,0) 10 39 13 30 24 41,.zlit 2 (1,0,1,0) 25 39 24 41 13 30,.zlit 1 (0,0,0,0) 10 39 13 32 24 41,.zlit 2 (1,0,1,0) 25 39 24 41 13 32),(.zlit 1 (0,0,0,0) 10 39 13 30 24 42,.zlit 2 (1,0,1,0) 25 39 24 42 13 30,.zlit 1 (0,0,0,0) 10 39 13 32 24 42,.zlit 2 (1,0,1,0) 25 39 24 42 13 32),(.zlit 1 (0,0,0,0) 10 39 13 30 25 41,.zlit 2 (1,0,1,0) 25 39 25 41 13 30,.zlit 1 (0,0,0,0) 10 39 13 32 25 41,.zlit 2 (1,0,1,0) 25 39 25 41 13 32),(.zlit 1 (0,0,0,0) 10 39 13 30 25 42,.zlit 2 (1,0,1,0) 25 39 25 42 13 30,.zlit 1 (0,0,0,0) 10 39 13 32 25 42,.zlit 2 (1,0,1,0) 25 39 25 42 13 32)]),
  some (.half 96),
  some (.half 60),
  some (.half 73),
  some (.cross 94 false [(.zlit 1 (0,0,0,0) 10 39 17 25 24 41,.zlit 2 (1,0,1,0) 25 39 24 41 17 25,.zlit 1 (0,0,0,0) 10 39 17 27 24 41,.zlit 2 (1,0,1,0) 25 39 24 41 17 27),(.zlit 1 (0,0,0,0) 10 39 17 25 24 42,.zlit 2 (1,0,1,0) 25 39 24 42 17 25,.zlit 1 (0,0,0,0) 10 39 17 27 24 42,.zlit 2 (1,0,1,0) 25 39 24 42 17 27),(.zlit 1 (0,0,0,0) 10 39 17 25 25 41,.zlit 2 (1,0,1,0) 25 39 25 41 17 25,.zlit 1 (0,0,0,0) 10 39 17 27 25 41,.zlit 2 (1,0,1,0) 25 39 25 41 17 27),(.zlit 1 (0,0,0,0) 10 39 17 25 25 42,.zlit 2 (1,0,1,0) 25 39 25 42 17 25,.zlit 1 (0,0,0,0) 10 39 17 27 25 42,.zlit 2 (1,0,1,0) 25 39 25 42 17 27)]),
  none,
  some (.cross 56 true [(.zlit 1 (0,0,0,0) 51 1 45 15 24 41,.zlit 1 (0,0,0,0) 41 15 51 1 24 41,.zlit 1 (0,0,0,0) 52 1 45 15 24 41,.zlit 1 (0,0,0,0) 41 15 52 1 24 41),(.zlit 1 (0,0,0,0) 51 1 45 15 24 42,.zlit 1 (0,0,0,0) 41 15 51 1 24 42,.zlit 1 (0,0,0,0) 52 1 45 15 24 42,.zlit 1 (0,0,0,0) 41 15 52 1 24 42),(.zlit 1 (0,0,0,0) 51 1 45 15 25 41,.zlit 1 (0,0,0,0) 41 15 51 1 25 41,.zlit 1 (0,0,0,0) 52 1 45 15 25 41,.zlit 1 (0,0,0,0) 41 15 52 1 25 41),(.zlit 1 (0,0,0,0) 51 1 45 15 25 42,.zlit 1 (0,0,0,0) 41 15 51 1 25 42,.zlit 1 (0,0,0,0) 52 1 45 15 25 42,.zlit 1 (0,0,0,0) 41 15 52 1 25 42)]),
  some (.half 27),
  some (.half 42)]

theorem u0tile : inTile C.tiles (50,84)=true := by (try rw [C_lit]); decide +kernel

theorem u0rcert : crossOne C (45,1) (46,1) (50,84) 74 true true [(.zlit 2 (1,0,1,0) 30 38 24 41 45 1,.zlit 2 (1,0,1,0) 30 38 24 41 46 1),(.zlit 2 (1,0,1,0) 30 38 24 42 45 1,.zlit 2 (1,0,1,0) 30 38 24 42 46 1),(.zlit 2 (1,0,1,0) 30 38 25 41 45 1,.zlit 2 (1,0,1,0) 30 38 25 41 46 1),(.zlit 2 (1,0,1,0) 30 38 25 42 45 1,.zlit 2 (1,0,1,0) 30 38 25 42 46 1)]=true := by (try rw [C_lit]); decide +kernel

theorem u0hc : (if true then C.next 74 else C.node 74)=(28,38) := by (try rw [C_lit]); decide +kernel

theorem u0bcert : crossOne C (32,12) (33,12) (50,84) 94 false true [(.zlit 1 (0,0,0,0) 10 39 32 12 24 41,.zlit 1 (0,0,0,0) 10 39 33 12 24 41),(.zlit 1 (0,0,0,0) 10 39 32 12 24 42,.zlit 1 (0,0,0,0) 10 39 33 12 24 42),(.zlit 1 (0,0,0,0) 10 39 32 12 25 41,.zlit 1 (0,0,0,0) 10 39 33 12 25 41),(.zlit 1 (0,0,0,0) 10 39 32 12 25 42,.zlit 1 (0,0,0,0) 10 39 33 12 25 42)]=true := by (try rw [C_lit]); decide +kernel

theorem u0bc : (if true then C.next 94 else C.node 94)=(25,39) := by (try rw [C_lit]); decide +kernel

theorem u0all0 : allOK C (50,84) 8 (0) ((WingRecords.InvRevGe_1_10.index).2.take 1) (u0es.take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all1 : allOK C (50,84) 8 (0+1) (((WingRecords.InvRevGe_1_10.index).2.drop 1).take 1) ((u0es.drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all2 : allOK C (50,84) 8 (0+1+1) ((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).take 1) (((u0es.drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all3 : allOK C (50,84) 8 (0+1+1+1) (((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).take 1) ((((u0es.drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all4 : allOK C (50,84) 8 (0+1+1+1+1) ((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).take 1) (((((u0es.drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all5 : allOK C (50,84) 8 (0+1+1+1+1+1) (((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all6 : allOK C (50,84) 8 (0+1+1+1+1+1+1) ((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all7 : allOK C (50,84) 8 (0+1+1+1+1+1+1+1) (((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all8 : allOK C (50,84) 8 (0+1+1+1+1+1+1+1+1) ((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all9 : allOK C (50,84) 8 (0+1+1+1+1+1+1+1+1+1) (((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all10 : allOK C (50,84) 8 (0+1+1+1+1+1+1+1+1+1+1) ((((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all11 : allOK C (50,84) 8 (0+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all12 : allOK C (50,84) 8 (0+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) ((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all : allOK C (50,84) 8 0 (WingRecords.InvRevGe_1_10.index).2 u0es=true :=
  (allOK_split 1 (0) _ _ u0all0 (allOK_split 1 (0+1) _ _ u0all1 (allOK_split 1 (0+1+1) _ _ u0all2 (allOK_split 1 (0+1+1+1) _ _ u0all3 (allOK_split 1 (0+1+1+1+1) _ _ u0all4 (allOK_split 1 (0+1+1+1+1+1) _ _ u0all5 (allOK_split 1 (0+1+1+1+1+1+1) _ _ u0all6 (allOK_split 1 (0+1+1+1+1+1+1+1) _ _ u0all7 (allOK_split 1 (0+1+1+1+1+1+1+1+1) _ _ u0all8 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1) _ _ u0all9 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1) _ _ u0all10 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all11 u0all12))))))))))))

theorem u0inner : Inner C.nx 50 ∧ Inner C.ny 84 := by (try rw [C_lit]); decide +kernel


/-- The chamber test of channel 0 in the local frame of the wing: `tR ≤ tB`. -/
theorem upper0 : CopySpec.Test template WingRecords.InvRevGe_1_10.index 2 2 1 (45,1) (46,1) 8 true := by
  unfold CopySpec.Test
  intro rs size n j hn hj hr s args X Y sr J Q b D W L P rest fill closed contact Gs cover tB tR Bg htB htR hBase hR owned
  show tR≤tB
  simp only [L] at fill contact hR owned hBase
  have hn0 : 0<n := by omega
  have hsr : (0:ℝ)<sr := by
    simp only [sr,s]; have : (0:ℚ)<n := by exact_mod_cast hn0
    exact_mod_cast (show (0:ℚ)<1/n by positivity)
  obtain ⟨G,Leq,-⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.InvRevGe_1_10.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.InvRevGe_1_10.records⟩
    (fun g hx hy => WingChart.InvRevGe_1_10.simple g hx hy) SepData.InvRevGe_1_10.cert (WingFill.InvRevGe_1_10.filled_eq size n j hn hj hr)
  rw [Leq] at fill contact hR owned hBase
  have m := WingModel.model_at_size (t:=template) (size ▸ WingBounds.InvRevGe_1_10.certificate) n j hn hj hr sizes verified
  obtain ⟨hwy,Ua0,Ua1,Ub0,Ub1,bLow,H43u,DL0,DL1,DR0,DR1,hdl,hdr⟩ := CopyRange.InvRevGe_1_10.ranges0 m rfl
    (WingModel.args_unit hn0 hj hr 0) (WingModel.args_unit hn0 hj hr 1)
  replace bLow : 0<(1:ℝ)*(Y.getD 39 0)+(-1:ℝ)*(1-50050/sr^2) := bLow
  have hy1 : 1<Y.getD 41 0 := by
    rw [show (1:ℝ)=Y.getD 12 0 from (hwy.trans (by norm_num)).symm]
    exact SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide +kernel) (by decide)
  have blockB : ∀ x y : ℝ, X.getD 24 0<x → x<X.getD 25 0 → Y.getD 41 0<y → y<Y.getD 42 0 →
      x<lineX (W+b*D+tB,1-D) (gridPt X Y (25,39)) y → ¬P.Sees Bg (x,y) := by
    intro x y h0 h1 y0 y1 left
    have ax := CopyChannel.atom_between G.hx (by rw [WingModel.grid_length]; decide +kernel) h0 h1
    have ay := CopyChannel.atom_between G.hy (by rw [WingModel.grid_length]; decide +kernel) y0 y1
    rcases hBase with ⟨rfl,hB⟩|blind
    · exact CopyChannel.base_blocked_upper G fill closed contact (by positivity) u0tile
        (by simp only [gridPt]; rw [hdl,hwy]; norm_num) (by simp only [gridPt]; rw [hdr,hwy]; exact Prod.ext rfl (by norm_num))
        u0bcert (congrArg (gridPt X Y) u0bc) hB (by show 1-50050/sr^2<Y.getD 39 0; linarith) ax ay (by linarith) left
    · exact blind _ (CopyChannel.tile_filled G u0tile (z:=(x,y)) ax ay)
  have hB : Y.getD 39 0≠1-50050/sr^2 := by intro e; rw [e] at bLow; linarith
  have hR' : Y.getD 38 0≠Y.getD 1 0 := ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide +kernel)
    (by decide : 1<38))
  have matched := CopyMatch.InvRevGe_1_10.upper0 m rfl hB hR'
  exact CopyRoles.upper_chart2 (xc:=24) (iy:=41) (win:=(44,12)) (cBn:=(25,39)) G fill closed contact (by positivity) cover (by rw [WingModel.grid_length]; decide +kernel)
    (by rw [WingModel.grid_length]; decide +kernel) u0tile u0rcert u0hc u0all u0inner (hwy.trans (by norm_num)) rfl
    (by decide) (by decide) (by decide) (by rw [WingModel.grid_length]; decide +kernel) (div_pos (by norm_num) (pow_pos hsr 2))
    htB htR hR bLow blockB matched Ua0 Ua1 Ub0 Ub1 H43u DL0 DL1 DR0 DR1 owned


end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10
end
