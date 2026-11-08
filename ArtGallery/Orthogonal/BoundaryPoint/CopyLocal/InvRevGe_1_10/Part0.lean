module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10.Base

/-! A nook copy test of profile `InvRevGe_1_10` in the local frame of a wing (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.InvRevGe_1_10
set_option maxRecDepth 200000
set_option maxHeartbeats 0


/-! ## Channel 1: receiver role 1, bank 10 -/

def c1es : List (Option CellHalf.CellExL) := [
  some (.full (.cross 94 true [(.zlit 1 (1,0,1,0) 8 41 10 39 16 18,.zlit 1 (0,0,0,0) 25 39 8 41 16 18,.zlit 1 (1,0,1,0) 10 41 10 39 16 18,.zlit 1 (0,0,0,0) 25 39 10 41 16 18),(.zlit 1 (1,0,1,0) 8 41 10 39 16 19,.zlit 1 (0,0,0,0) 25 39 8 41 16 19,.zlit 1 (1,0,1,0) 10 41 10 39 16 19,.zlit 1 (0,0,0,0) 25 39 10 41 16 19),(.zlit 1 (1,0,1,0) 8 41 10 39 17 18,.zlit 1 (0,0,0,0) 25 39 8 41 17 18,.zlit 1 (1,0,1,0) 10 41 10 39 17 18,.zlit 1 (0,0,0,0) 25 39 10 41 17 18),(.zlit 1 (1,0,1,0) 8 41 10 39 17 19,.zlit 1 (0,0,0,0) 25 39 8 41 17 19,.zlit 1 (1,0,1,0) 10 41 10 39 17 19,.zlit 1 (0,0,0,0) 25 39 10 41 17 19)])),
  some (.full (.half 83)),
  some (.full (.cross 124 true [(.zlit 1 (0,1,1,0) 5 23 7 21 16 18,.zlit 1 (0,1,0,1) 12 21 5 23 16 18,.zlit 1 (0,1,1,0) 7 23 7 21 16 18,.zlit 1 (0,1,0,1) 12 21 7 23 16 18),(.zlit 1 (0,1,1,0) 5 23 7 21 16 19,.zlit 1 (0,1,0,1) 12 21 5 23 16 19,.zlit 1 (0,1,1,0) 7 23 7 21 16 19,.zlit 1 (0,1,0,1) 12 21 7 23 16 19),(.zlit 1 (0,1,1,0) 5 23 7 21 17 18,.zlit 1 (0,1,0,1) 12 21 5 23 17 18,.zlit 1 (0,1,1,0) 7 23 7 21 17 18,.zlit 1 (0,1,0,1) 12 21 7 23 17 18),(.zlit 1 (0,1,1,0) 5 23 7 21 17 19,.zlit 1 (0,1,0,1) 12 21 5 23 17 19,.zlit 1 (0,1,1,0) 7 23 7 21 17 19,.zlit 1 (0,1,0,1) 12 21 7 23 17 19)])),
  some (.full (.cross 104 false [(.zlit 1 (0,1,0,1) 17 20 13 30 16 18,.zlit 1 (1,0,0,1) 13 30 15 20 16 18,.zlit 1 (0,1,0,1) 17 20 13 32 16 18,.zlit 1 (1,0,0,1) 13 32 15 20 16 18),(.zlit 1 (0,1,0,1) 17 20 13 30 16 19,.zlit 1 (1,0,0,1) 13 30 15 20 16 19,.zlit 1 (0,1,0,1) 17 20 13 32 16 19,.zlit 1 (1,0,0,1) 13 32 15 20 16 19),(.zlit 1 (1,1,0,2) 17 20 13 30 17 18,.zlit 1 (1,0,0,1) 13 30 15 20 17 18,.zlit 1 (1,1,0,2) 17 20 13 32 17 18,.zlit 1 (1,0,0,1) 13 32 15 20 17 18),(.zlit 1 (1,1,0,2) 17 20 13 30 17 19,.zlit 1 (1,0,0,1) 13 30 15 20 17 19,.zlit 1 (1,1,0,2) 17 20 13 32 17 19,.zlit 1 (1,0,0,1) 13 32 15 20 17 19)])),
  some (.full (.cross 99 true [(.zlit 1 (1,0,1,0) 22 36 21 35 16 18,.zlit 0 (0,0,0,0) 16 18 21 28 22 36,.zlit 1 (1,0,1,0) 24 36 21 35 16 18,.zlit 0 (0,0,0,0) 16 18 21 28 24 36),(.zlit 1 (1,0,1,0) 22 36 21 35 16 19,.zlit 0 (0,0,0,0) 16 19 21 28 22 36,.zlit 1 (1,0,1,0) 24 36 21 35 16 19,.zlit 0 (0,0,0,0) 16 19 21 28 24 36),(.zlit 1 (1,0,1,0) 22 36 21 35 17 18,.zlit 0 (0,0,0,0) 17 18 21 28 22 36,.zlit 1 (1,0,1,0) 24 36 21 35 17 18,.zlit 0 (0,0,0,0) 17 18 21 28 24 36),(.zlit 1 (1,0,1,0) 22 36 21 35 17 19,.zlit 0 (0,0,0,0) 17 19 21 28 22 36,.zlit 1 (1,0,1,0) 24 36 21 35 17 19,.zlit 0 (0,0,0,0) 17 19 21 28 24 36)])),
  some (.full (.half 60)),
  some (.full (.half 73)),
  some (.full (.half 103)),
  some (.full (.cross 10 false [(.zlit 1 (0,0,0,0) 37 12 45 1 16 18,.zlit 1 (0,0,0,0) 45 1 38 12 16 18,.zlit 1 (0,0,0,0) 37 12 46 1 16 18,.zlit 1 (0,0,0,0) 46 1 38 12 16 18),(.zlit 1 (0,0,0,0) 37 12 45 1 16 19,.zlit 1 (0,0,0,0) 45 1 38 12 16 19,.zlit 1 (0,0,0,0) 37 12 46 1 16 19,.zlit 1 (0,0,0,0) 46 1 38 12 16 19),(.zlit 1 (0,0,0,0) 37 12 45 1 17 18,.zlit 1 (0,0,0,0) 45 1 38 12 17 18,.zlit 1 (0,0,0,0) 37 12 46 1 17 18,.zlit 1 (0,0,0,0) 46 1 38 12 17 18),(.zlit 1 (0,0,0,0) 37 12 45 1 17 19,.zlit 1 (0,0,0,0) 45 1 38 12 17 19,.zlit 1 (0,0,0,0) 37 12 46 1 17 19,.zlit 1 (0,0,0,0) 46 1 38 12 17 19)])),
  none,
  some (.full (.half 27)),
  some (.full (.half 42))]

theorem c1tile : inTile C.tiles (34,38)=true := by (try rw [C_lit]); decide +kernel

theorem c1rcert : crossOne C (51,1) (52,1) (34,38) 14 false true [(.zlit 1 (0,0,0,0) 40 12 51 1 16 18,.zlit 1 (0,0,0,0) 40 12 52 1 16 18),(.zlit 1 (0,0,0,0) 40 12 51 1 16 19,.zlit 1 (0,0,0,0) 40 12 52 1 16 19),(.zlit 1 (0,0,0,0) 40 12 51 1 17 18,.zlit 1 (0,0,0,0) 40 12 52 1 17 18),(.zlit 1 (0,0,0,0) 40 12 51 1 17 19,.zlit 1 (0,0,0,0) 40 12 52 1 17 19)]=true := by (try rw [C_lit]); decide +kernel

theorem c1hu : (if true then C.next 14 else C.node 14)=(44,12) := by (try rw [C_lit]); decide +kernel

theorem c1all0 : CellHalf.allOKL C 16 18 9 (0) ((WingRecords.InvRevGe_1_10.index).2.take 1) (c1es.take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all1 : CellHalf.allOKL C 16 18 9 (0+1) (((WingRecords.InvRevGe_1_10.index).2.drop 1).take 1) ((c1es.drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all2 : CellHalf.allOKL C 16 18 9 (0+1+1) ((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).take 1) (((c1es.drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all3 : CellHalf.allOKL C 16 18 9 (0+1+1+1) (((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).take 1) ((((c1es.drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all4 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1) ((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).take 1) (((((c1es.drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all5 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1) (((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all6 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1+1) ((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all7 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1+1+1) (((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all8 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1+1+1+1) ((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all9 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1+1+1+1+1) (((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all10 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1+1+1+1+1+1) ((((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all11 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all12 : CellHalf.allOKL C 16 18 9 (0+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.InvRevGe_1_10.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) ((((((((((((c1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1)=true := by (try rw [C_lit]); decide +kernel

theorem c1all : CellHalf.allOKL C 16 18 9 0 (WingRecords.InvRevGe_1_10.index).2 c1es=true :=
  (CellHalf.allOKL_split 1 (0) _ _ c1all0 (CellHalf.allOKL_split 1 (0+1) _ _ c1all1 (CellHalf.allOKL_split 1 (0+1+1) _ _ c1all2 (CellHalf.allOKL_split 1 (0+1+1+1) _ _ c1all3 (CellHalf.allOKL_split 1 (0+1+1+1+1) _ _ c1all4 (CellHalf.allOKL_split 1 (0+1+1+1+1+1) _ _ c1all5 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1) _ _ c1all6 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1) _ _ c1all7 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1) _ _ c1all8 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1) _ _ c1all9 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1) _ _ c1all10 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1) _ _ c1all11 c1all12))))))))))))

theorem c1inner : Inner C.nx 34 ∧ Inner C.ny 38 := by (try rw [C_lit]); decide +kernel


/-- The nook test of channel 1 in the local frame of the wing: `tB ≤ tR`. -/
theorem lower1 : CopySpec.Test template WingRecords.InvRevGe_1_10.index 2 3 10 (51,1) (52,1) 9 false := by
  unfold CopySpec.Test
  intro rs size n j hn hj hr s args X Y sr J Q b D W L P rest fill closed contact Gs cover tB tR Bg htB htR hBase hR owned
  show tB≤tR
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
  have blockB : ∀ x y : ℝ, X.getD 16 0<x → x<X.getD 17 0 → Y.getD 18 0<y → y<Y.getD 19 0 →
      W-(b+tB/D)*(y-1)<x → ¬P.Sees Bg (x,y) := by
    intro x y h0 h1 y0 y1 right
    have zL := CopyChannel.tile_filled G c1tile (z:=(x,y))
      (CopyChannel.atom_between G.hx (by rw [WingModel.grid_length]; decide +kernel) h0 h1)
      (CopyChannel.atom_between G.hy (by rw [WingModel.grid_length]; decide +kernel) y0 y1)
    rcases hBase with ⟨rfl,hB⟩|blind
    · exact CopyChannel.base_blocked fill closed contact (by positivity) (div_pos (by norm_num) (pow_pos hsr 2)) hB zL right
    · exact blind _ zL
  obtain ⟨hwx,hwy,hrb,L1,L2,deep,H43⟩ := CopyRange.InvRevGe_1_10.ranges1 m rfl (WingModel.args_unit hn0 hj hr 0)
    (WingModel.args_unit hn0 hj hr 2)
  have inc := CopyInc.InvRevGe_1_10.lower1 m
  have hY : Y.getD 18 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 369 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 18]; rfl
  have ex : X.getD 51 0=((((axisOf template false).coordsQ (getRat args 0)).getD 8 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 51]; rfl
  have ey : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 1]; rfl
  have hrr : ((20:ℝ) + (-1/25025:ℝ)*sr^2 + (1/2004002000:ℝ)*sr^4)=(X.getD 51 0-301/2)/(1-Y.getD 1 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex,ey,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have hsr1 : sr≤1/65 := by
    have h65 : (65:ℝ)≤n := by exact_mod_cast hn
    have e : sr=1/(n:ℝ) := by simp only [sr,s]; push_cast; ring
    rw [e]; exact one_div_le_one_div_of_le (by norm_num) h65
  exact CopyRoles.lower_chart2 (xc:=16) (iy:=18) G fill closed contact (by positivity) (by simp only [W]; linarith) cover
    (by rw [WingModel.grid_length]; decide +kernel)
    (by rw [WingModel.grid_length]; decide +kernel) c1tile c1rcert c1hu c1all c1inner hwx (hwy.trans (by norm_num))
    rfl (by decide) (by decide) (div_pos (by norm_num) (pow_pos hsr 2)) hrb deep L1 L2 H43
    (by rw [hY,←hrr]; exact inc) htB htR blockB hR owned


end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvRevGe_1_10
end
