module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvLe_40_200.Base

/-! A nook copy test of profile `InvLe_40_200` in the local frame of a wing (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvLe_40_200
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.InvLe_40_200
set_option maxRecDepth 200000
set_option maxHeartbeats 0


/-! ## Channel 0: receiver role 0, bank 40 -/

def c0es : List (Option CellHalf.CellExL) := [
  some (.full (.cross 106 true [(.zlit 1 (0,1,1,0) 8 42 10 40 29 37,.zlit 1 (0,1,0,1) 25 40 8 42 29 37,.zlit 1 (0,1,1,0) 10 42 10 40 29 37,.zlit 1 (0,1,0,1) 25 40 10 42 29 37),(.zlit 1 (0,1,1,0) 8 42 10 40 29 38,.zlit 1 (0,1,0,1) 25 40 8 42 29 38,.zlit 1 (0,1,1,0) 10 42 10 40 29 38,.zlit 1 (0,1,0,1) 25 40 10 42 29 38),(.zlit 1 (0,1,1,0) 8 42 10 40 30 37,.zlit 1 (0,1,0,1) 25 40 8 42 30 37,.zlit 1 (0,1,1,0) 10 42 10 40 30 37,.zlit 1 (0,1,0,1) 25 40 10 42 30 37),(.zlit 1 (0,1,1,0) 8 42 10 40 30 38,.zlit 1 (0,1,0,1) 25 40 8 42 30 38,.zlit 1 (0,1,1,0) 10 42 10 40 30 38,.zlit 1 (0,1,0,1) 25 40 10 42 30 38)])),
  some (.full (.cross 86 false [(.zlit 1 (0,1,0,1) 30 39 26 47 29 37,.zlit 1 (1,0,0,1) 26 47 28 39 29 37,.zlit 1 (0,1,0,1) 30 39 26 49 29 37,.zlit 1 (1,0,0,1) 26 49 28 39 29 37),(.zlit 1 (0,1,0,1) 30 39 26 47 29 38,.zlit 1 (1,0,0,1) 26 47 28 39 29 38,.zlit 1 (0,1,0,1) 30 39 26 49 29 38,.zlit 1 (1,0,0,1) 26 49 28 39 29 38),(.zlit 1 (1,1,0,2) 30 39 26 47 30 37,.zlit 1 (1,0,0,1) 26 47 28 39 30 37,.zlit 1 (1,1,0,2) 30 39 26 49 30 37,.zlit 1 (1,0,0,1) 26 49 28 39 30 37),(.zlit 1 (1,1,0,2) 30 39 26 47 30 38,.zlit 1 (1,0,0,1) 26 47 28 39 30 38,.zlit 1 (1,1,0,2) 30 39 26 49 30 38,.zlit 1 (1,0,0,1) 26 49 28 39 30 38)])),
  some (.full (.half 128)),
  some (.full (.cross 121 true [(.zlit 1 (1,0,1,0) 13 31 15 33 29 37,.zlit 1 (0,0,0,0) 15 34 13 31 29 37,.zlit 1 (1,0,1,0) 13 33 15 33 29 37,.zlit 1 (0,0,0,0) 15 34 13 33 29 37),(.zlit 1 (1,0,1,0) 13 31 15 33 29 38,.zlit 1 (0,0,0,0) 15 34 13 31 29 38,.zlit 1 (1,0,1,0) 13 33 15 33 29 38,.zlit 1 (0,0,0,0) 15 34 13 33 29 38),(.zlit 1 (1,0,1,0) 13 31 15 33 30 37,.zlit 1 (0,0,0,0) 15 34 13 31 30 37,.zlit 1 (1,0,1,0) 13 33 15 33 30 37,.zlit 1 (0,0,0,0) 15 34 13 33 30 37),(.zlit 1 (1,0,1,0) 13 31 15 33 30 38,.zlit 1 (0,0,0,0) 15 34 13 31 30 38,.zlit 1 (1,0,1,0) 13 33 15 33 30 38,.zlit 1 (0,0,0,0) 15 34 13 33 30 38)])),
  some (.full (.half 108)),
  some (.full (.half 72)),
  some (.full (.half 85)),
  some (.full (.cross 112 true [(.zlit 0 (0,0,0,0) 29 37 17 26 21 29,.zlit 1 (1,0,1,0) 18 29 17 26 29 37,.zlit 0 (0,0,0,0) 29 37 17 28 21 29,.zlit 1 (1,0,1,0) 18 29 17 28 29 37),(.zlit 0 (0,0,0,0) 29 38 17 26 21 29,.zlit 1 (1,0,1,0) 18 29 17 26 29 38,.zlit 0 (0,0,0,0) 29 38 17 28 21 29,.zlit 1 (1,0,1,0) 18 29 17 28 29 38),(.zlit 0 (0,0,0,0) 30 37 17 26 21 29,.zlit 1 (1,0,1,0) 18 29 17 26 30 37,.zlit 0 (0,0,0,0) 30 37 17 28 21 29,.zlit 1 (1,0,1,0) 18 29 17 28 30 37),(.zlit 0 (0,0,0,0) 30 38 17 26 21 29,.zlit 1 (1,0,1,0) 18 29 17 26 30 38,.zlit 0 (0,0,0,0) 30 38 17 28 21 29,.zlit 1 (1,0,1,0) 18 29 17 28 30 38)])),
  none,
  some (.full (.cross 68 true [(.zlit 1 (0,0,0,0) 55 1 45 16 29 37,.zlit 1 (0,0,0,0) 41 16 55 1 29 37,.zlit 1 (0,0,0,0) 56 1 45 16 29 37,.zlit 1 (0,0,0,0) 41 16 56 1 29 37),(.zlit 1 (0,0,0,0) 55 1 45 16 29 38,.zlit 1 (0,0,0,0) 41 16 55 1 29 38,.zlit 1 (0,0,0,0) 56 1 45 16 29 38,.zlit 1 (0,0,0,0) 41 16 56 1 29 38),(.zlit 1 (0,0,0,0) 55 1 45 16 30 37,.zlit 1 (0,0,0,0) 41 16 55 1 30 37,.zlit 1 (0,0,0,0) 56 1 45 16 30 37,.zlit 1 (0,0,0,0) 41 16 56 1 30 37),(.zlit 1 (0,0,0,0) 55 1 45 16 30 38,.zlit 1 (0,0,0,0) 41 16 55 1 30 38,.zlit 1 (0,0,0,0) 56 1 45 16 30 38,.zlit 1 (0,0,0,0) 41 16 56 1 30 38)])),
  some (.full (.half 61)),
  some (.full (.half 46))]

theorem c0tile : inTile C.tiles (60,76)=true := by (try rw [C_lit]); decide +kernel

theorem c0rcert : crossOne C (45,1) (46,1) (60,76) 24 false true [(.zlit 1 (0,0,0,0) 40 13 45 1 29 37,.zlit 1 (0,0,0,0) 40 13 46 1 29 37),(.zlit 1 (0,0,0,0) 40 13 45 1 29 38,.zlit 1 (0,0,0,0) 40 13 46 1 29 38),(.zlit 1 (0,0,0,0) 40 13 45 1 30 37,.zlit 1 (0,0,0,0) 40 13 46 1 30 37),(.zlit 1 (0,0,0,0) 40 13 45 1 30 38,.zlit 1 (0,0,0,0) 40 13 46 1 30 38)]=true := by (try rw [C_lit]); decide +kernel

theorem c0hu : (if true then C.next 24 else C.node 24)=(44,13) := by (try rw [C_lit]); decide +kernel

theorem c0all0 : CellHalf.allOKL C 29 37 8 (0) ((WingRecords.InvLe_40_200.index).2.take 1) (c0es.take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all1 : CellHalf.allOKL C 29 37 8 (0+1) (((WingRecords.InvLe_40_200.index).2.drop 1).take 1) ((c0es.drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all2 : CellHalf.allOKL C 29 37 8 (0+1+1) ((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).take 1) (((c0es.drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all3 : CellHalf.allOKL C 29 37 8 (0+1+1+1) (((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).take 1) ((((c0es.drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all4 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1) ((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).take 1) (((((c0es.drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all5 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1) (((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all6 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1+1) ((((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all7 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1+1+1) (((((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all8 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1+1+1+1) ((((((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all9 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1+1+1+1+1) (((((((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all10 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1+1+1+1+1+1) ((((((((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all11 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all12 : CellHalf.allOKL C 29 37 8 (0+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.InvLe_40_200.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) ((((((((((((c0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1)=true := by (try rw [C_lit]); decide +kernel

theorem c0all : CellHalf.allOKL C 29 37 8 0 (WingRecords.InvLe_40_200.index).2 c0es=true :=
  (CellHalf.allOKL_split 1 (0) _ _ c0all0 (CellHalf.allOKL_split 1 (0+1) _ _ c0all1 (CellHalf.allOKL_split 1 (0+1+1) _ _ c0all2 (CellHalf.allOKL_split 1 (0+1+1+1) _ _ c0all3 (CellHalf.allOKL_split 1 (0+1+1+1+1) _ _ c0all4 (CellHalf.allOKL_split 1 (0+1+1+1+1+1) _ _ c0all5 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1) _ _ c0all6 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1) _ _ c0all7 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1) _ _ c0all8 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1) _ _ c0all9 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1) _ _ c0all10 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1) _ _ c0all11 c0all12))))))))))))

theorem c0inner : Inner C.nx 60 ∧ Inner C.ny 76 := by (try rw [C_lit]); decide +kernel


/-- The nook test of channel 0 in the local frame of the wing: `tB ≤ tR`. -/
theorem lower0 : CopySpec.Test template WingRecords.InvLe_40_200.index 2 2 40 (45,1) (46,1) 8 false := by
  unfold CopySpec.Test
  intro rs size n j hn hj hr s args X Y sr J Q b D W L P rest fill closed contact Gs cover tB tR Bg htB htR hBase hR owned
  show tB≤tR
  simp only [L] at fill contact hR owned hBase
  have hn0 : 0<n := by omega
  have hsr : (0:ℝ)<sr := by
    simp only [sr,s]; have : (0:ℚ)<n := by exact_mod_cast hn0
    exact_mod_cast (show (0:ℚ)<1/n by positivity)
  obtain ⟨G,Leq,-⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.InvLe_40_200.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.InvLe_40_200.records⟩
    (fun g hx hy => WingChart.InvLe_40_200.simple g hx hy) SepData.InvLe_40_200.cert (WingFill.InvLe_40_200.filled_eq size n j hn hj hr)
  rw [Leq] at fill contact hR owned hBase
  have m := WingModel.model_at_size (t:=template) (size ▸ WingBounds.InvLe_40_200.certificate) n j hn hj hr sizes verified
  have blockB : ∀ x y : ℝ, X.getD 29 0<x → x<X.getD 30 0 → Y.getD 37 0<y → y<Y.getD 38 0 →
      W-(b+tB/D)*(y-1)<x → ¬P.Sees Bg (x,y) := by
    intro x y h0 h1 y0 y1 right
    have zL := CopyChannel.tile_filled G c0tile (z:=(x,y))
      (CopyChannel.atom_between G.hx (by rw [WingModel.grid_length]; decide +kernel) h0 h1)
      (CopyChannel.atom_between G.hy (by rw [WingModel.grid_length]; decide +kernel) y0 y1)
    rcases hBase with ⟨rfl,hB⟩|blind
    · exact CopyChannel.base_blocked fill closed contact (by positivity) (div_pos (by norm_num) (pow_pos hsr 2)) hB zL right
    · exact blind _ zL
  obtain ⟨hwx,hwy,hrb,L1,L2,deep,H43⟩ := CopyRange.InvLe_40_200.ranges0 m rfl (WingModel.args_unit hn0 hj hr 0)
    (WingModel.args_unit hn0 hj hr 1)
  have inc := CopyInc.InvLe_40_200.lower0 m
  have hY : Y.getD 37 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 579 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 37]; rfl
  have ex : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 45]; rfl
  have ey : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 1]; rfl
  have hrr : ((96/5:ℝ) + (1/100100:ℝ)*sr^2)=(X.getD 45 0-301/2)/(1-Y.getD 1 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex,ey,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have hsr1 : sr≤1/65 := by
    have h65 : (65:ℝ)≤n := by exact_mod_cast hn
    have e : sr=1/(n:ℝ) := by simp only [sr,s]; push_cast; ring
    rw [e]; exact one_div_le_one_div_of_le (by norm_num) h65
  exact CopyRoles.lower_chart2 (xc:=29) (iy:=37) G fill closed contact (by positivity) (by simp only [W]; linarith) cover
    (by rw [WingModel.grid_length]; decide +kernel)
    (by rw [WingModel.grid_length]; decide +kernel) c0tile c0rcert c0hu c0all c0inner hwx (hwy.trans (by norm_num))
    rfl (by decide) (by decide) (div_pos (by norm_num) (pow_pos hsr 2)) hrb deep L1 L2 H43
    (by rw [hY,←hrr]; exact inc) htB htR blockB hR owned


end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.InvLe_40_200
end
