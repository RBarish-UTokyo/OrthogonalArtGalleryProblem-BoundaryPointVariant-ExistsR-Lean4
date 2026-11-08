module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_40_200_1000.Base

/-! A nook copy test of profile `Lower_40_200_1000` in the local frame of a wing (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_40_200_1000
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.Lower_40_200_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0


/-! ## Channel 2: receiver role 6, bank 1000 -/

def c2es : List (Option CellHalf.CellExL) := [
  some (.full (.cross 144 true [(.zlit 1 (1,0,1,0) 13 70 15 68 21 29,.zlit 1 (0,0,0,0) 43 68 13 70 21 29,.zlit 1 (1,0,1,0) 15 70 15 68 21 29,.zlit 1 (0,0,0,0) 43 68 15 70 21 29),(.zlit 1 (1,0,1,0) 13 70 15 68 21 30,.zlit 1 (0,0,0,0) 43 68 13 70 21 30,.zlit 1 (1,0,1,0) 15 70 15 68 21 30,.zlit 1 (0,0,0,0) 43 68 15 70 21 30),(.zlit 1 (1,0,1,0) 13 70 15 68 22 29,.zlit 1 (0,0,0,0) 43 68 13 70 22 29,.zlit 1 (1,0,1,0) 15 70 15 68 22 29,.zlit 1 (0,0,0,0) 43 68 15 70 22 29),(.zlit 1 (1,0,1,0) 13 70 15 68 22 30,.zlit 1 (0,0,0,0) 43 68 13 70 22 30,.zlit 1 (1,0,1,0) 15 70 15 68 22 30,.zlit 1 (0,0,0,0) 43 68 15 70 22 30)])),
  some (.full (.half 133)),
  some (.full (.cross 6 true [(.zlit 1 (0,0,0,0) 10 52 9 32 21 29,.zlit 1 (0,1,0,1) 17 32 10 52 21 29,.zlit 1 (0,0,0,0) 12 52 9 32 21 29,.zlit 1 (0,1,0,1) 17 32 12 52 21 29),(.zlit 1 (0,0,0,0) 10 52 9 32 21 30,.zlit 1 (0,1,0,1) 17 32 10 52 21 30,.zlit 1 (0,0,0,0) 12 52 9 32 21 30,.zlit 1 (0,1,0,1) 17 32 12 52 21 30),(.zlit 1 (0,0,0,0) 10 52 9 32 22 29,.zlit 1 (0,1,0,1) 17 32 10 52 22 29,.zlit 1 (0,0,0,0) 12 52 9 32 22 29,.zlit 1 (0,1,0,1) 17 32 12 52 22 29),(.zlit 1 (0,0,0,0) 10 52 9 32 22 30,.zlit 1 (0,1,0,1) 17 32 10 52 22 30,.zlit 1 (0,0,0,0) 12 52 9 32 22 30,.zlit 1 (0,1,0,1) 17 32 12 52 22 30)])),
  some (.full (.half 163)),
  some (.full (.cross 6 true [(.zlit 1 (0,1,1,0) 7 34 9 32 21 29,.zlit 1 (0,1,0,1) 17 32 7 34 21 29,.zlit 1 (0,1,1,0) 9 34 9 32 21 29,.zlit 1 (0,1,0,1) 17 32 9 34 21 29),(.zlit 1 (0,1,1,0) 7 34 9 32 21 30,.zlit 1 (0,1,0,1) 17 32 7 34 21 30,.zlit 1 (0,1,1,0) 9 34 9 32 21 30,.zlit 1 (0,1,0,1) 17 32 9 34 21 30),(.zlit 1 (0,1,1,0) 7 34 9 32 22 29,.zlit 1 (0,1,0,1) 17 32 7 34 22 29,.zlit 1 (0,1,1,0) 9 34 9 32 22 29,.zlit 1 (0,1,0,1) 17 32 9 34 22 29),(.zlit 1 (0,1,1,0) 7 34 9 32 22 30,.zlit 1 (0,1,0,1) 17 32 7 34 22 30,.zlit 1 (0,1,1,0) 9 34 9 32 22 30,.zlit 1 (0,1,0,1) 17 32 9 34 22 30)])),
  some (.full (.cross 184 false [(.zlit 1 (0,1,0,1) 22 31 18 41 21 29,.zlit 1 (1,0,0,1) 18 41 20 31 21 29,.zlit 1 (0,1,0,1) 22 31 18 43 21 29,.zlit 1 (1,0,0,1) 18 43 20 31 21 29),(.zlit 1 (0,1,0,1) 22 31 18 41 21 30,.zlit 1 (1,0,0,1) 18 41 20 31 21 30,.zlit 1 (0,1,0,1) 22 31 18 43 21 30,.zlit 1 (1,0,0,1) 18 43 20 31 21 30),(.zlit 1 (1,1,0,2) 22 31 18 41 22 29,.zlit 1 (1,0,0,1) 18 41 20 31 22 29,.zlit 1 (1,1,0,2) 22 31 18 43 22 29,.zlit 1 (1,0,0,1) 18 43 20 31 22 29),(.zlit 1 (1,1,0,2) 22 31 18 41 22 30,.zlit 1 (1,0,0,1) 18 41 20 31 22 30,.zlit 1 (1,1,0,2) 22 31 18 43 22 30,.zlit 1 (1,0,0,1) 18 43 20 31 22 30)])),
  some (.full (.cross 149 true [(.zlit 1 (1,0,1,0) 40 65 38 64 21 29,.zlit 1 (0,0,0,0) 38 57 40 65 21 29,.zlit 1 (1,0,1,0) 42 65 38 64 21 29,.zlit 1 (0,0,0,0) 38 57 42 65 21 29),(.zlit 1 (1,0,1,0) 40 65 38 64 21 30,.zlit 1 (0,0,0,0) 38 57 40 65 21 30,.zlit 1 (1,0,1,0) 42 65 38 64 21 30,.zlit 1 (0,0,0,0) 38 57 42 65 21 30),(.zlit 1 (1,0,1,0) 40 65 38 64 22 29,.zlit 1 (0,0,0,0) 38 57 40 65 22 29,.zlit 1 (1,0,1,0) 42 65 38 64 22 29,.zlit 1 (0,0,0,0) 38 57 42 65 22 29),(.zlit 1 (1,0,1,0) 40 65 38 64 22 30,.zlit 1 (0,0,0,0) 38 57 40 65 22 30,.zlit 1 (1,0,1,0) 42 65 38 64 22 30,.zlit 1 (0,0,0,0) 38 57 42 65 22 30)])),
  some (.full (.cross 179 true [(.zlit 1 (1,0,1,0) 27 47 25 46 21 29,.zlit 1 (0,0,0,0) 25 39 27 47 21 29,.zlit 1 (1,0,1,0) 29 47 25 46 21 29,.zlit 1 (0,0,0,0) 25 39 29 47 21 29),(.zlit 1 (1,0,1,0) 27 47 25 46 21 30,.zlit 1 (0,0,0,0) 25 39 27 47 21 30,.zlit 1 (1,0,1,0) 29 47 25 46 21 30,.zlit 1 (0,0,0,0) 25 39 29 47 21 30),(.zlit 1 (1,0,1,0) 27 47 25 46 22 29,.zlit 1 (0,0,0,0) 25 39 27 47 22 29,.zlit 1 (1,0,1,0) 29 47 25 46 22 29,.zlit 1 (0,0,0,0) 25 39 29 47 22 29),(.zlit 1 (1,0,1,0) 27 47 25 46 22 30,.zlit 1 (0,0,0,0) 25 39 27 47 22 30,.zlit 1 (1,0,1,0) 29 47 25 46 22 30,.zlit 1 (0,0,0,0) 25 39 29 47 22 30)])),
  some (.full (.half 106)),
  some (.full (.half 123)),
  some (.full (.half 153)),
  some (.full (.half 183)),
  some (.full (.half 72)),
  some (.full (.cross 67 true [(.zlit 1 (0,0,0,0) 87 16 85 25 21 29,.zlit 1 (0,0,0,0) 85 18 87 16 21 29,.zlit 1 (0,0,0,0) 87 18 85 25 21 29,.zlit 1 (0,0,0,0) 85 18 87 18 21 29),(.zlit 1 (0,0,0,0) 87 16 85 25 21 30,.zlit 1 (0,0,0,0) 85 18 87 16 21 30,.zlit 1 (0,0,0,0) 87 18 85 25 21 30,.zlit 1 (0,0,0,0) 85 18 87 18 21 30),(.zlit 1 (0,0,0,0) 87 16 85 25 22 29,.zlit 1 (0,0,0,0) 85 18 87 16 22 29,.zlit 1 (0,0,0,0) 87 18 85 25 22 29,.zlit 1 (0,0,0,0) 85 18 87 18 22 29),(.zlit 1 (0,0,0,0) 87 16 85 25 22 30,.zlit 1 (0,0,0,0) 85 18 87 16 22 30,.zlit 1 (0,0,0,0) 87 18 85 25 22 30,.zlit 1 (0,0,0,0) 85 18 87 18 22 30)])),
  some (.full (.cross 24 false [(.zlit 1 (0,0,0,0) 55 20 75 0 21 29,.zlit 1 (0,0,0,0) 75 0 56 20 21 29,.zlit 1 (0,0,0,0) 55 20 77 0 21 29,.zlit 1 (0,0,0,0) 77 0 56 20 21 29),(.zlit 1 (0,0,0,0) 55 20 75 0 21 30,.zlit 1 (0,0,0,0) 75 0 56 20 21 30,.zlit 1 (0,0,0,0) 55 20 77 0 21 30,.zlit 1 (0,0,0,0) 77 0 56 20 21 30),(.zlit 1 (0,0,0,0) 55 20 75 0 22 29,.zlit 1 (0,0,0,0) 75 0 56 20 22 29,.zlit 1 (0,0,0,0) 55 20 77 0 22 29,.zlit 1 (0,0,0,0) 77 0 56 20 22 29),(.zlit 1 (0,0,0,0) 55 20 75 0 22 30,.zlit 1 (0,0,0,0) 75 0 56 20 22 30,.zlit 1 (0,0,0,0) 55 20 77 0 22 30,.zlit 1 (0,0,0,0) 77 0 56 20 22 30)])),
  some (.full (.cross 22 false [(.zlit 1 (0,0,0,0) 51 22 63 6 21 29,.zlit 1 (0,0,0,0) 63 6 55 22 21 29,.zlit 1 (0,0,0,0) 51 22 64 6 21 29,.zlit 1 (0,0,0,0) 64 6 55 22 21 29),(.zlit 1 (0,0,0,0) 51 22 63 6 21 30,.zlit 1 (0,0,0,0) 63 6 55 22 21 30,.zlit 1 (0,0,0,0) 51 22 64 6 21 30,.zlit 1 (0,0,0,0) 64 6 55 22 21 30),(.zlit 1 (0,0,0,0) 51 22 63 6 22 29,.zlit 1 (0,0,0,0) 63 6 55 22 22 29,.zlit 1 (0,0,0,0) 51 22 64 6 22 29,.zlit 1 (0,0,0,0) 64 6 55 22 22 29),(.zlit 1 (0,0,0,0) 51 22 63 6 22 30,.zlit 1 (0,0,0,0) 63 6 55 22 22 30,.zlit 1 (0,0,0,0) 51 22 64 6 22 30,.zlit 1 (0,0,0,0) 64 6 55 22 22 30)])),
  some (.full (.cross 61 true [(.zlit 1 (0,0,0,0) 94 8 88 25 21 29,.zlit 1 (0,0,0,0) 88 15 94 8 21 29,.zlit 1 (0,0,0,0) 95 8 88 25 21 29,.zlit 1 (0,0,0,0) 88 15 95 8 21 29),(.zlit 1 (0,0,0,0) 94 8 88 25 21 30,.zlit 1 (0,0,0,0) 88 15 94 8 21 30,.zlit 1 (0,0,0,0) 95 8 88 25 21 30,.zlit 1 (0,0,0,0) 88 15 95 8 21 30),(.zlit 1 (0,0,0,0) 94 8 88 25 22 29,.zlit 1 (0,0,0,0) 88 15 94 8 22 29,.zlit 1 (0,0,0,0) 95 8 88 25 22 29,.zlit 1 (0,0,0,0) 88 15 95 8 22 29),(.zlit 1 (0,0,0,0) 94 8 88 25 22 30,.zlit 1 (0,0,0,0) 88 15 94 8 22 30,.zlit 1 (0,0,0,0) 95 8 88 25 22 30,.zlit 1 (0,0,0,0) 88 15 95 8 22 30)])),
  some (.full (.cross 24 false [(.zlit 1 (0,0,0,0) 55 20 67 4 21 29,.zlit 1 (0,0,0,0) 67 4 56 20 21 29,.zlit 1 (0,0,0,0) 55 20 68 4 21 29,.zlit 1 (0,0,0,0) 68 4 56 20 21 29),(.zlit 1 (0,0,0,0) 55 20 67 4 21 30,.zlit 1 (0,0,0,0) 67 4 56 20 21 30,.zlit 1 (0,0,0,0) 55 20 68 4 21 30,.zlit 1 (0,0,0,0) 68 4 56 20 21 30),(.zlit 1 (0,0,0,0) 55 20 67 4 22 29,.zlit 1 (0,0,0,0) 67 4 56 20 22 29,.zlit 1 (0,0,0,0) 55 20 68 4 22 29,.zlit 1 (0,0,0,0) 68 4 56 20 22 29),(.zlit 1 (0,0,0,0) 55 20 67 4 22 30,.zlit 1 (0,0,0,0) 67 4 56 20 22 30,.zlit 1 (0,0,0,0) 55 20 68 4 22 30,.zlit 1 (0,0,0,0) 68 4 56 20 22 30)])),
  none]

theorem c2tile : inTile C.tiles (44,60)=true := by (try rw [C_lit]); decide +kernel

theorem c2rcert : crossOne C (71,2) (72,2) (44,60) 28 false true [(.zlit 1 (0,0,0,0) 58 20 71 2 21 29,.zlit 1 (0,0,0,0) 58 20 72 2 21 29),(.zlit 1 (0,0,0,0) 58 20 71 2 21 30,.zlit 1 (0,0,0,0) 58 20 72 2 21 30),(.zlit 1 (0,0,0,0) 58 20 71 2 22 29,.zlit 1 (0,0,0,0) 58 20 72 2 22 29),(.zlit 1 (0,0,0,0) 58 20 71 2 22 30,.zlit 1 (0,0,0,0) 58 20 72 2 22 30)]=true := by (try rw [C_lit]); decide +kernel

theorem c2hu : (if true then C.next 28 else C.node 28)=(61,20) := by (try rw [C_lit]); decide +kernel

theorem c2all0 : CellHalf.allOKL C 21 29 18 (0) ((WingRecords.Lower_40_200_1000.index).2.take 1) (c2es.take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all1 : CellHalf.allOKL C 21 29 18 (0+1) (((WingRecords.Lower_40_200_1000.index).2.drop 1).take 1) ((c2es.drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all2 : CellHalf.allOKL C 21 29 18 (0+1+1) ((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).take 1) (((c2es.drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all3 : CellHalf.allOKL C 21 29 18 (0+1+1+1) (((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).take 1) ((((c2es.drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all4 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1) ((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).take 1) (((((c2es.drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all5 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1) (((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all6 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1) ((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all7 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1) (((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all8 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1) ((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all9 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1) (((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all10 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1) ((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all11 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all12 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all13 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all14 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all15 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all16 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all17 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all18 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all19 : CellHalf.allOKL C 21 29 18 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((((WingRecords.Lower_40_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) (((((((((((((((((((c2es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1)=true := by (try rw [C_lit]); decide +kernel

theorem c2all : CellHalf.allOKL C 21 29 18 0 (WingRecords.Lower_40_200_1000.index).2 c2es=true :=
  (CellHalf.allOKL_split 1 (0) _ _ c2all0 (CellHalf.allOKL_split 1 (0+1) _ _ c2all1 (CellHalf.allOKL_split 1 (0+1+1) _ _ c2all2 (CellHalf.allOKL_split 1 (0+1+1+1) _ _ c2all3 (CellHalf.allOKL_split 1 (0+1+1+1+1) _ _ c2all4 (CellHalf.allOKL_split 1 (0+1+1+1+1+1) _ _ c2all5 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1) _ _ c2all6 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1) _ _ c2all7 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1) _ _ c2all8 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1) _ _ c2all9 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1) _ _ c2all10 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all11 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all12 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all13 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all14 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all15 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all16 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all17 (CellHalf.allOKL_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ c2all18 c2all19)))))))))))))))))))

theorem c2inner : Inner C.nx 44 ∧ Inner C.ny 60 := by (try rw [C_lit]); decide +kernel


/-- The nook test of channel 2 in the local frame of the wing: `tB ≤ tR`. -/
theorem lower2 : CopySpec.Test template WingRecords.Lower_40_200_1000.index 3 4 1000 (71,2) (72,2) 18 false := by
  unfold CopySpec.Test
  intro rs size n j hn hj hr s args X Y sr J Q b D W L P rest fill closed contact Gs cover tB tR Bg htB htR hBase hR owned
  show tB≤tR
  simp only [L] at fill contact hR owned hBase
  have hn0 : 0<n := by omega
  have hsr : (0:ℝ)<sr := by
    simp only [sr,s]; have : (0:ℚ)<n := by exact_mod_cast hn0
    exact_mod_cast (show (0:ℚ)<1/n by positivity)
  obtain ⟨G,Leq,-⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.Lower_40_200_1000.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.Lower_40_200_1000.records⟩
    (fun g hx hy => WingChart.Lower_40_200_1000.simple g hx hy) SepData.Lower_40_200_1000.cert (WingFill.Lower_40_200_1000.filled_eq size n j hn hj hr)
  rw [Leq] at fill contact hR owned hBase
  have m := WingModel.model_at_size (t:=template) (size ▸ WingBounds.Lower_40_200_1000.certificate) n j hn hj hr sizes verified
  have blockB : ∀ x y : ℝ, X.getD 21 0<x → x<X.getD 22 0 → Y.getD 29 0<y → y<Y.getD 30 0 →
      W-(b+tB/D)*(y-1)<x → ¬P.Sees Bg (x,y) := by
    intro x y h0 h1 y0 y1 right
    have zL := CopyChannel.tile_filled G c2tile (z:=(x,y))
      (CopyChannel.atom_between G.hx (by rw [WingModel.grid_length]; decide +kernel) h0 h1)
      (CopyChannel.atom_between G.hy (by rw [WingModel.grid_length]; decide +kernel) y0 y1)
    rcases hBase with ⟨rfl,hB⟩|blind
    · exact CopyChannel.base_blocked fill closed contact (by positivity) (div_pos (by norm_num) (pow_pos hsr 2)) hB zL right
    · exact blind _ zL
  obtain ⟨hwx,hwy,hrb,L1,L2,deep,H43⟩ := CopyRange.Lower_40_200_1000.ranges2 m rfl (WingModel.args_unit hn0 hj hr 0)
    (WingModel.args_unit hn0 hj hr 3)
  have inc := CopyInc.Lower_40_200_1000.lower2 m
  have hY : Y.getD 29 0=((getRat (execRat args [] (template.corridor.baseRows++template.corridor.rest)) 525 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 29]; rfl
  have ex : X.getD 71 0=((((axisOf template false).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl false 71]; rfl
  have ey : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
    rw [CopyMatch.grid_ref m rfl true 2]; rfl
  have hrr : ((217/2:ℝ) + (3/100100:ℝ)*sr^2)=(X.getD 71 0-301/2)/(1-Y.getD 2 0) := by
    have e0 : ((getRat args 0 : ℚ) : ℝ)=sr := rfl
    rw [ex,ey,CopyMatch.level_cast,CopyMatch.level_cast,e0,CopyMatch.level_eq _ _ _ (by decide),
      CopyMatch.level_eq _ _ _ (by decide)]
    simp [axisOf,template,RoomFamily.Lower.xAxis,RoomFamily.Lower.yAxis,Gap.valR,evalR]
    field_simp
    ring
  have hsr1 : sr≤1/65 := by
    have h65 : (65:ℝ)≤n := by exact_mod_cast hn
    have e : sr=1/(n:ℝ) := by simp only [sr,s]; push_cast; ring
    rw [e]; exact one_div_le_one_div_of_le (by norm_num) h65
  exact CopyRoles.lower_chart2 (xc:=21) (iy:=29) G fill closed contact (by positivity) (by simp only [W]; linarith) cover
    (by rw [WingModel.grid_length]; decide +kernel)
    (by rw [WingModel.grid_length]; decide +kernel) c2tile c2rcert c2hu c2all c2inner hwx (hwy.trans (by norm_num))
    rfl (by decide) (by decide) (div_pos (by norm_num) (pow_pos hsr 2)) hrb deep L1 L2 H43
    (by rw [hY,←hrr]; exact inc) htB htR blockB hR owned


end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_40_200_1000
end
