module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_200_1000.Base

/-! A nook copy test of profile `Lower_10_200_1000` in the local frame of a wing (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_200_1000
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.Lower_10_200_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0


/-! ## Channel 1, chamber test -/

def u1es : List (Option CellRoles.CellEx) := [
  some (.cross 144 true [(.zlit 1 (1,0,1,0) 13 70 15 68 26 52,.zlit 1 (0,0,0,0) 43 68 13 70 26 52,.zlit 1 (1,0,1,0) 15 70 15 68 26 52,.zlit 1 (0,0,0,0) 43 68 15 70 26 52),(.zlit 1 (1,0,1,0) 13 70 15 68 26 53,.zlit 1 (0,0,0,0) 43 68 13 70 26 53,.zlit 1 (1,0,1,0) 15 70 15 68 26 53,.zlit 1 (0,0,0,0) 43 68 15 70 26 53),(.zlit 1 (1,0,1,0) 13 70 15 68 27 52,.zlit 1 (0,0,0,0) 43 68 13 70 27 52,.zlit 1 (1,0,1,0) 15 70 15 68 27 52,.zlit 1 (0,0,0,0) 43 68 15 70 27 52),(.zlit 1 (1,0,1,0) 13 70 15 68 27 53,.zlit 1 (0,0,0,0) 43 68 13 70 27 53,.zlit 1 (1,0,1,0) 15 70 15 68 27 53,.zlit 1 (0,0,0,0) 43 68 15 70 27 53)]),
  some (.half 133),
  some (.half 166),
  some (.half 163),
  some (.half 196),
  some (.cross 174 false [(.zlit 1 (0,0,0,0) 12 50 18 41 26 52,.zlit 2 (1,0,1,0) 30 50 26 52 18 41,.zlit 1 (0,0,0,0) 12 50 18 43 26 52,.zlit 2 (1,0,1,0) 30 50 26 52 18 43),(.zlit 1 (0,0,0,0) 12 50 18 41 26 53,.zlit 2 (1,0,1,0) 30 50 26 53 18 41,.zlit 1 (0,0,0,0) 12 50 18 43 26 53,.zlit 2 (1,0,1,0) 30 50 26 53 18 43),(.zlit 1 (0,0,0,0) 12 50 18 41 27 52,.zlit 2 (1,0,1,0) 30 50 27 52 18 41,.zlit 1 (0,0,0,0) 12 50 18 43 27 52,.zlit 2 (1,0,1,0) 30 50 27 52 18 43),(.zlit 1 (0,0,0,0) 12 50 18 41 27 53,.zlit 2 (1,0,1,0) 30 50 27 53 18 41,.zlit 1 (0,0,0,0) 12 50 18 43 27 53,.zlit 2 (1,0,1,0) 30 50 27 53 18 43)]),
  some (.cross 149 true [(.zlit 1 (1,0,1,0) 40 65 38 64 26 52,.zlit 1 (0,0,0,0) 38 57 40 65 26 52,.zlit 1 (1,0,1,0) 42 65 38 64 26 52,.zlit 1 (0,0,0,0) 38 57 42 65 26 52),(.zlit 1 (1,0,1,0) 40 65 38 64 26 53,.zlit 1 (0,0,0,0) 38 57 40 65 26 53,.zlit 1 (1,0,1,0) 42 65 38 64 26 53,.zlit 1 (0,0,0,0) 38 57 42 65 26 53),(.zlit 1 (1,0,1,0) 40 65 38 64 27 52,.zlit 1 (0,0,0,0) 38 57 40 65 27 52,.zlit 1 (1,0,1,0) 42 65 38 64 27 52,.zlit 1 (0,0,0,0) 38 57 42 65 27 52),(.zlit 1 (1,0,1,0) 40 65 38 64 27 53,.zlit 1 (0,0,0,0) 38 57 40 65 27 53,.zlit 1 (1,0,1,0) 42 65 38 64 27 53,.zlit 1 (0,0,0,0) 38 57 42 65 27 53)]),
  some (.half 176),
  some (.half 106),
  some (.half 123),
  some (.half 153),
  some (.cross 174 false [(.zlit 1 (0,0,0,0) 12 50 22 36 26 52,.zlit 2 (1,0,1,0) 30 50 26 52 22 36,.zlit 1 (0,0,0,0) 12 50 22 38 26 52,.zlit 2 (1,0,1,0) 30 50 26 52 22 38),(.zlit 1 (0,0,0,0) 12 50 22 36 26 53,.zlit 2 (1,0,1,0) 30 50 26 53 22 36,.zlit 1 (0,0,0,0) 12 50 22 38 26 53,.zlit 2 (1,0,1,0) 30 50 26 53 22 38),(.zlit 1 (0,0,0,0) 12 50 22 36 27 52,.zlit 2 (1,0,1,0) 30 50 27 52 22 36,.zlit 1 (0,0,0,0) 12 50 22 38 27 52,.zlit 2 (1,0,1,0) 30 50 27 52 22 38),(.zlit 1 (0,0,0,0) 12 50 22 36 27 53,.zlit 2 (1,0,1,0) 30 50 27 53 22 36,.zlit 1 (0,0,0,0) 12 50 22 38 27 53,.zlit 2 (1,0,1,0) 30 50 27 53 22 38)]),
  some (.half 72),
  some (.cross 67 true [(.zlit 1 (0,0,0,0) 87 16 85 25 26 52,.zlit 1 (0,0,0,0) 85 18 87 16 26 52,.zlit 1 (0,0,0,0) 87 18 85 25 26 52,.zlit 1 (0,0,0,0) 85 18 87 18 26 52),(.zlit 1 (0,0,0,0) 87 16 85 25 26 53,.zlit 1 (0,0,0,0) 85 18 87 16 26 53,.zlit 1 (0,0,0,0) 87 18 85 25 26 53,.zlit 1 (0,0,0,0) 85 18 87 18 26 53),(.zlit 1 (0,0,0,0) 87 16 85 25 27 52,.zlit 1 (0,0,0,0) 85 18 87 16 27 52,.zlit 1 (0,0,0,0) 87 18 85 25 27 52,.zlit 1 (0,0,0,0) 85 18 87 18 27 52),(.zlit 1 (0,0,0,0) 87 16 85 25 27 53,.zlit 1 (0,0,0,0) 85 18 87 16 27 53,.zlit 1 (0,0,0,0) 87 18 85 25 27 53,.zlit 1 (0,0,0,0) 85 18 87 18 27 53)]),
  some (.cross 36 false [(.zlit 1 (0,0,0,0) 65 4 75 0 26 52,.zlit 1 (0,0,0,0) 75 0 70 4 26 52,.zlit 1 (0,0,0,0) 65 4 77 0 26 52,.zlit 1 (0,0,0,0) 77 0 70 4 26 52),(.zlit 1 (0,0,0,0) 65 4 75 0 26 53,.zlit 1 (0,0,0,0) 75 0 70 4 26 53,.zlit 1 (0,0,0,0) 65 4 77 0 26 53,.zlit 1 (0,0,0,0) 77 0 70 4 26 53),(.zlit 1 (0,0,0,0) 65 4 75 0 27 52,.zlit 1 (0,0,0,0) 75 0 70 4 27 52,.zlit 1 (0,0,0,0) 65 4 77 0 27 52,.zlit 1 (0,0,0,0) 77 0 70 4 27 52),(.zlit 1 (0,0,0,0) 65 4 75 0 27 53,.zlit 1 (0,0,0,0) 75 0 70 4 27 53,.zlit 1 (0,0,0,0) 65 4 77 0 27 53,.zlit 1 (0,0,0,0) 77 0 70 4 27 53)]),
  some (.cross 24 false [(.zlit 1 (0,0,0,0) 55 20 63 6 26 52,.zlit 1 (0,0,0,0) 63 6 56 20 26 52,.zlit 1 (0,0,0,0) 55 20 64 6 26 52,.zlit 1 (0,0,0,0) 64 6 56 20 26 52),(.zlit 1 (0,0,0,0) 55 20 63 6 26 53,.zlit 1 (0,0,0,0) 63 6 56 20 26 53,.zlit 1 (0,0,0,0) 55 20 64 6 26 53,.zlit 1 (0,0,0,0) 64 6 56 20 26 53),(.zlit 1 (0,0,0,0) 55 20 63 6 27 52,.zlit 1 (0,0,0,0) 63 6 56 20 27 52,.zlit 1 (0,0,0,0) 55 20 64 6 27 52,.zlit 1 (0,0,0,0) 64 6 56 20 27 52),(.zlit 1 (0,0,0,0) 55 20 63 6 27 53,.zlit 1 (0,0,0,0) 63 6 56 20 27 53,.zlit 1 (0,0,0,0) 55 20 64 6 27 53,.zlit 1 (0,0,0,0) 64 6 56 20 27 53)]),
  some (.cross 61 true [(.zlit 1 (0,0,0,0) 94 8 88 25 26 52,.zlit 1 (0,0,0,0) 88 15 94 8 26 52,.zlit 1 (0,0,0,0) 95 8 88 25 26 52,.zlit 1 (0,0,0,0) 88 15 95 8 26 52),(.zlit 1 (0,0,0,0) 94 8 88 25 26 53,.zlit 1 (0,0,0,0) 88 15 94 8 26 53,.zlit 1 (0,0,0,0) 95 8 88 25 26 53,.zlit 1 (0,0,0,0) 88 15 95 8 26 53),(.zlit 1 (0,0,0,0) 94 8 88 25 27 52,.zlit 1 (0,0,0,0) 88 15 94 8 27 52,.zlit 1 (0,0,0,0) 95 8 88 25 27 52,.zlit 1 (0,0,0,0) 88 15 95 8 27 52),(.zlit 1 (0,0,0,0) 94 8 88 25 27 53,.zlit 1 (0,0,0,0) 88 15 94 8 27 53,.zlit 1 (0,0,0,0) 95 8 88 25 27 53,.zlit 1 (0,0,0,0) 88 15 95 8 27 53)]),
  none,
  some (.cross 101 true [(.zlit 1 (0,0,0,0) 71 2 61 25 26 52,.zlit 1 (0,0,0,0) 61 23 71 2 26 52,.zlit 1 (0,0,0,0) 72 2 61 25 26 52,.zlit 1 (0,0,0,0) 61 23 72 2 26 52),(.zlit 1 (0,0,0,0) 71 2 61 25 26 53,.zlit 1 (0,0,0,0) 61 23 71 2 26 53,.zlit 1 (0,0,0,0) 72 2 61 25 26 53,.zlit 1 (0,0,0,0) 61 23 72 2 26 53),(.zlit 1 (0,0,0,0) 71 2 61 25 27 52,.zlit 1 (0,0,0,0) 61 23 71 2 27 52,.zlit 1 (0,0,0,0) 72 2 61 25 27 52,.zlit 1 (0,0,0,0) 61 23 72 2 27 52),(.zlit 1 (0,0,0,0) 71 2 61 25 27 53,.zlit 1 (0,0,0,0) 61 23 71 2 27 53,.zlit 1 (0,0,0,0) 72 2 61 25 27 53,.zlit 1 (0,0,0,0) 61 23 72 2 27 53)])]

theorem u1tile : inTile C.tiles (54,106)=true := by (try rw [C_lit]); decide +kernel

theorem u1rcert : crossOne C (67,4) (68,4) (54,106) 154 true true [(.zlit 2 (1,0,1,0) 35 49 26 52 67 4,.zlit 2 (1,0,1,0) 35 49 26 52 68 4),(.zlit 2 (1,0,1,0) 35 49 26 53 67 4,.zlit 2 (1,0,1,0) 35 49 26 53 68 4),(.zlit 2 (1,0,1,0) 35 49 27 52 67 4,.zlit 2 (1,0,1,0) 35 49 27 52 68 4),(.zlit 2 (1,0,1,0) 35 49 27 53 67 4,.zlit 2 (1,0,1,0) 35 49 27 53 68 4)]=true := by (try rw [C_lit]); decide +kernel

theorem u1hc : (if true then C.next 154 else C.node 154)=(33,49) := by (try rw [C_lit]); decide +kernel

theorem u1bcert : crossOne C (50,20) (51,20) (54,106) 174 false true [(.zlit 1 (0,0,0,0) 12 50 50 20 26 52,.zlit 1 (0,0,0,0) 12 50 51 20 26 52),(.zlit 1 (0,0,0,0) 12 50 50 20 26 53,.zlit 1 (0,0,0,0) 12 50 51 20 26 53),(.zlit 1 (0,0,0,0) 12 50 50 20 27 52,.zlit 1 (0,0,0,0) 12 50 51 20 27 52),(.zlit 1 (0,0,0,0) 12 50 50 20 27 53,.zlit 1 (0,0,0,0) 12 50 51 20 27 53)]=true := by (try rw [C_lit]); decide +kernel

theorem u1bc : (if true then C.next 174 else C.node 174)=(30,50) := by (try rw [C_lit]); decide +kernel

theorem u1all0 : allOK C (54,106) 17 (0) ((WingRecords.Lower_10_200_1000.index).2.take 1) (u1es.take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all1 : allOK C (54,106) 17 (0+1) (((WingRecords.Lower_10_200_1000.index).2.drop 1).take 1) ((u1es.drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all2 : allOK C (54,106) 17 (0+1+1) ((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).take 1) (((u1es.drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all3 : allOK C (54,106) 17 (0+1+1+1) (((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).take 1) ((((u1es.drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all4 : allOK C (54,106) 17 (0+1+1+1+1) ((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).take 1) (((((u1es.drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all5 : allOK C (54,106) 17 (0+1+1+1+1+1) (((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all6 : allOK C (54,106) 17 (0+1+1+1+1+1+1) ((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all7 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1) (((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all8 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1) ((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all9 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1) (((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all10 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1) ((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all11 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all12 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all13 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all14 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all15 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all16 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all17 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all18 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all19 : allOK C (54,106) 17 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) (((((((((((((((((((u1es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1)=true := by (try rw [C_lit]); decide +kernel

theorem u1all : allOK C (54,106) 17 0 (WingRecords.Lower_10_200_1000.index).2 u1es=true :=
  (allOK_split 1 (0) _ _ u1all0 (allOK_split 1 (0+1) _ _ u1all1 (allOK_split 1 (0+1+1) _ _ u1all2 (allOK_split 1 (0+1+1+1) _ _ u1all3 (allOK_split 1 (0+1+1+1+1) _ _ u1all4 (allOK_split 1 (0+1+1+1+1+1) _ _ u1all5 (allOK_split 1 (0+1+1+1+1+1+1) _ _ u1all6 (allOK_split 1 (0+1+1+1+1+1+1+1) _ _ u1all7 (allOK_split 1 (0+1+1+1+1+1+1+1+1) _ _ u1all8 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1) _ _ u1all9 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1) _ _ u1all10 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all11 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all12 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all13 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all14 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all15 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all16 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all17 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u1all18 u1all19)))))))))))))))))))

theorem u1inner : Inner C.nx 54 ∧ Inner C.ny 106 := by (try rw [C_lit]); decide +kernel


/-- The chamber test of channel 1 in the local frame of the wing: `tR ≤ tB`. -/
theorem upper1 : CopySpec.Test template WingRecords.Lower_10_200_1000.index 3 3 200 (67,4) (68,4) 17 true := by
  unfold CopySpec.Test
  intro rs size n j hn hj hr s args X Y sr J Q b D W L P rest fill closed contact Gs cover tB tR Bg htB htR hBase hR owned
  show tR≤tB
  simp only [L] at fill contact hR owned hBase
  have hn0 : 0<n := by omega
  have hsr : (0:ℝ)<sr := by
    simp only [sr,s]; have : (0:ℚ)<n := by exact_mod_cast hn0
    exact_mod_cast (show (0:ℚ)<1/n by positivity)
  obtain ⟨G,Leq,-⟩ := WingModel.good_at_size (t:=template) (size ▸ WingBounds.Lower_10_200_1000.certificate) n j hn hj hr
    ⟨sizes,verified,x_ok,y_ok,WingRecords.Lower_10_200_1000.records⟩
    (fun g hx hy => WingChart.Lower_10_200_1000.simple g hx hy) SepData.Lower_10_200_1000.cert (WingFill.Lower_10_200_1000.filled_eq size n j hn hj hr)
  rw [Leq] at fill contact hR owned hBase
  have m := WingModel.model_at_size (t:=template) (size ▸ WingBounds.Lower_10_200_1000.certificate) n j hn hj hr sizes verified
  obtain ⟨hwy,Ua0,Ua1,Ub0,Ub1,bLow,H43u,DL0,DL1,DR0,DR1,hdl,hdr⟩ := CopyRange.Lower_10_200_1000.ranges1 m rfl
    (WingModel.args_unit hn0 hj hr 0) (WingModel.args_unit hn0 hj hr 2)
  replace bLow : 0<(1:ℝ)*(Y.getD 50 0)+(-1:ℝ)*(1-50050/sr^2) := bLow
  have hy1 : 1<Y.getD 52 0 := by
    rw [show (1:ℝ)=Y.getD 20 0 from (hwy.trans (by norm_num)).symm]
    exact SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide +kernel) (by decide)
  have blockB : ∀ x y : ℝ, X.getD 26 0<x → x<X.getD 27 0 → Y.getD 52 0<y → y<Y.getD 53 0 →
      x<lineX (W+b*D+tB,1-D) (gridPt X Y (30,50)) y → ¬P.Sees Bg (x,y) := by
    intro x y h0 h1 y0 y1 left
    have ax := CopyChannel.atom_between G.hx (by rw [WingModel.grid_length]; decide +kernel) h0 h1
    have ay := CopyChannel.atom_between G.hy (by rw [WingModel.grid_length]; decide +kernel) y0 y1
    rcases hBase with ⟨rfl,hB⟩|blind
    · exact CopyChannel.base_blocked_upper G fill closed contact (by positivity) u1tile
        (by simp only [gridPt]; rw [hdl,hwy]; norm_num) (by simp only [gridPt]; rw [hdr,hwy]; exact Prod.ext rfl (by norm_num))
        u1bcert (congrArg (gridPt X Y) u1bc) hB (by show 1-50050/sr^2<Y.getD 50 0; linarith) ax ay (by linarith) left
    · exact blind _ (CopyChannel.tile_filled G u1tile (z:=(x,y)) ax ay)
  have hB : Y.getD 50 0≠1-50050/sr^2 := by intro e; rw [e] at bLow; linarith
  have hR' : Y.getD 49 0≠Y.getD 4 0 := ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide +kernel)
    (by decide : 4<49))
  have matched := CopyMatch.Lower_10_200_1000.upper1 m rfl hB hR'
  exact CopyRoles.upper_chart2 (xc:=26) (iy:=52) (win:=(61,20)) (cBn:=(30,50)) G fill closed contact (by positivity) cover (by rw [WingModel.grid_length]; decide +kernel)
    (by rw [WingModel.grid_length]; decide +kernel) u1tile u1rcert u1hc u1all u1inner (hwy.trans (by norm_num)) rfl
    (by decide) (by decide) (by decide) (by rw [WingModel.grid_length]; decide +kernel) (div_pos (by norm_num) (pow_pos hsr 2))
    htB htR hR bLow blockB matched Ua0 Ua1 Ub0 Ub1 H43u DL0 DL1 DR0 DR1 owned


end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_200_1000
end
