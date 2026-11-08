module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_200_1000.Base

/-! A nook copy test of profile `Lower_10_200_1000` in the local frame of a wing (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_200_1000
open MarginCert RegisterTable RegisterOrder IndexedWing SepCert CellCert CellRoles CopyChannel SpanCells RoomCoordinates ArtGallery.Orthogonal.Hard
open WingOrder.Lower_10_200_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0


/-! ## Channel 0, chamber test -/

def u0es : List (Option CellRoles.CellEx) := [
  some (.half 136),
  some (.half 133),
  some (.half 166),
  some (.cross 144 false [(.zlit 1 (0,0,0,0) 15 68 31 59 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 31 59,.zlit 1 (0,0,0,0) 15 68 31 61 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 31 61),(.zlit 1 (0,0,0,0) 15 68 31 59 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 31 59,.zlit 1 (0,0,0,0) 15 68 31 61 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 31 61),(.zlit 1 (0,0,0,0) 15 68 31 59 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 31 59,.zlit 1 (0,0,0,0) 15 68 31 61 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 31 61),(.zlit 1 (0,0,0,0) 15 68 31 59 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 31 59,.zlit 1 (0,0,0,0) 15 68 31 61 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 31 61)]),
  some (.half 196),
  some (.cross 144 false [(.zlit 1 (0,0,0,0) 15 68 18 41 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 18 41,.zlit 1 (0,0,0,0) 15 68 18 43 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 18 43),(.zlit 1 (0,0,0,0) 15 68 18 41 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 18 41,.zlit 1 (0,0,0,0) 15 68 18 43 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 18 43),(.zlit 1 (0,0,0,0) 15 68 18 41 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 18 41,.zlit 1 (0,0,0,0) 15 68 18 43 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 18 43),(.zlit 1 (0,0,0,0) 15 68 18 41 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 18 41,.zlit 1 (0,0,0,0) 15 68 18 43 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 18 43)]),
  some (.half 146),
  some (.half 176),
  some (.half 106),
  some (.half 123),
  some (.cross 144 false [(.zlit 1 (0,0,0,0) 15 68 35 54 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 35 54,.zlit 1 (0,0,0,0) 15 68 35 56 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 35 56),(.zlit 1 (0,0,0,0) 15 68 35 54 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 35 54,.zlit 1 (0,0,0,0) 15 68 35 56 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 35 56),(.zlit 1 (0,0,0,0) 15 68 35 54 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 35 54,.zlit 1 (0,0,0,0) 15 68 35 56 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 35 56),(.zlit 1 (0,0,0,0) 15 68 35 54 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 35 54,.zlit 1 (0,0,0,0) 15 68 35 56 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 35 56)]),
  some (.cross 144 false [(.zlit 1 (0,0,0,0) 15 68 22 36 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 22 36,.zlit 1 (0,0,0,0) 15 68 22 38 42 70,.zlit 2 (1,0,1,0) 43 68 42 70 22 38),(.zlit 1 (0,0,0,0) 15 68 22 36 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 22 36,.zlit 1 (0,0,0,0) 15 68 22 38 42 71,.zlit 2 (1,0,1,0) 43 68 42 71 22 38),(.zlit 1 (0,0,0,0) 15 68 22 36 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 22 36,.zlit 1 (0,0,0,0) 15 68 22 38 43 70,.zlit 2 (1,0,1,0) 43 68 43 70 22 38),(.zlit 1 (0,0,0,0) 15 68 22 36 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 22 36,.zlit 1 (0,0,0,0) 15 68 22 38 43 71,.zlit 2 (1,0,1,0) 43 68 43 71 22 38)]),
  some (.half 72),
  some (.cross 67 true [(.zlit 1 (0,0,0,0) 87 16 85 25 42 70,.zlit 1 (0,0,0,0) 85 18 87 16 42 70,.zlit 1 (0,0,0,0) 87 18 85 25 42 70,.zlit 1 (0,0,0,0) 85 18 87 18 42 70),(.zlit 1 (0,0,0,0) 87 16 85 25 42 71,.zlit 1 (0,0,0,0) 85 18 87 16 42 71,.zlit 1 (0,0,0,0) 87 18 85 25 42 71,.zlit 1 (0,0,0,0) 85 18 87 18 42 71),(.zlit 1 (0,0,0,0) 87 16 85 25 43 70,.zlit 1 (0,0,0,0) 85 18 87 16 43 70,.zlit 1 (0,0,0,0) 87 18 85 25 43 70,.zlit 1 (0,0,0,0) 85 18 87 18 43 70),(.zlit 1 (0,0,0,0) 87 16 85 25 43 71,.zlit 1 (0,0,0,0) 85 18 87 16 43 71,.zlit 1 (0,0,0,0) 87 18 85 25 43 71,.zlit 1 (0,0,0,0) 85 18 87 18 43 71)]),
  some (.cross 36 false [(.zlit 1 (0,0,0,0) 65 4 75 0 42 70,.zlit 1 (0,0,0,0) 75 0 70 4 42 70,.zlit 1 (0,0,0,0) 65 4 77 0 42 70,.zlit 1 (0,0,0,0) 77 0 70 4 42 70),(.zlit 1 (0,0,0,0) 65 4 75 0 42 71,.zlit 1 (0,0,0,0) 75 0 70 4 42 71,.zlit 1 (0,0,0,0) 65 4 77 0 42 71,.zlit 1 (0,0,0,0) 77 0 70 4 42 71),(.zlit 1 (0,0,0,0) 65 4 75 0 43 70,.zlit 1 (0,0,0,0) 75 0 70 4 43 70,.zlit 1 (0,0,0,0) 65 4 77 0 43 70,.zlit 1 (0,0,0,0) 77 0 70 4 43 70),(.zlit 1 (0,0,0,0) 65 4 75 0 43 71,.zlit 1 (0,0,0,0) 75 0 70 4 43 71,.zlit 1 (0,0,0,0) 65 4 77 0 43 71,.zlit 1 (0,0,0,0) 77 0 70 4 43 71)]),
  none,
  some (.cross 61 true [(.zlit 1 (0,0,0,0) 94 8 88 25 42 70,.zlit 1 (0,0,0,0) 88 15 94 8 42 70,.zlit 1 (0,0,0,0) 95 8 88 25 42 70,.zlit 1 (0,0,0,0) 88 15 95 8 42 70),(.zlit 1 (0,0,0,0) 94 8 88 25 42 71,.zlit 1 (0,0,0,0) 88 15 94 8 42 71,.zlit 1 (0,0,0,0) 95 8 88 25 42 71,.zlit 1 (0,0,0,0) 88 15 95 8 42 71),(.zlit 1 (0,0,0,0) 94 8 88 25 43 70,.zlit 1 (0,0,0,0) 88 15 94 8 43 70,.zlit 1 (0,0,0,0) 95 8 88 25 43 70,.zlit 1 (0,0,0,0) 88 15 95 8 43 70),(.zlit 1 (0,0,0,0) 94 8 88 25 43 71,.zlit 1 (0,0,0,0) 88 15 94 8 43 71,.zlit 1 (0,0,0,0) 95 8 88 25 43 71,.zlit 1 (0,0,0,0) 88 15 95 8 43 71)]),
  some (.cross 101 true [(.zlit 1 (0,0,0,0) 67 4 61 25 42 70,.zlit 1 (0,0,0,0) 61 23 67 4 42 70,.zlit 1 (0,0,0,0) 68 4 61 25 42 70,.zlit 1 (0,0,0,0) 61 23 68 4 42 70),(.zlit 1 (0,0,0,0) 67 4 61 25 42 71,.zlit 1 (0,0,0,0) 61 23 67 4 42 71,.zlit 1 (0,0,0,0) 68 4 61 25 42 71,.zlit 1 (0,0,0,0) 61 23 68 4 42 71),(.zlit 1 (0,0,0,0) 67 4 61 25 43 70,.zlit 1 (0,0,0,0) 61 23 67 4 43 70,.zlit 1 (0,0,0,0) 68 4 61 25 43 70,.zlit 1 (0,0,0,0) 61 23 68 4 43 70),(.zlit 1 (0,0,0,0) 67 4 61 25 43 71,.zlit 1 (0,0,0,0) 61 23 67 4 43 71,.zlit 1 (0,0,0,0) 68 4 61 25 43 71,.zlit 1 (0,0,0,0) 61 23 68 4 43 71)]),
  some (.cross 100 true [(.zlit 1 (0,0,0,0) 71 2 63 25 42 70,.zlit 1 (0,0,0,0) 61 25 71 2 42 70,.zlit 1 (0,0,0,0) 72 2 63 25 42 70,.zlit 1 (0,0,0,0) 61 25 72 2 42 70),(.zlit 1 (0,0,0,0) 71 2 63 25 42 71,.zlit 1 (0,0,0,0) 61 25 71 2 42 71,.zlit 1 (0,0,0,0) 72 2 63 25 42 71,.zlit 1 (0,0,0,0) 61 25 72 2 42 71),(.zlit 1 (0,0,0,0) 71 2 63 25 43 70,.zlit 1 (0,0,0,0) 61 25 71 2 43 70,.zlit 1 (0,0,0,0) 72 2 63 25 43 70,.zlit 1 (0,0,0,0) 61 25 72 2 43 70),(.zlit 1 (0,0,0,0) 71 2 63 25 43 71,.zlit 1 (0,0,0,0) 61 25 71 2 43 71,.zlit 1 (0,0,0,0) 72 2 63 25 43 71,.zlit 1 (0,0,0,0) 61 25 72 2 43 71)])]

theorem u0tile : inTile C.tiles (86,142)=true := by (try rw [C_lit]); decide +kernel

theorem u0rcert : crossOne C (63,6) (64,6) (86,142) 124 true true [(.zlit 2 (1,0,1,0) 48 67 42 70 63 6,.zlit 2 (1,0,1,0) 48 67 42 70 64 6),(.zlit 2 (1,0,1,0) 48 67 42 71 63 6,.zlit 2 (1,0,1,0) 48 67 42 71 64 6),(.zlit 2 (1,0,1,0) 48 67 43 70 63 6,.zlit 2 (1,0,1,0) 48 67 43 70 64 6),(.zlit 2 (1,0,1,0) 48 67 43 71 63 6,.zlit 2 (1,0,1,0) 48 67 43 71 64 6)]=true := by (try rw [C_lit]); decide +kernel

theorem u0hc : (if true then C.next 124 else C.node 124)=(46,67) := by (try rw [C_lit]); decide +kernel

theorem u0bcert : crossOne C (50,20) (51,20) (86,142) 144 false true [(.zlit 1 (0,0,0,0) 15 68 50 20 42 70,.zlit 1 (0,0,0,0) 15 68 51 20 42 70),(.zlit 1 (0,0,0,0) 15 68 50 20 42 71,.zlit 1 (0,0,0,0) 15 68 51 20 42 71),(.zlit 1 (0,0,0,0) 15 68 50 20 43 70,.zlit 1 (0,0,0,0) 15 68 51 20 43 70),(.zlit 1 (0,0,0,0) 15 68 50 20 43 71,.zlit 1 (0,0,0,0) 15 68 51 20 43 71)]=true := by (try rw [C_lit]); decide +kernel

theorem u0bc : (if true then C.next 144 else C.node 144)=(43,68) := by (try rw [C_lit]); decide +kernel

theorem u0all0 : allOK C (86,142) 15 (0) ((WingRecords.Lower_10_200_1000.index).2.take 1) (u0es.take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all1 : allOK C (86,142) 15 (0+1) (((WingRecords.Lower_10_200_1000.index).2.drop 1).take 1) ((u0es.drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all2 : allOK C (86,142) 15 (0+1+1) ((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).take 1) (((u0es.drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all3 : allOK C (86,142) 15 (0+1+1+1) (((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).take 1) ((((u0es.drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all4 : allOK C (86,142) 15 (0+1+1+1+1) ((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).take 1) (((((u0es.drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all5 : allOK C (86,142) 15 (0+1+1+1+1+1) (((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all6 : allOK C (86,142) 15 (0+1+1+1+1+1+1) ((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all7 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1) (((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all8 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1) ((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all9 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1) (((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all10 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1) ((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all11 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all12 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all13 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all14 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all15 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all16 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all17 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) ((((((((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all18 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1) (((((((((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).take 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all19 : allOK C (86,142) 15 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) ((((((((((((((((((((WingRecords.Lower_10_200_1000.index).2.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) (((((((((((((((((((u0es.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1)=true := by (try rw [C_lit]); decide +kernel

theorem u0all : allOK C (86,142) 15 0 (WingRecords.Lower_10_200_1000.index).2 u0es=true :=
  (allOK_split 1 (0) _ _ u0all0 (allOK_split 1 (0+1) _ _ u0all1 (allOK_split 1 (0+1+1) _ _ u0all2 (allOK_split 1 (0+1+1+1) _ _ u0all3 (allOK_split 1 (0+1+1+1+1) _ _ u0all4 (allOK_split 1 (0+1+1+1+1+1) _ _ u0all5 (allOK_split 1 (0+1+1+1+1+1+1) _ _ u0all6 (allOK_split 1 (0+1+1+1+1+1+1+1) _ _ u0all7 (allOK_split 1 (0+1+1+1+1+1+1+1+1) _ _ u0all8 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1) _ _ u0all9 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1) _ _ u0all10 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all11 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all12 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all13 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all14 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all15 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all16 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all17 (allOK_split 1 (0+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) _ _ u0all18 u0all19)))))))))))))))))))

theorem u0inner : Inner C.nx 86 ∧ Inner C.ny 142 := by (try rw [C_lit]); decide +kernel


/-- The chamber test of channel 0 in the local frame of the wing: `tR ≤ tB`. -/
theorem upper0 : CopySpec.Test template WingRecords.Lower_10_200_1000.index 3 2 10 (63,6) (64,6) 15 true := by
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
  obtain ⟨hwy,Ua0,Ua1,Ub0,Ub1,bLow,H43u,DL0,DL1,DR0,DR1,hdl,hdr⟩ := CopyRange.Lower_10_200_1000.ranges0 m rfl
    (WingModel.args_unit hn0 hj hr 0) (WingModel.args_unit hn0 hj hr 1)
  replace bLow : 0<(1:ℝ)*(Y.getD 68 0)+(-1:ℝ)*(1-50050/sr^2) := bLow
  have hy1 : 1<Y.getD 70 0 := by
    rw [show (1:ℝ)=Y.getD 20 0 from (hwy.trans (by norm_num)).symm]
    exact SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide +kernel) (by decide)
  have blockB : ∀ x y : ℝ, X.getD 42 0<x → x<X.getD 43 0 → Y.getD 70 0<y → y<Y.getD 71 0 →
      x<lineX (W+b*D+tB,1-D) (gridPt X Y (43,68)) y → ¬P.Sees Bg (x,y) := by
    intro x y h0 h1 y0 y1 left
    have ax := CopyChannel.atom_between G.hx (by rw [WingModel.grid_length]; decide +kernel) h0 h1
    have ay := CopyChannel.atom_between G.hy (by rw [WingModel.grid_length]; decide +kernel) y0 y1
    rcases hBase with ⟨rfl,hB⟩|blind
    · exact CopyChannel.base_blocked_upper G fill closed contact (by positivity) u0tile
        (by simp only [gridPt]; rw [hdl,hwy]; norm_num) (by simp only [gridPt]; rw [hdr,hwy]; exact Prod.ext rfl (by norm_num))
        u0bcert (congrArg (gridPt X Y) u0bc) hB (by show 1-50050/sr^2<Y.getD 68 0; linarith) ax ay (by linarith) left
    · exact blind _ (CopyChannel.tile_filled G u0tile (z:=(x,y)) ax ay)
  have hB : Y.getD 68 0≠1-50050/sr^2 := by intro e; rw [e] at bLow; linarith
  have hR' : Y.getD 67 0≠Y.getD 6 0 := ne_of_gt (SepGeom.level_lt G.hy (by rw [WingModel.grid_length]; decide +kernel)
    (by decide : 6<67))
  have matched := CopyMatch.Lower_10_200_1000.upper0 m rfl hB hR'
  exact CopyRoles.upper_chart2 (xc:=42) (iy:=70) (win:=(61,20)) (cBn:=(43,68)) G fill closed contact (by positivity) cover (by rw [WingModel.grid_length]; decide +kernel)
    (by rw [WingModel.grid_length]; decide +kernel) u0tile u0rcert u0hc u0all u0inner (hwy.trans (by norm_num)) rfl
    (by decide) (by decide) (by decide) (by rw [WingModel.grid_length]; decide +kernel) (div_pos (by norm_num) (pow_pos hsr 2))
    htB htR hR bLow blockB matched Ua0 Ua1 Ub0 Ub1 H43u DL0 DL1 DR0 DR1 owned


end ArtGallery.Orthogonal.BoundaryPoint.CopyLocal.Lower_10_200_1000
end
