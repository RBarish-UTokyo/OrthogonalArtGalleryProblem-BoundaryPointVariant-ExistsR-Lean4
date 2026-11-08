module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.Shifted
public import ArtGallery.Orthogonal.BoundaryPoint.SlotLines
public import Mathlib.Tactic.Ring

/-! Arithmetic on the actual hard-room slot records. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.Shifted
open RoomFamily.Shifted RoomGrid RoomCoordinates SlotLines ArtGallery.Orthogonal.Hard Geometry DerivedAlgebra
set_option maxRecDepth 14000

noncomputable def guard (s : ℝ) (i : Nat) (t : ℝ) : Point :=
  slot (gridPt (xAxis.coordsR s) (yAxis.coordsR s)) roles i t

private theorem x2 (s : ℝ) : (xAxis.coordsR s).getD 2 0=evalR s [272] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x3 (s : ℝ) : (xAxis.coordsR s).getD 3 0=evalR s [272, 0, (81/1001000)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x6 (s : ℝ) : (xAxis.coordsR s).getD 6 0=evalR s [358] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x7 (s : ℝ) : (xAxis.coordsR s).getD 7 0=evalR s [358, 0, (9/100100)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x10 (s : ℝ) : (xAxis.coordsR s).getD 10 0=evalR s [(1169/2), 0, (4/25025)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x11 (s : ℝ) : (xAxis.coordsR s).getD 11 0=evalR s [(1169/2), 0, (1/3575)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x33 (s : ℝ) : (xAxis.coordsR s).getD 33 0=evalR s [(100879/70)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem x34 (s : ℝ) : (xAxis.coordsR s).getD 34 0=evalR s [(100879/70), 0, (27/557375)] := by
  simp [xAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem y2 (s : ℝ) : (yAxis.coordsR s).getD 2 0=evalR s [(-3)] := by
  simp [yAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem y4 (s : ℝ) : (yAxis.coordsR s).getD 4 0=evalR s [(-2)] := by
  simp [yAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem y6 (s : ℝ) : (yAxis.coordsR s).getD 6 0=evalR s [(-17/10)] := by
  simp [yAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

private theorem y8 (s : ℝ) : (yAxis.coordsR s).getD 8 0=evalR s [(-33/245)] := by
  simp [yAxis,Axis.coordsR,positions,Gap.valR,evalR] <;> ring

theorem position_q (s t : ℝ) : guard s 3 t =
    (evalR s [272]+t*(2/3)*(evalR s [272, 0, (81/1001000)]-evalR s [272]),(-17/10)) := by
  unfold guard slot
  dsimp only
  change lerp ((xAxis.coordsR s).getD 2 0,(yAxis.coordsR s).getD 6 0)
    ((xAxis.coordsR s).getD 3 0,(yAxis.coordsR s).getD 6 0) (t*(2/3))=_
  rw [x2,x3,y6]
  ext <;> simp [lerp,evalR] <;> ring

theorem position_r (s t : ℝ) : guard s 4 t =
    (evalR s [(100879/70)]+t*(2/3)*(evalR s [(100879/70), 0, (27/557375)]-evalR s [(100879/70)]),(-33/245)) := by
  unfold guard slot
  dsimp only
  change lerp ((xAxis.coordsR s).getD 33 0,(yAxis.coordsR s).getD 8 0)
    ((xAxis.coordsR s).getD 34 0,(yAxis.coordsR s).getD 8 0) (t*(2/3))=_
  rw [x33,x34,y8]
  ext <;> simp [lerp,evalR] <;> ring

theorem position_x (s t : ℝ) : guard s 5 t =
    (evalR s [358]+t*(2/3)*(evalR s [358, 0, (9/100100)]-evalR s [358]),(-2)) := by
  unfold guard slot
  dsimp only
  change lerp ((xAxis.coordsR s).getD 6 0,(yAxis.coordsR s).getD 4 0)
    ((xAxis.coordsR s).getD 7 0,(yAxis.coordsR s).getD 4 0) (t*(2/3))=_
  rw [x6,x7,y4]
  ext <;> simp [lerp,evalR] <;> ring

theorem position_z (s t : ℝ) : guard s 6 t =
    (evalR s [(1169/2), 0, (4/25025)]+t*(2/3)*(evalR s [(1169/2), 0, (1/3575)]-evalR s [(1169/2), 0, (4/25025)]),(-3)) := by
  unfold guard slot
  dsimp only
  change lerp ((xAxis.coordsR s).getD 10 0,(yAxis.coordsR s).getD 2 0)
    ((xAxis.coordsR s).getD 11 0,(yAxis.coordsR s).getD 2 0) (t*(2/3))=_
  rw [x10,x11,y2]
  ext <;> simp [lerp,evalR] <;> ring

theorem balance (s tx tr tz : ℝ) :
    (8*xSlope 766 (guard s 5 tx)+xSlope (2639/2) (guard s 4 tr))/9-
      xSlope (1655/2) (guard s 6 tz) = (4/3)*(s^2/50050)*(tz-tx-tr-(-2)) := by
  rw [position_x,position_r,position_z]
  norm_num [xSlope,evalR] <;> ring

end ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.Shifted
end
