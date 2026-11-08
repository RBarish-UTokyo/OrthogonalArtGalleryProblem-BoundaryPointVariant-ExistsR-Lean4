module

public import ArtGallery.Orthogonal.BoundaryPoint.GridParity
public import Mathlib.Tactic.IntervalCases
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.Lower
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFill.Ordinary

/-! Certified rectangle union for the scaled room, including all edges and vertex events. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomFill.Lower
open RoomGrid RoomCoordinates GridParity
open RoomFamily.Lower

set_option maxRecDepth 12000

theorem rows (i : Fin 73) : rowOK cycle.points cells i.val 25=true :=
  ArtGallery.Orthogonal.BoundaryPoint.RoomFill.Ordinary.rows i

theorem cell_indices : ∀ r ∈ cells, r.1<xAxis.gaps.length+1 ∧ r.2.1<xAxis.gaps.length+1 ∧
    r.2.2.1<yAxis.gaps.length+1 ∧ r.2.2.2<yAxis.gaps.length+1 := by decide +kernel

theorem filled_eq (n : Nat) (hn : 65 ≤ n) : (room n).filled =
    cellsR (xAxis.coordsR (1/(n:ℝ))) (yAxis.coordsR (1/(n:ℝ))) cells := by
  apply filled_of_rows (xAxis.for_size x_ok hn) (yAxis.for_size y_ok hn)
    (by simpa only [length_coords] using index_bounds) axis_edges (simple n hn)
    (by simpa only [length_coords] using cell_indices)
  intro i
  have hx : (xAxis.coordsR (1/(n:ℝ))).length=36 := (length_coords _ _).trans rfl
  have hy : (yAxis.coordsR (1/(n:ℝ))).length=25 := (length_coords _ _).trans rfl
  rw [hy]
  exact rows ⟨i.val,by simpa only [hx] using i.isLt⟩

end ArtGallery.Orthogonal.BoundaryPoint.RoomFill.Lower
end
