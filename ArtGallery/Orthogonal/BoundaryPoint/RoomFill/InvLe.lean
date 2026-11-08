module

public import ArtGallery.Orthogonal.BoundaryPoint.GridParity
public import Mathlib.Tactic.IntervalCases
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvLe

/-! Certified rectangle union for the scaled room, including all edges and vertex events. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomFill.InvLe
open RoomGrid RoomCoordinates GridParity
open RoomFamily.InvLe

set_option maxRecDepth 12000

theorem row0 : rowOK cycle.points cells 0 15 = true := by decide +kernel
theorem row1 : rowOK cycle.points cells 1 15 = true := by decide +kernel
theorem row2 : rowOK cycle.points cells 2 15 = true := by decide +kernel
theorem row3 : rowOK cycle.points cells 3 15 = true := by decide +kernel
theorem row4 : rowOK cycle.points cells 4 15 = true := by decide +kernel
theorem row5 : rowOK cycle.points cells 5 15 = true := by decide +kernel
theorem row6 : rowOK cycle.points cells 6 15 = true := by decide +kernel
theorem row7 : rowOK cycle.points cells 7 15 = true := by decide +kernel
theorem row8 : rowOK cycle.points cells 8 15 = true := by decide +kernel
theorem row9 : rowOK cycle.points cells 9 15 = true := by decide +kernel
theorem row10 : rowOK cycle.points cells 10 15 = true := by decide +kernel
theorem row11 : rowOK cycle.points cells 11 15 = true := by decide +kernel
theorem row12 : rowOK cycle.points cells 12 15 = true := by decide +kernel
theorem row13 : rowOK cycle.points cells 13 15 = true := by decide +kernel
theorem row14 : rowOK cycle.points cells 14 15 = true := by decide +kernel
theorem row15 : rowOK cycle.points cells 15 15 = true := by decide +kernel
theorem row16 : rowOK cycle.points cells 16 15 = true := by decide +kernel
theorem row17 : rowOK cycle.points cells 17 15 = true := by decide +kernel
theorem row18 : rowOK cycle.points cells 18 15 = true := by decide +kernel
theorem row19 : rowOK cycle.points cells 19 15 = true := by decide +kernel
theorem row20 : rowOK cycle.points cells 20 15 = true := by decide +kernel
theorem row21 : rowOK cycle.points cells 21 15 = true := by decide +kernel
theorem row22 : rowOK cycle.points cells 22 15 = true := by decide +kernel
theorem row23 : rowOK cycle.points cells 23 15 = true := by decide +kernel
theorem row24 : rowOK cycle.points cells 24 15 = true := by decide +kernel
theorem row25 : rowOK cycle.points cells 25 15 = true := by decide +kernel
theorem row26 : rowOK cycle.points cells 26 15 = true := by decide +kernel
theorem row27 : rowOK cycle.points cells 27 15 = true := by decide +kernel
theorem row28 : rowOK cycle.points cells 28 15 = true := by decide +kernel
theorem row29 : rowOK cycle.points cells 29 15 = true := by decide +kernel
theorem row30 : rowOK cycle.points cells 30 15 = true := by decide +kernel
theorem row31 : rowOK cycle.points cells 31 15 = true := by decide +kernel
theorem row32 : rowOK cycle.points cells 32 15 = true := by decide +kernel
theorem row33 : rowOK cycle.points cells 33 15 = true := by decide +kernel
theorem row34 : rowOK cycle.points cells 34 15 = true := by decide +kernel
theorem row35 : rowOK cycle.points cells 35 15 = true := by decide +kernel
theorem row36 : rowOK cycle.points cells 36 15 = true := by decide +kernel
theorem row37 : rowOK cycle.points cells 37 15 = true := by decide +kernel
theorem row38 : rowOK cycle.points cells 38 15 = true := by decide +kernel
theorem row39 : rowOK cycle.points cells 39 15 = true := by decide +kernel
theorem row40 : rowOK cycle.points cells 40 15 = true := by decide +kernel

theorem rows (i : Fin 41) : rowOK cycle.points cells i.val 15=true := by
  obtain ⟨i,hi⟩ := i
  interval_cases i
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40

theorem cell_indices : ∀ r ∈ cells, r.1<xAxis.gaps.length+1 ∧ r.2.1<xAxis.gaps.length+1 ∧
    r.2.2.1<yAxis.gaps.length+1 ∧ r.2.2.2<yAxis.gaps.length+1 := by decide +kernel

theorem filled_eq (n : Nat) (hn : 65 ≤ n) : (room n).filled =
    cellsR (xAxis.coordsR (1/(n:ℝ))) (yAxis.coordsR (1/(n:ℝ))) cells := by
  apply filled_of_rows (xAxis.for_size x_ok hn) (yAxis.for_size y_ok hn)
    (by simpa only [length_coords] using index_bounds) axis_edges (simple n hn)
    (by simpa only [length_coords] using cell_indices)
  intro i
  have hx : (xAxis.coordsR (1/(n:ℝ))).length=20 := (length_coords _ _).trans rfl
  have hy : (yAxis.coordsR (1/(n:ℝ))).length=15 := (length_coords _ _).trans rfl
  rw [hy]
  exact rows ⟨i.val,by simpa only [hx] using i.isLt⟩

end ArtGallery.Orthogonal.BoundaryPoint.RoomFill.InvLe
end
