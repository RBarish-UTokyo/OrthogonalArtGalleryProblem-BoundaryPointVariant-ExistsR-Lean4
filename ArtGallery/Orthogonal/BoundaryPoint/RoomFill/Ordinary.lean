module

public import ArtGallery.Orthogonal.BoundaryPoint.GridParity
public import Mathlib.Tactic.IntervalCases
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.Ordinary

/-! Certified rectangle union for the scaled room, including all edges and vertex events. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomFill.Ordinary
open RoomGrid RoomCoordinates GridParity
open RoomFamily.Ordinary

set_option maxRecDepth 12000

theorem row0 : rowOK cycle.points cells 0 25 = true := by decide +kernel
theorem row1 : rowOK cycle.points cells 1 25 = true := by decide +kernel
theorem row2 : rowOK cycle.points cells 2 25 = true := by decide +kernel
theorem row3 : rowOK cycle.points cells 3 25 = true := by decide +kernel
theorem row4 : rowOK cycle.points cells 4 25 = true := by decide +kernel
theorem row5 : rowOK cycle.points cells 5 25 = true := by decide +kernel
theorem row6 : rowOK cycle.points cells 6 25 = true := by decide +kernel
theorem row7 : rowOK cycle.points cells 7 25 = true := by decide +kernel
theorem row8 : rowOK cycle.points cells 8 25 = true := by decide +kernel
theorem row9 : rowOK cycle.points cells 9 25 = true := by decide +kernel
theorem row10 : rowOK cycle.points cells 10 25 = true := by decide +kernel
theorem row11 : rowOK cycle.points cells 11 25 = true := by decide +kernel
theorem row12 : rowOK cycle.points cells 12 25 = true := by decide +kernel
theorem row13 : rowOK cycle.points cells 13 25 = true := by decide +kernel
theorem row14 : rowOK cycle.points cells 14 25 = true := by decide +kernel
theorem row15 : rowOK cycle.points cells 15 25 = true := by decide +kernel
theorem row16 : rowOK cycle.points cells 16 25 = true := by decide +kernel
theorem row17 : rowOK cycle.points cells 17 25 = true := by decide +kernel
theorem row18 : rowOK cycle.points cells 18 25 = true := by decide +kernel
theorem row19 : rowOK cycle.points cells 19 25 = true := by decide +kernel
theorem row20 : rowOK cycle.points cells 20 25 = true := by decide +kernel
theorem row21 : rowOK cycle.points cells 21 25 = true := by decide +kernel
theorem row22 : rowOK cycle.points cells 22 25 = true := by decide +kernel
theorem row23 : rowOK cycle.points cells 23 25 = true := by decide +kernel
theorem row24 : rowOK cycle.points cells 24 25 = true := by decide +kernel
theorem row25 : rowOK cycle.points cells 25 25 = true := by decide +kernel
theorem row26 : rowOK cycle.points cells 26 25 = true := by decide +kernel
theorem row27 : rowOK cycle.points cells 27 25 = true := by decide +kernel
theorem row28 : rowOK cycle.points cells 28 25 = true := by decide +kernel
theorem row29 : rowOK cycle.points cells 29 25 = true := by decide +kernel
theorem row30 : rowOK cycle.points cells 30 25 = true := by decide +kernel
theorem row31 : rowOK cycle.points cells 31 25 = true := by decide +kernel
theorem row32 : rowOK cycle.points cells 32 25 = true := by decide +kernel
theorem row33 : rowOK cycle.points cells 33 25 = true := by decide +kernel
theorem row34 : rowOK cycle.points cells 34 25 = true := by decide +kernel
theorem row35 : rowOK cycle.points cells 35 25 = true := by decide +kernel
theorem row36 : rowOK cycle.points cells 36 25 = true := by decide +kernel
theorem row37 : rowOK cycle.points cells 37 25 = true := by decide +kernel
theorem row38 : rowOK cycle.points cells 38 25 = true := by decide +kernel
theorem row39 : rowOK cycle.points cells 39 25 = true := by decide +kernel
theorem row40 : rowOK cycle.points cells 40 25 = true := by decide +kernel
theorem row41 : rowOK cycle.points cells 41 25 = true := by decide +kernel
theorem row42 : rowOK cycle.points cells 42 25 = true := by decide +kernel
theorem row43 : rowOK cycle.points cells 43 25 = true := by decide +kernel
theorem row44 : rowOK cycle.points cells 44 25 = true := by decide +kernel
theorem row45 : rowOK cycle.points cells 45 25 = true := by decide +kernel
theorem row46 : rowOK cycle.points cells 46 25 = true := by decide +kernel
theorem row47 : rowOK cycle.points cells 47 25 = true := by decide +kernel
theorem row48 : rowOK cycle.points cells 48 25 = true := by decide +kernel
theorem row49 : rowOK cycle.points cells 49 25 = true := by decide +kernel
theorem row50 : rowOK cycle.points cells 50 25 = true := by decide +kernel
theorem row51 : rowOK cycle.points cells 51 25 = true := by decide +kernel
theorem row52 : rowOK cycle.points cells 52 25 = true := by decide +kernel
theorem row53 : rowOK cycle.points cells 53 25 = true := by decide +kernel
theorem row54 : rowOK cycle.points cells 54 25 = true := by decide +kernel
theorem row55 : rowOK cycle.points cells 55 25 = true := by decide +kernel
theorem row56 : rowOK cycle.points cells 56 25 = true := by decide +kernel
theorem row57 : rowOK cycle.points cells 57 25 = true := by decide +kernel
theorem row58 : rowOK cycle.points cells 58 25 = true := by decide +kernel
theorem row59 : rowOK cycle.points cells 59 25 = true := by decide +kernel
theorem row60 : rowOK cycle.points cells 60 25 = true := by decide +kernel
theorem row61 : rowOK cycle.points cells 61 25 = true := by decide +kernel
theorem row62 : rowOK cycle.points cells 62 25 = true := by decide +kernel
theorem row63 : rowOK cycle.points cells 63 25 = true := by decide +kernel
theorem row64 : rowOK cycle.points cells 64 25 = true := by decide +kernel
theorem row65 : rowOK cycle.points cells 65 25 = true := by decide +kernel
theorem row66 : rowOK cycle.points cells 66 25 = true := by decide +kernel
theorem row67 : rowOK cycle.points cells 67 25 = true := by decide +kernel
theorem row68 : rowOK cycle.points cells 68 25 = true := by decide +kernel
theorem row69 : rowOK cycle.points cells 69 25 = true := by decide +kernel
theorem row70 : rowOK cycle.points cells 70 25 = true := by decide +kernel
theorem row71 : rowOK cycle.points cells 71 25 = true := by decide +kernel
theorem row72 : rowOK cycle.points cells 72 25 = true := by decide +kernel

theorem rows (i : Fin 73) : rowOK cycle.points cells i.val 25=true := by
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
  · exact row41
  · exact row42
  · exact row43
  · exact row44
  · exact row45
  · exact row46
  · exact row47
  · exact row48
  · exact row49
  · exact row50
  · exact row51
  · exact row52
  · exact row53
  · exact row54
  · exact row55
  · exact row56
  · exact row57
  · exact row58
  · exact row59
  · exact row60
  · exact row61
  · exact row62
  · exact row63
  · exact row64
  · exact row65
  · exact row66
  · exact row67
  · exact row68
  · exact row69
  · exact row70
  · exact row71
  · exact row72

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

end ArtGallery.Orthogonal.BoundaryPoint.RoomFill.Ordinary
end
