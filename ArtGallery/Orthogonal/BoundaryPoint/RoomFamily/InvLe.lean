module

public import ArtGallery.Orthogonal.BoundaryPoint.GridPins

/-! Generated polynomial grid for the actual arithmetic room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvLe
open RoomGrid RoomCoordinates ArtGallery.Orthogonal.Hard

def xAxis : Axis := ⟨[(301/2), 0, (-1/100100)], [
  ⟨2, [(1/100100)]⟩,
  ⟨0, [96, 0, (1/20020)]⟩,
  ⟨2, [(3/20020)]⟩,
  ⟨0, [2, 0, (-1/5005)]⟩,
  ⟨2, [(1/20020)]⟩,
  ⟨0, [2, 0, (-1/10010)]⟩,
  ⟨2, [(1/20020)]⟩,
  ⟨4, [(1/20040020000000)]⟩,
  ⟨4, [(49999/20040020000000)]⟩,
  ⟨2, [(1/1001000), 0, 0]⟩,
  ⟨2, [(3/125125), 0, 0]⟩,
  ⟨2, [(1/40040), 0, (-1/200400200)]⟩,
  ⟨2, [(3/20020), 0, 0]⟩,
  ⟨2, [(1/1001), 0, (1/400800400)]⟩,
  ⟨2, [(49999/1001000000)]⟩,
  ⟨2, [(1/1001000000)]⟩,
  ⟨2, [(1/1001000000)]⟩,
  ⟨2, [(49999/1001000000)]⟩,
  ⟨2, [(1/100100)]⟩]⟩
theorem x_ok : xAxis.ok = true := by decide +kernel

def yAxis : Axis := ⟨[(-481/120)], [
  ⟨0, [(1/120)]⟩,
  ⟨4, [(1/1202401200000000000)]⟩,
  ⟨2, [(1/24024000000), 0, (-1/1202401200000000000)]⟩,
  ⟨0, [(1/24), 0, (-1/24024000000)]⟩,
  ⟨0, [(1/48), 0, (-1/24024000000)]⟩,
  ⟨2, [(1/24024000000)]⟩,
  ⟨0, [(1/48)]⟩,
  ⟨0, [(1/12)]⟩,
  ⟨0, [(33333/400000)]⟩,
  ⟨0, [(1/1200000)]⟩,
  ⟨0, [(1/1200000)]⟩,
  ⟨0, [(5699999/1200000)]⟩,
  ⟨1, [(1/320)]⟩,
  ⟨0, [(5/6), 0]⟩]⟩
theorem y_ok : yAxis.ok = true := by decide +kernel

def cycle : Cycle := ⟨(0, 1), [(4, 1), (4, 4), (5, 4), (5, 1), (7, 1), (7, 0), (8, 0), (8, 1), (15, 1), (15, 0), (17, 0), (17, 1), (19, 1), (19, 2), (18, 2), (18, 5), (19, 5), (19, 6), (14, 6), (14, 13), (13, 13), (13, 14), (12, 14), (12, 13), (11, 13), (11, 7), (9, 7), (9, 9), (10, 9), (10, 11), (9, 11), (9, 13), (7, 13), (7, 8), (6, 8), (6, 13), (3, 13), (3, 14), (2, 14), (2, 13), (1, 13)], (1, 3), (0, 3)⟩
def cells : List (Nat × Nat × Nat × Nat) := [(1, 4, 1, 13), (5, 6, 1, 13), (7, 9, 1, 13), (6, 7, 1, 8), (11, 14, 1, 13), (9, 11, 1, 7), (4, 5, 4, 13), (14, 18, 1, 6), (2, 3, 13, 14), (0, 1, 1, 3), (12, 13, 13, 14), (18, 19, 1, 2), (15, 17, 0, 1), (18, 19, 5, 6), (9, 10, 9, 11), (7, 8, 0, 1)]
def roles : List (List Index) := [
  -- A (moving)
  [(2, 1), (2, 1), (3, 1), (2, 14), (3, 14), (0, 1)],
  -- B (moving)
  [(12, 1), (12, 1), (13, 1), (12, 14), (13, 14), (19, 1)],
  -- axis
  [(7, 10), (7, 9), (7, 11), (10, 9), (10, 11), (7, 0)],
  -- low
  [(16, 6), (15, 6), (17, 6), (15, 0), (17, 0), (19, 6)]]
def window : Index × Index := ((1, 12), (1, 13))

theorem cycle_ok : cycle.ok = true := by decide +kernel
theorem axis_edges : cyclicAxis cycle.points := by decide +kernel
theorem index_bounds : ∀ p ∈ cycle.points, p.1 < xAxis.gaps.length+1 ∧ p.2 < yAxis.gaps.length+1 := by decide +kernel

noncomputable def room (n : Nat) : Polygon :=
  ⟨cycle.points.map (gridPt (xAxis.coordsR (1/(n:ℝ))) (yAxis.coordsR (1/(n:ℝ))))⟩
theorem simple (n : Nat) (hn : 65 ≤ n) : (room n).Simple :=
  cycle.simple (xAxis.for_size x_ok hn) (yAxis.for_size y_ok hn)
    (by simpa only [length_coords] using index_bounds) cycle_ok
theorem orthogonal (n : Nat) : (room n).Orthogonal :=
  grid_orthogonal _ _ _ axis_edges

def marks : List GridPins.Mark := [(0, (2, 1), (2, 1)),
  (0, (2, 1), (3, 1)),
  (38, (2, 14), (2, 14)),
  (37, (3, 14), (3, 14)),
  (0, (0, 1), (0, 1)),
  (8, (12, 1), (12, 1)),
  (8, (12, 1), (13, 1)),
  (22, (12, 14), (12, 14)),
  (21, (13, 14), (13, 14)),
  (12, (19, 1), (19, 1)),
  (33, (7, 10), (7, 10)),
  (33, (7, 9), (7, 11)),
  (28, (10, 9), (10, 9)),
  (29, (10, 11), (10, 11)),
  (5, (7, 0), (7, 0)),
  (18, (16, 6), (16, 6)),
  (18, (15, 6), (17, 6)),
  (9, (15, 0), (15, 0)),
  (10, (17, 0), (17, 0)),
  (17, (19, 6), (19, 6))]
theorem marked_roles : marks.map Prod.snd = GridPins.requirements roles := by decide +kernel
theorem marks_ok : marks.all (GridPins.markOk (xAxis.gaps.length+1) (yAxis.gaps.length+1) cycle.points) = true := by decide +kernel
theorem guards_and_witnesses_on_boundary (n : Nat) (hn : 65 ≤ n) :
    let p := gridPt (xAxis.coordsR (1/(n:ℝ))) (yAxis.coordsR (1/(n:ℝ)))
    ∀ r ∈ GridPins.requirements roles, segment (p r.1) (p r.2) ⊆ (room n).boundary := by
  dsimp only
  rw [← marked_roles]
  exact GridPins.all_segments (xAxis.for_size x_ok hn) (yAxis.for_size y_ok hn)
    (by simpa only [length_coords] using marks_ok)

end ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvLe
end
