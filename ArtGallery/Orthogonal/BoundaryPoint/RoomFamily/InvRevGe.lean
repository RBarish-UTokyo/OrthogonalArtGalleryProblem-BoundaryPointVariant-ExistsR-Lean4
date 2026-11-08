module

public import ArtGallery.Orthogonal.BoundaryPoint.GridPins

/-! Generated polynomial grid for the actual arithmetic room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvRevGe
open RoomGrid RoomCoordinates ArtGallery.Orthogonal.Hard

def xAxis : Axis := ⟨[(301/2), 0, (-1/100100)], [
  ⟨2, [(1/100100)]⟩,
  ⟨0, [96, 0, (1/20020)]⟩,
  ⟨2, [(3/20020)]⟩,
  ⟨0, [2, 0, (-1/4004)]⟩,
  ⟨2, [(1/50050)]⟩,
  ⟨2, [(1/100100)]⟩,
  ⟨2, [(1/50050)]⟩,
  ⟨0, [2, 0, (-1/5005), 0, (1/400800400)]⟩,
  ⟨2, [(3/20020), 0, 0]⟩,
  ⟨2, [(1/20020), 0, (-1/200400200)]⟩,
  ⟨4, [(1/2004002000)]⟩,
  ⟨4, [(1/501000500)]⟩,
  ⟨4, [(1/20040020000000)]⟩,
  ⟨2, [(4999/1001000000), 0, (-1/20040020000000)]⟩,
  ⟨2, [(1/1001000000)]⟩,
  ⟨2, [(1/1001000000)]⟩,
  ⟨2, [(91923/77000000)]⟩,
  ⟨2, [(1/10010)]⟩,
  ⟨2, [(1/1001000)]⟩,
  ⟨2, [(9/1001000)]⟩]⟩
theorem x_ok : xAxis.ok = true := by decide +kernel

def yAxis : Axis := ⟨[(-481/120)], [
  ⟨0, [(1/120)]⟩,
  ⟨4, [(1/1202401200000000000)]⟩,
  ⟨2, [(1/24024000000), 0, (-1/1202401200000000000)]⟩,
  ⟨0, [(1/120), 0, (-1/24024000000)]⟩,
  ⟨0, [(63333/400000)]⟩,
  ⟨0, [(1/1200000)]⟩,
  ⟨0, [(1/1200000)]⟩,
  ⟨0, [(199999/1200000)]⟩,
  ⟨2, [(49999/24024000000)]⟩,
  ⟨2, [(1/24024000000)]⟩,
  ⟨0, [(14/3), 0, (-1/480480)]⟩,
  ⟨1, [(1/320)]⟩,
  ⟨0, [(5/6), 0]⟩]⟩
theorem y_ok : yAxis.ok = true := by decide +kernel

def cycle : Cycle := ⟨(0, 1), [(5, 1), (5, 4), (6, 4), (6, 1), (11, 1), (11, 2), (10, 2), (10, 8), (12, 8), (12, 0), (13, 0), (13, 1), (14, 1), (14, 0), (16, 0), (16, 1), (18, 1), (18, 5), (19, 5), (19, 7), (18, 7), (18, 9), (20, 9), (20, 10), (12, 10), (12, 12), (9, 12), (9, 13), (8, 13), (8, 12), (7, 12), (7, 6), (4, 6), (4, 12), (3, 12), (3, 13), (2, 13), (2, 12), (1, 12)], (1, 3), (0, 3)⟩
def cells : List (Nat × Nat × Nat × Nat) := [(1, 4, 1, 12), (7, 10, 1, 12), (12, 17, 1, 10), (10, 12, 8, 12), (4, 5, 1, 6), (6, 7, 1, 6), (5, 6, 4, 6), (17, 18, 1, 10), (2, 3, 12, 13), (0, 1, 1, 3), (8, 9, 12, 13), (10, 11, 1, 2), (14, 16, 0, 1), (18, 20, 9, 10), (18, 19, 5, 7), (12, 13, 0, 1)]
def roles : List (List Index) := [
  -- A (moving)
  [(2, 1), (2, 1), (3, 1), (2, 13), (3, 13), (0, 1)],
  -- B (moving)
  [(8, 1), (8, 1), (9, 1), (8, 13), (9, 13), (11, 1)],
  -- axis
  [(12, 6), (12, 5), (12, 7), (19, 5), (19, 7), (12, 0)],
  -- low
  [(15, 10), (14, 10), (16, 10), (14, 0), (16, 0), (20, 10)]]
def window : Index × Index := ((1, 11), (1, 12))

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
  (36, (2, 13), (2, 13)),
  (35, (3, 13), (3, 13)),
  (0, (0, 1), (0, 1)),
  (4, (8, 1), (8, 1)),
  (4, (8, 1), (9, 1)),
  (28, (8, 13), (8, 13)),
  (27, (9, 13), (9, 13)),
  (4, (11, 1), (11, 1)),
  (9, (12, 6), (12, 6)),
  (9, (12, 5), (12, 7)),
  (18, (19, 5), (19, 5)),
  (19, (19, 7), (19, 7)),
  (9, (12, 0), (12, 0)),
  (24, (15, 10), (15, 10)),
  (24, (14, 10), (16, 10)),
  (13, (14, 0), (14, 0)),
  (14, (16, 0), (16, 0)),
  (23, (20, 10), (20, 10))]
theorem marked_roles : marks.map Prod.snd = GridPins.requirements roles := by decide +kernel
theorem marks_ok : marks.all (GridPins.markOk (xAxis.gaps.length+1) (yAxis.gaps.length+1) cycle.points) = true := by decide +kernel
theorem guards_and_witnesses_on_boundary (n : Nat) (hn : 65 ≤ n) :
    let p := gridPt (xAxis.coordsR (1/(n:ℝ))) (yAxis.coordsR (1/(n:ℝ)))
    ∀ r ∈ GridPins.requirements roles, segment (p r.1) (p r.2) ⊆ (room n).boundary := by
  dsimp only
  rw [← marked_roles]
  exact GridPins.all_segments (xAxis.for_size x_ok hn) (yAxis.for_size y_ok hn)
    (by simpa only [length_coords] using marks_ok)

end ArtGallery.Orthogonal.BoundaryPoint.RoomFamily.InvRevGe
end
