module

public import ArtGallery.Orthogonal.BoundaryPoint.BoundaryChart

/-! Joined wing turn indices and coordinate selectors. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_1_360
open RoomGrid BoundaryChart CorridorProgram

def chart : Chart where
  x := [42, 26, 2, 34, 18, 40, 110, 41, 32, 98, 33, 22, 6, 28, 47, 25, 45, 60, 65, 50, 14, 12, 48, 122, 49, 10, 20, 39, 17, 37, 8, 59, 0, 1, 7, 63, 57, 3, 52, 128, 53, 5, 55, 84, 31, 82, 83, 67, 68, 69, 70, 97, 71, 95, 74, 86, 87, 75, 90, 164, 91, 81, 89]
  y := [90, 66, 89, 85, 78, 92, 81, 77, 73, 94, 158, 95, 52, 0, 48, 1, 31, 83, 54, 3, 40, 7, 22, 42, 27, 23, 62, 140, 63, 61, 65, 44, 116, 45, 29, 47, 50, 13, 32, 8, 14, 34, 19, 15, 56, 134, 57, 36, 104, 37, 21, 39, 9, 59]
  cycle := ⟨(0, 23), [(1, 23), (1, 22), (5, 22), (5, 20), (7, 20), (7, 22), (12, 22), (12, 19), (2, 19), (2, 15), (22, 15), (22, 14), (24, 14), (24, 15), (32, 15), (32, 13), (33, 13), (33, 15), (37, 15), (37, 13), (38, 13), (38, 12), (40, 12), (40, 13), (44, 13), (44, 3), (43, 3), (43, 1), (47, 1), (47, 4), (48, 4), (48, 1), (50, 1), (50, 0), (51, 0), (51, 1), (58, 1), (58, 0), (60, 0), (60, 1), (62, 1), (62, 2), (61, 2), (61, 5), (62, 5), (62, 6), (57, 6), (57, 16), (56, 16), (56, 17), (55, 17), (55, 16), (54, 16), (54, 7), (52, 7), (52, 9), (53, 9), (53, 11), (52, 11), (52, 16), (50, 16), (50, 8), (49, 8), (49, 16), (46, 16), (46, 17), (45, 17), (45, 16), (41, 16), (41, 18), (42, 18), (42, 19), (34, 19), (34, 26), (35, 26), (35, 28), (34, 28), (34, 44), (36, 44), (36, 46), (34, 46), (34, 52), (31, 52), (31, 53), (30, 53), (30, 39), (28, 39), (28, 47), (29, 47), (29, 49), (28, 49), (28, 50), (27, 50), (27, 51), (26, 51), (26, 43), (20, 43), (20, 42), (3, 42), (3, 41), (4, 41), (4, 40), (8, 40), (8, 38), (10, 38), (10, 40), (25, 40), (25, 37), (19, 37), (19, 36), (21, 36), (21, 29), (18, 29), (18, 30), (17, 30), (17, 21), (15, 21), (15, 31), (16, 31), (16, 33), (15, 33), (15, 34), (14, 34), (14, 35), (13, 35), (13, 25), (11, 25)], (11, 24), (0, 24)⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

theorem axis_edges : cyclicAxis chart.cycle.points := by decide +kernel
theorem indices : ∀ v∈chart.cycle.points, v.1<chart.x.length ∧ v.2<chart.y.length := by decide +kernel
theorem checked : chart.cycle.ok=true := by decide +kernel

theorem orthogonal (g : Data ℚ) : (actual chart g).Orthogonal := BoundaryChart.orthogonal _ axis_edges _
theorem simple (g : Data ℚ)
    (hx : ((selected (pool false g) chart.x).map ((↑) : ℚ → ℝ)).IsChain (·<·))
    (hy : ((selected (pool true g) chart.y).map ((↑) : ℚ → ℝ)).IsChain (·<·)) :
    (actual chart g).Simple := BoundaryChart.simple _ checked indices _ hx hy

end ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_1_360
end
