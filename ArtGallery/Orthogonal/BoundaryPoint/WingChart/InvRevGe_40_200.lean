module

public import ArtGallery.Orthogonal.BoundaryPoint.BoundaryChart

/-! Joined wing turn indices and coordinate selectors. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvRevGe_40_200
open RoomGrid BoundaryChart CorridorProgram

def chart : Chart where
  x := [42, 2, 26, 34, 18, 40, 110, 41, 32, 98, 33, 22, 6, 28, 47, 25, 45, 60, 65, 50, 14, 12, 48, 122, 49, 10, 20, 39, 17, 37, 8, 59, 0, 1, 7, 63, 57, 3, 52, 128, 53, 5, 55, 84, 31, 82, 83, 67, 75, 76, 68, 86, 87, 69, 89, 70, 97, 90, 164, 91, 71, 81, 95, 93]
  y := [90, 66, 89, 85, 78, 94, 75, 95, 72, 92, 71, 52, 0, 48, 1, 31, 83, 54, 3, 40, 7, 22, 42, 27, 23, 62, 140, 63, 61, 65, 44, 116, 45, 29, 47, 50, 13, 32, 8, 14, 34, 19, 15, 56, 134, 57, 36, 104, 37, 21, 39, 9, 59]
  cycle := ⟨(0, 22), [(2, 22), (2, 21), (5, 21), (5, 19), (7, 19), (7, 21), (12, 21), (12, 18), (1, 18), (1, 14), (22, 14), (22, 13), (24, 13), (24, 14), (32, 14), (32, 12), (33, 12), (33, 14), (37, 14), (37, 12), (38, 12), (38, 11), (40, 11), (40, 12), (44, 12), (44, 3), (43, 3), (43, 1), (48, 1), (48, 4), (49, 4), (49, 1), (54, 1), (54, 2), (53, 2), (53, 8), (55, 8), (55, 0), (56, 0), (56, 1), (57, 1), (57, 0), (59, 0), (59, 1), (61, 1), (61, 5), (62, 5), (62, 7), (61, 7), (61, 9), (63, 9), (63, 10), (55, 10), (55, 15), (52, 15), (52, 16), (51, 16), (51, 15), (50, 15), (50, 6), (47, 6), (47, 15), (46, 15), (46, 16), (45, 16), (45, 15), (41, 15), (41, 17), (42, 17), (42, 18), (34, 18), (34, 25), (35, 25), (35, 27), (34, 27), (34, 43), (36, 43), (36, 45), (34, 45), (34, 51), (31, 51), (31, 52), (30, 52), (30, 38), (28, 38), (28, 46), (29, 46), (29, 48), (28, 48), (28, 49), (27, 49), (27, 50), (26, 50), (26, 42), (20, 42), (20, 41), (3, 41), (3, 40), (4, 40), (4, 39), (8, 39), (8, 37), (10, 37), (10, 39), (25, 39), (25, 36), (19, 36), (19, 35), (21, 35), (21, 28), (18, 28), (18, 29), (17, 29), (17, 20), (15, 20), (15, 30), (16, 30), (16, 32), (15, 32), (15, 33), (14, 33), (14, 34), (13, 34), (13, 24), (11, 24)], (11, 23), (0, 23)⟩

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

end ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvRevGe_40_200
end
