module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomExclusion
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFill.Shifted

/-! Continuous foreign-guard exclusions on both critical boxes of the physical room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomForeign.Shifted
open RoomFamily.Shifted RoomExclusion RoomGrid ArtGallery.Orthogonal.Hard
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

-- gFloor to the addition box
def test0 : Query := ⟨2, (867, 869, (49/100), (51/100)), 829, (-4), 0⟩
theorem test0_ok : ok xAxis yAxis cells roles test0=true := by decide +kernel

-- gFin to the addition box
def test1 : Query := ⟨0, (867, 869, (49/100), (51/100)), (6127/8), (9/20), (11/5)⟩
theorem test1_ok : ok xAxis yAxis cells roles test1=true := by decide +kernel

-- gFinSide to the addition box
def test2 : Query := ⟨1, (867, 869, (49/100), (51/100)), (1601/2), (3/5), (11/5)⟩
theorem test2_ok : ok xAxis yAxis cells roles test2=true := by decide +kernel

-- gFloor to the relay box
def test3 : Query := ⟨2, (1438, 1440, (11/5), (221/100)), 829, (-4), 0⟩
theorem test3_ok : ok xAxis yAxis cells roles test3=true := by decide +kernel

-- gFin to the relay box
def test4 : Query := ⟨0, (1438, 1440, (11/5), (221/100)), (6127/8), (9/20), (11/5)⟩
theorem test4_ok : ok xAxis yAxis cells roles test4=true := by decide +kernel

-- gFinSide to the relay box
def test5 : Query := ⟨1, (1438, 1440, (11/5), (221/100)), (1601/2), (3/5), (11/5)⟩
theorem test5_ok : ok xAxis yAxis cells roles test5=true := by decide +kernel

-- q to the addition box
def test6 : Query := ⟨3, (867, 869, (49/100), (51/100)), (3063/4), 0, (39/100)⟩
theorem test6_ok : ok xAxis yAxis cells roles test6=true := by decide +kernel

-- x to the relay box
def test7 : Query := ⟨5, (1438, 1440, (11/5), (221/100)), 829, (-4), 0⟩
theorem test7_ok : ok xAxis yAxis cells roles test7=true := by decide +kernel

-- z to the relay box
def test8 : Query := ⟨6, (1438, 1440, (11/5), (221/100)), 829, (-4), 0⟩
theorem test8_ok : ok xAxis yAxis cells roles test8=true := by decide +kernel

def tests : List Query := [test0, test1, test2, test3, test4, test5, test6, test7, test8]
theorem passed : ∀ q∈tests, ok xAxis yAxis cells roles q=true := by
  intro q h
  simp only [tests,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact test0_ok
  · exact test1_ok
  · exact test2_ok
  · exact test3_ok
  · exact test4_ok
  · exact test5_ok
  · exact test6_ok
  · exact test7_ok
  · exact test8_ok

theorem exclude (n : Nat) (hn : 65≤n) :
    let s : ℝ := 1/n
    let f := gridPt (xAxis.coordsR s) (yAxis.coordsR s)
    ∀ c∈tests, ∀ g∈ArtGallery.segment (f (nodeAt roles c.role 1)) (f (nodeAt roles c.role 2)),
    ∀ z : Point, (c.target.1:ℝ)≤z.1 → z.1≤(c.target.2.1:ℝ) →
      (c.target.2.2.1:ℝ)≤z.2 → z.2≤(c.target.2.2.2:ℝ) → ¬(room n).Sees g z := by
  dsimp only
  intro c hc
  have hpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hbig : (65:ℝ)≤n := by exact_mod_cast hn
  exact sound (s:=1/(n:ℝ)) (by positivity) (one_div_le_one_div_of_le (by norm_num) hbig) (RoomFill.Shifted.filled_eq n hn) (passed c hc)

end ArtGallery.Orthogonal.BoundaryPoint.RoomForeign.Shifted
end
