module

public import ArtGallery.Orthogonal.BoundaryPoint.SupportingEdge
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFill.InvRevGe

/-! The two stationary guard segments of the inverse room cannot see the interior
to the left of its critical axis and at or above the bottom of its critical box. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomForeign.InvRevGe
open RoomFamily.InvRevGe SupportingEdge RoomGrid RoomCoordinates RoomPolynomials ArtGallery.Orthogonal.Hard
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def bottom : P := [(-11/3), 0, (1/400400)]
def lowLine : P := [(-11/3), 0, (1/480480)]

theorem axis_ok : ok xAxis yAxis cells roles 2 .west=true := by decide +kernel
theorem low_ok : ok xAxis yAxis cells roles 3 .north=true := by decide +kernel
theorem axis_limit : levelTest xAxis yAxis roles 2 .west [-(501/2)]=true := by decide +kernel
theorem low_limit : levelTest xAxis yAxis roles 3 .north lowLine=true := by decide +kernel
theorem low_below : ltP lowLine bottom=true := by decide +kernel

theorem exclude (n : Nat) (hn : 65≤n) :
    let s : ℝ := 1/n
    let f := gridPt (xAxis.coordsR s) (yAxis.coordsR s)
    ∀ i∈[2,3], ∀ g∈ArtGallery.segment (f (RoomExclusion.nodeAt roles i 1)) (f (RoomExclusion.nodeAt roles i 2)),
    ∀ z : Point, z.1<501/2 → evalR s bottom≤z.2 → ¬(room n).Sees g z := by
  dsimp only
  intro i hi g hg z hx hy
  have hpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hbig : (65:ℝ)≤n := by exact_mod_cast hn
  have hs : 0<1/(n:ℝ) := by positivity
  have hu := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<65) hbig
  have filled := RoomFill.InvRevGe.filled_eq n hn
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl
  · apply excludes_above hs hu filled axis_ok axis_limit g hg z
    simpa [evalR,normal] using hx
  · exact excludes_above hs hu filled low_ok low_limit g hg z ((lt_sound hs hu low_below).trans_le hy)

end ArtGallery.Orthogonal.BoundaryPoint.RoomForeign.InvRevGe
end
