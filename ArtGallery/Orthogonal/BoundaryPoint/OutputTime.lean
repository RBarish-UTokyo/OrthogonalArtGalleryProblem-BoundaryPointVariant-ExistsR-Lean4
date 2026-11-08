module

public import ArtGallery.Orthogonal.BoundaryPoint.CandidateWord
public import ArtGallery.Stade.PTimeRat

/-! # Machine polynomial time of the actual rational output encoding

This covers the final bit-string serialization once the vertex list and the
guard budget have been computed. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.OutputTime
open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade CandidateWord RectContour

def pointDigits (v : Vertex) : FracDigits := (pack v).digits

theorem point_digits_pt : PT pointDigits := by
  unfold pointDigits pack FracPoint.digits
  fun_prop

theorem serialize_pt {α : Type} [Code α] {vertices : α → List Vertex} {g : α → Nat}
    (hv : PT vertices) (hg : PT g) :
    PT (fun a => encodeAGP ((vertices a).map pack) (g a)) := by
  have hd : PT (fun a => (vertices a).map pointDigits) := PT.map (point_digits_pt.comp PT.snd') hv
  have h : PT (fun a => agpWord ((vertices a).map pointDigits) (g a).bits) := by
    unfold agpWord
    fun_prop
  exact h.of_eq (fun a => by rw [encodeAGP_eq_agpWord,List.map_map]; rfl)

end ArtGallery.Orthogonal.BoundaryPoint.OutputTime
end
