module

public import ArtGallery.Orthogonal.BoundaryPoint.OutputTime
public import PT.Raw

/-! # Polynomial running time of the full boundary-guard candidate
This theorem concerns the complete executable word function, including rejection
on parse failure, private-variable naming, physical coordinates, door splicing,
and serialization. Geometric language equivalence is a separate obligation. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WordTime
open Complexity Complexity.PT Complexity.PT.Code CandidateWord RectContour

theorem vertices_time : PT CandidateWord.vertices :=
  ChartDrawing.vertices_pt (CatalogPlan.compile_pt PT.id)

def emit (o : Option (List Vertex × Nat)) : Word :=
  o.elim [] (fun r => encodeAGP (r.1.map pack) r.2)

theorem emit_time : PT emit := by
  unfold emit
  exact PT.optionElim PT.id (PT.const []) (OutputTime.serialize_pt (PT.fst PT.snd') (PT.snd PT.snd'))

theorem typed : PT CandidateWord.word := by
  apply PT.of_optionCases (o:=ETRINV.decodeINV) (d:=fun _ => [])
    (f:=fun _ Φ => emit (CandidateWord.vertices Φ)) (PT.decodeINV PT.id) (PT.const [])
    ((emit_time.comp vertices_time).comp PT.snd')
  · intro w h; simp [CandidateWord.word,h]
  · intro w Φ h
    cases hp : CandidateWord.vertices Φ <;> simp [CandidateWord.word,emit,h,hp]

theorem polynomial_time : PolyTime CandidateWord.word := typed.polyTime_word

end ArtGallery.Orthogonal.BoundaryPoint.WordTime
end
