module

public import ArtGallery.Orthogonal.BoundaryPoint.CandidateWord
public import ArtGallery.PTime.AGPinER

/-! # Meaning of every word emitted by the executable construction

The registry decoder recovers the actual rational vertices and the computed
budget uniquely. A failed parse or contour produces a word outside the
target language. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CandidateWord
open Complexity RectContour CorridorProgram

theorem nil_rejected : ¬AGPOrthBoundaryPoint [] := by
  rintro ⟨V,g,h,_⟩
  cases V <;> simp [encodeAGP,encodeList] at h

theorem encoded_iff (v : List Vertex) (g : Nat) :
    let P := Polygon.mk (v.map ratPoint)
    AGPOrthBoundaryPoint (encodeAGP (v.map pack) g) ↔
      P.Simple ∧ P.Orthogonal ∧ P.HasGuardSetOnBoundaryOfCard g := by
  have points : (v.map pack).map FracPoint.toPoint = v.map ratPoint := by
    simp only [List.map_map,Function.comp_def,pack_point]
  constructor
  · rintro ⟨V,b,h,_,hs,ho,hg⟩
    obtain ⟨rfl,rfl⟩ := encodeAGP_inj h.symm
    rw [points] at hs ho hg
    exact ⟨hs,ho,hg⟩
  · rintro ⟨hs,ho,hg⟩
    refine ⟨v.map pack,g,rfl,?_,?_⟩
    · intro p hp
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hp
      exact pack_valid z
    · rw [points]; exact ⟨hs,ho,hg⟩

theorem output_iff (w : Word) : AGPOrthBoundaryPoint (word w) ↔
    ∃ Φ v g, ETRINV.decodeINV w = some Φ ∧ vertices Φ = some (v,g) ∧
      let P := Polygon.mk (v.map ratPoint)
      P.Simple ∧ P.Orthogonal ∧ P.HasGuardSetOnBoundaryOfCard g := by
  cases he : ETRINV.decodeINV w with
  | none => simp [word,he,nil_rejected]
  | some Φ =>
    cases hv : vertices Φ with
    | none => simp [word,he,hv,nil_rejected]
    | some vg =>
      obtain ⟨v,g⟩ := vg
      simp [word,he,hv,encoded_iff]

end ArtGallery.Orthogonal.BoundaryPoint.CandidateWord
end
