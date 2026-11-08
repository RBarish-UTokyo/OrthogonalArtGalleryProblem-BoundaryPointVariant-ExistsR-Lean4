module

public import ArtGallery.Orthogonal.BoundaryPoint.GalleryBoundary
public import ArtGallery.Orthogonal.BoundaryPoint.PinTransport

/-! # An emitted wing in its own coordinates

Translating the emitted gallery by minus the door abscissa puts the wing's chart
polygon in place, and the rest of the gallery meets it exactly in the closed door
segment from `(0,1)` to `(W,1)`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.LocalWing
open Set ChartDrawing ContourJoin RectContour BankCoordinates CompiledSize PinTransport Hardening.Invariance

theorem shift_cancel (d : ℚ) (p : Point) : shift (-d) (shift d p)=p := by
  rw [shift_pt,shift_pt]; ext <;> simp

theorem shift_cancel' (d : ℚ) (p : Point) : shift d (shift (-d) p)=p := by
  rw [shift_pt,shift_pt]; ext <;> simp

theorem unshift_image (d : ℚ) (S : Set Point) : shift (-d) '' (shift d '' S)=S := by
  ext p; constructor
  · rintro ⟨q,⟨u,hu,rfl⟩,rfl⟩; rwa [shift_cancel]
  · intro hp; exact ⟨shift d p,⟨p,hp,rfl⟩,shift_cancel d p⟩

theorem shift_continuous (d : ℚ) : Continuous (shift d) := by
  have : (shift d : Point → Point)=fun p => (p.1+(d:ℝ),p.2) := funext (shift_pt d)
  rw [this]; fun_prop

/-- The local frame of an emitted wing. -/
theorem frame {eqs : List ETRINV.Constraint} {r : CatalogPlan.Row} {j : Nat} {e : Entrance} {v g}
    (path : WingSeparation.emitted eqs r j e) (out : CandidateWord.vertices eqs=some (v,g))
    {t : Template} (hit : (drawOne t (scale eqs) j r.2).1=some e) :
    let s := (1:ℚ)/(scale eqs)
    let args := s::((j:ℚ)*s)::(r.2.map fun (i:Nat) => (i:ℚ)*s)
    let L := BoundaryChart.actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords s))
    ∃ rest : Set Point, IsClosed rest ∧
      (mapPoly (shift (-door j)) (Polygon.mk (v.map ratPoint))).filled=L.filled∪rest ∧
      L.filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) ((W (scale eqs):ℚ),1) := by
  intro s args L
  let d := door j
  have opened : atDoor d (W (scale eqs)) (t.chart.draw (ShapeRefs.join (t.corridor.coords args) (t.room.coords s)))=some e.2 := by
    simp only [drawOne] at hit
    obtain ⟨l,hl,el⟩ := Option.map_eq_some_iff.mp hit
    rw [←el]; exact hl
  obtain ⟨k,rot⟩ := placed opened
  have wingFilled : (RealizedDoors.wing e).filled=shift d '' L.filled := by
    change (Polygon.mk (e.2.map ratPoint)).filled=_
    rw [rot,Existence.filled_rotate,filled_mapPoly]; rfl
  let J := GalleryBoundary.joined path out
  refine ⟨shift (-d) '' J.rest,?_,?_,?_⟩
  · have : shift (-d) '' J.rest=shift d ⁻¹' J.rest := by
      ext p; constructor
      · rintro ⟨q,hq,rfl⟩; simpa [shift_cancel'] using hq
      · intro hp; exact ⟨shift d p,hp,shift_cancel d p⟩
    rw [this]; exact J.closed.preimage (shift_continuous d)
  · rw [filled_mapPoly,J.fill,Set.image_union,wingFilled,unshift_image]
  · have inj : Function.Injective (shift (-d)) := (shift (-d)).injective
    have : L.filled=shift (-d) '' (RealizedDoors.wing e).filled := by
      rw [wingFilled,unshift_image]
    rw [this,←Set.image_inter inj,J.contact,image_segment']
    congr 1 <;> rw [shift_pt] <;> ext <;> simp [d,BankCoordinates.door]

end ArtGallery.Orthogonal.BoundaryPoint.LocalWing
end
