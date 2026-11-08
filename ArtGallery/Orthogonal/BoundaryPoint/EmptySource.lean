module

public import ArtGallery.Orthogonal.BoundaryPoint.CandidateSemantics
public import ArtGallery.Orthogonal.BoundaryPoint.GridParity
public import ArtGallery.Orthogonal.BoundaryPoint.ChimneyCells

/-! # The actual empty-conjunction output is a yes-instance -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.EmptySource
open CandidateWord CorridorProgram RectContour RoomGrid GridParity ChimneyRegion
open ArtGallery.Orthogonal.Hard

def square : List Vertex := [(0,0),(1,0),(1,1),(0,1)]

theorem emitted : vertices [] = some (square,1) := rfl

def cycle : Cycle := ⟨(0,0),[(1,0)],(1,1),(0,1)⟩

private noncomputable def axis : List ℝ := [0,1]
private noncomputable def P : Polygon := ⟨cycle.points.map (gridPt axis axis)⟩
private theorem sortedAxis : axis.IsChain (· < ·) := by norm_num [axis,List.isChain_cons_cons]
private theorem indexes : ∀ p∈cycle.points, p.1<axis.length ∧ p.2<axis.length := by
  change ∀ p∈cycle.points, p.1<2 ∧ p.2<2
  decide +kernel
private theorem ortho : cyclicAxis cycle.points := by decide +kernel
private theorem simple : P.Simple := cycle.simple sortedAxis sortedAxis indexes (by decide +kernel)
private theorem filled : P.filled=cell 0 1 0 1 := by
  let rs : List (Rect Nat) := [(0,1,0,1)]
  have bound : ∀ r∈rs, r.1<axis.length ∧ r.2.1<axis.length ∧
      r.2.2.1<axis.length ∧ r.2.2.2<axis.length := by
    change ∀ r∈([(0,1,0,1)] : List (Rect Nat)), r.1<2 ∧ r.2.1<2 ∧ r.2.2.1<2 ∧ r.2.2.2<2
    decide +kernel
  have all : ∀ i : Fin 5, rowOK cycle.points rs i.val 2=true := by decide +kernel
  rw [show P.filled=cellsR axis axis rs from filled_of_rows sortedAxis sortedAxis indexes ortho simple bound all]
  ext q
  simp [cellsR,rs,axis,cell]

theorem accepted : AGPOrthBoundaryPoint (word (ETRINV.encode [])) := by
  rw [word_of_output emitted]
  apply (encoded_iff square 1).2
  have hp : Polygon.mk (square.map ratPoint)=P := by
    unfold P square cycle Cycle.points gridPt axis ratPoint
    norm_num
  rw [hp]
  refine ⟨simple,grid_orthogonal _ _ _ ortho,?_⟩
  let g : Point := (0,0)
  have bg : g∈P.boundary := by
    refine ⟨0,by decide +kernel,?_⟩
    change (0,0)∈ArtGallery.segment (0,0) (1,0)
    exact Geometry.left_mem_segment _ _
  have fg := Jordan.boundary_subset_filled _ bg
  refine ⟨{g},Finset.card_singleton _,?_,?_⟩
  · simpa using bg
  · intro z hz
    refine ⟨g,by simp,?_⟩
    change ArtGallery.segment g z ⊆ P.filled
    rw [filled,Geometry.segment_eq]
    exact (cell_convex _ _ _ _).segment_subset (filled ▸ fg) (filled ▸ hz)

end ArtGallery.Orthogonal.BoundaryPoint.EmptySource
end
