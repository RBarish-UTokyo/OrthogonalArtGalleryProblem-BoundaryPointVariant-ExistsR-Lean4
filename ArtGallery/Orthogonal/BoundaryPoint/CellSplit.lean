module

public import ArtGallery.Orthogonal.BoundaryPoint.CoverAssume

/-! # A cell split by a line through the guard

Two chain certificates from the same guard segment whose only assumed ends are one node `w`, with
opposite signs, together certify the whole cell: every sightline has `det(g,z,w) ≥ 0` or `≤ 0`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CellSplit
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CoverChain CoverAssume ArtGallery.Orthogonal.Hard

def splitOK (C : Chart) (g₀ g₁ w : Index) (x x' y y' : Nat) (cA cB : CertA) : Bool :=
  cA.ok C g₀ g₁ x x' y y' && cB.ok C g₀ g₁ x x' y y' &&
    cA.assumed.all (· == (w,true)) && cB.assumed.all (· == (w,false))

theorem split_sound {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {g₀ g₁ w : Index} {x x' y y' : Nat} {cA cB : CertA} (h : splitOK C g₀ g₁ w x x' y y' cA cB=true)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) : (C.poly X Y).Sees g z := by
  simp only [splitOK,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at h
  obtain ⟨⟨⟨okA,okB⟩,aA⟩,aB⟩ := h
  rcases le_total 0 (ArtGallery.det g z (gridPt X Y w)) with h0|h0
  · refine CertA.sound G okA hg hz fun e he => ?_
    rw [aA e he]; simp only [Holds,ite_true,one_mul]; exact h0
  · refine CertA.sound G okB hg hz fun e he => ?_
    rw [aB e he]; simp only [Holds,Bool.false_eq_true,ite_false]; linarith

end ArtGallery.Orthogonal.BoundaryPoint.CellSplit
end
