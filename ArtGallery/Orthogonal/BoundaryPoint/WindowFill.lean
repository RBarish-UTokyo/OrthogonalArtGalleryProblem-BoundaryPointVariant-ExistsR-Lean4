module

public import ArtGallery.Existence.Arc
public import ArtGallery.Existence.Split
public import ArtGallery.Orthogonal.BoundaryPoint.WindowSplice

/-! # The filled set of a cycle made by a single-window splice
Parity is additive on the complementary arcs. Away from all three boundaries
their intersection is empty, because any common point belongs to the door
on the first piece's boundary. The pieces and the joined polygon are regular
closed Jordan regions, so the equality extends to the removed door as well. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WindowFill
open Set Jordan Existence

private theorem dense_off {P : Polygon} (h : P.Simple) : Dense P.boundaryᶜ := by
  have front : frontier P.filled=P.boundary := by
    rw [frontier,(isClosed_filled P).closure_eq,interior_filled h]
    ext z
    have sub : z∈P.boundary → z∈P.filled := fun hz => Or.inl hz
    change (z∈P.filled ∧ ¬(z∈P.filled ∧ z∉P.boundary)) ↔ z∈P.boundary
    tauto
  rw [← interior_eq_empty_iff_dense_compl,← front]
  exact interior_frontier (isClosed_filled P)

private theorem recover {P : Polygon} (h : P.Simple) {U D : Set Point} (closed : IsClosed U)
    (dense : Dense D) (same : ∀ z∈P.filled,z∈D → z∈U) : P.filled⊆U := by
  have inside := dense.open_subset_closure_inter (isOpen_filled_sdiff_boundary h)
  have part : (P.filled\P.boundary)∩D⊆U := fun z hz => same z hz.1.1 hz.2
  exact (filled_subset_closure_interior h).trans (closure_minimal (inside.trans (closure_minimal part closed)) closed)

theorem parity_union {P A B : Polygon} (hp : P.Simple) (ha : A.Simple) (hb : B.Simple)
    (touch : A.filled∩B.filled⊆A.boundary)
    (split : ∀ z, parity P z=Bool.xor (parity A z) (parity B z)) :
    P.filled=A.filled∪B.filled := by
  let D := (P.boundaryᶜ∩A.boundaryᶜ)∩B.boundaryᶜ
  have dense : Dense D := ((dense_off hp).inter_of_isOpen_left (dense_off ha)
    (isOpen_boundary_compl P)).inter_of_isOpen_right (dense_off hb) (isOpen_boundary_compl B)
  have agree (z : Point) (hz : z∈D) : z∈P.filled ↔ z∈A.filled∪B.filled := by
    have pNot : z∉P.boundary := hz.1.1
    have aNot : z∉A.boundary := hz.1.2
    have bNot : z∉B.boundary := hz.2
    have misses : ¬(parity A z=true ∧ parity B z=true) :=
      fun h => aNot (touch ⟨(mem_filled_iff ha aNot).2 h.1,(mem_filled_iff hb bNot).2 h.2⟩)
    rw [mem_filled_iff hp pNot,split,Set.mem_union,mem_filled_iff ha aNot,mem_filled_iff hb bNot]
    cases p : parity A z <;> cases q : parity B z <;> simp_all
  apply Set.Subset.antisymm
  · exact recover hp ((isClosed_filled A).union (isClosed_filled B)) dense (fun z h d => (agree z d).1 h)
  · exact Set.union_subset
      (recover ha (isClosed_filled P) dense (fun z h d => (agree z d).2 (Or.inl h)))
      (recover hb (isClosed_filled P) dense (fun z h d => (agree z d).2 (Or.inr h)))

theorem arcs {P : Polygon} (hp : P.Simple) (s L : Nat) (hl : L≤P.n)
    (ha : (P.arc s L).Simple) (hb : (P.arc ((s+L)%P.n) (P.n-L)).Simple)
    (touch : (P.arc s L).filled∩(P.arc ((s+L)%P.n) (P.n-L)).filled⊆(P.arc s L).boundary) :
    P.filled=(P.arc s L).filled∪(P.arc ((s+L)%P.n) (P.n-L)).filled :=
  parity_union hp ha hb touch (parity_split P s L hl)

theorem attach {P A B : Polygon} (hp : P.Simple) (ha : A.Simple) (hb : B.Simple)
    (touch : A.filled∩B.filled⊆A.boundary) (window : Convex ℝ (A.filled∩B.filled))
    (split : ∀ z, parity P z=Bool.xor (parity A z) (parity B z)) :
    WindowTree.Attachments A.filled P.filled := by
  rw [parity_union hp ha hb touch split]
  exact .attach (.start (isClosed_filled A)) (isClosed_filled B) window

end ArtGallery.Orthogonal.BoundaryPoint.WindowFill
end
