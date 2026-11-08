module

public import ArtGallery.Spec

/-! # Padding a boundary guard set to an exact cardinality

The boundary of a simple polygon is infinite, so a finite guard set on the boundary with at most
`k` points extends to one with exactly `k` points; extra guards keep every view. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GuardPad

theorem segment_infinite {a b : Point} (h : a≠b) : (ArtGallery.segment a b).Infinite := by
  let f : ℝ → Point := fun t => (a.1+t*(b.1-a.1),a.2+t*(b.2-a.2))
  have inj : Set.InjOn f (Set.Icc 0 1) := by
    intro s _ t _ e
    simp only [f,Prod.mk.injEq] at e
    by_contra ne
    apply h
    have e1 : (s-t)*(b.1-a.1)=0 := by linarith [e.1]
    have e2 : (s-t)*(b.2-a.2)=0 := by linarith [e.2]
    have hs : s-t≠0 := sub_ne_zero.mpr ne
    have x := (mul_eq_zero.mp e1).resolve_left hs
    have y := (mul_eq_zero.mp e2).resolve_left hs
    exact Prod.ext (by linarith) (by linarith)
  have img := (Set.Icc_infinite (zero_lt_one' ℝ)).image inj
  refine img.mono ?_
  rintro p ⟨t,⟨t0,t1⟩,rfl⟩
  exact ⟨t,t0,t1,rfl⟩

theorem boundary_infinite {P : Polygon} (hs : P.Simple) : P.boundary.Infinite := by
  obtain ⟨n3,dist,-⟩ := hs
  have ne : P.vtx 0≠P.vtx ((0+1)%P.n) := by
    intro e
    have := dist 0 ((0+1)%P.n) (by omega) (Nat.mod_lt _ (by omega)) e
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  refine (segment_infinite ne).mono ?_
  intro p hp
  exact ⟨0,by omega,hp⟩

/-- A guard set on the boundary with at most `k` guards extends to one with exactly `k`. -/
theorem pad {P : Polygon} (hs : P.Simple) {S : Finset Point} (hS : P.IsGuardSetOnBoundary (S:Set Point))
    {k : Nat} (hk : S.card≤k) : P.HasGuardSetOnBoundaryOfCard k := by
  classical
  have inf : (P.boundary\(S:Set Point)).Infinite := (boundary_infinite hs).sdiff (Finset.finite_toSet S)
  obtain ⟨T,hT,card⟩ := inf.exists_subset_card_eq (k-S.card)
  have disj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro p hp hpT
    exact (hT hpT).2 hp
  refine ⟨S∪T,by rw [Finset.card_union_of_disjoint disj,card]; omega,?_,?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with h|h
    · exact hS.1 h
    · exact (hT h).1
  · intro z hz
    obtain ⟨g,hg,sees⟩ := hS.2 z hz
    exact ⟨g,Finset.mem_union_left _ hg,sees⟩

end ArtGallery.Orthogonal.BoundaryPoint.GuardPad
end
