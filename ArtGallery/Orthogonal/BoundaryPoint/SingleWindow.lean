module

public import ArtGallery.Geometry.Basic
public import ArtGallery.Jordan.Filled

/-! # Internal visibility survives joining through a convex window

A room and the rest of a polygon are closed regions whose intersection is a
single segment. A sightline between room points in the union lies entirely in
the room. More generally the common interface may be any convex set.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SingleWindow

open Set

/-- In a closed cover of an interval, a subinterval from one set to the
other has a parameter belonging to both sets. -/
private theorem common_parameter {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    {s t : ℝ} (hst : s ≤ t) (hCover : Icc s t ⊆ A ∪ B) (hs : s ∈ A) (ht : t ∈ B) :
    ∃ u ∈ Icc s t, u ∈ A ∩ B :=
  isPreconnected_closed_iff.1 isPreconnected_Icc A B hA hB hCover
    ⟨s, ⟨le_rfl, hst⟩, hs⟩ ⟨t, ⟨hst, le_rfl⟩, ht⟩

/-- A sightline from the room to the other region meets their common door.
This part holds for every closed interface. -/
theorem segment_meets_window {R H : Set Point} (hR : IsClosed R) (hH : IsClosed H)
    {a b : Point} (ha : a ∈ R) (hb : b ∈ H) (hall : segment a b ⊆ R ∪ H) :
    ∃ q ∈ segment a b, q ∈ R ∩ H :=
  isPreconnected_closed_iff.1 (Geometry.segment_convex a b).isPreconnected R H hR hH hall
    ⟨a, Geometry.left_mem_segment _ _, ha⟩ ⟨b, Geometry.right_mem_segment _ _, hb⟩

/-- Any straight segment between two room points in the union stays in the
room when its intersection with the other closed region is convex. -/
theorem segment_subset_room {R H : Set Point} (hR : IsClosed R) (hH : IsClosed H)
    (hwindow : Convex ℝ (R ∩ H)) {a b : Point} (ha : a ∈ R) (hb : b ∈ R)
    (hall : segment a b ⊆ R ∪ H) : segment a b ⊆ R := by
  let f : ℝ →ᵃ[ℝ] Point := AffineMap.lineMap a b
  have hf : Continuous f := by
    change Continuous (fun t : ℝ => AffineMap.lineMap a b t)
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hcover : Icc (0 : ℝ) 1 ⊆ (f ⁻¹' R) ∪ (f ⁻¹' H) := by
    intro t ht
    apply hall
    rw [Geometry.segment_eq]
    exact lineMap_mem_segment ℝ a b ht
  have hf0 : 0 ∈ f ⁻¹' R := by simpa [f] using ha
  have hf1 : 1 ∈ f ⁻¹' R := by simpa [f] using hb
  intro z hz
  rw [Geometry.segment_eq, segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  change t ∈ f ⁻¹' R
  by_contra h
  have htH := (hcover ht).resolve_left h
  obtain ⟨s, hs, hs_w⟩ := common_parameter (hR.preimage hf) (hH.preimage hf) ht.1
    (fun u hu => hcover ⟨hu.1, hu.2.trans ht.2⟩) hf0 htH
  obtain ⟨u, hu, hu_w⟩ := common_parameter (hH.preimage hf) (hR.preimage hf) ht.2
    (fun u hu => Or.comm.mp (hcover ⟨ht.1.trans hu.1, hu.2⟩)) htH hf1
  have hparams : Convex ℝ (f ⁻¹' (R ∩ H)) := hwindow.affine_preimage f
  have htW := hparams.ordConnected.out' (show s ∈ f ⁻¹' (R ∩ H) from hs_w)
    (show u ∈ f ⁻¹' (R ∩ H) from ⟨hu_w.2, hu_w.1⟩) (show t ∈ Icc s u from ⟨hs.2, hu.1⟩)
  exact h htW.1

/-- The internal visibility predicate of the room polygon agrees with
that of the joined polygon at any two room points. -/
theorem sees_iff {P room : Polygon} {H : Set Point}
    (hjoined : P.filled = room.filled ∪ H) (hH : IsClosed H)
    (hwindow : Convex ℝ (room.filled ∩ H)) {a b : Point}
    (ha : a ∈ room.filled) (hb : b ∈ room.filled) :
    P.Sees a b ↔ room.Sees a b := by
  change (segment a b ⊆ P.filled) ↔ segment a b ⊆ room.filled
  rw [hjoined]
  exact ⟨segment_subset_room (Jordan.isClosed_filled _) hH hwindow ha hb,
    fun h => h.trans subset_union_left⟩

/-- A cross-room sightline intersects the window at a point visible inside
the room from its target. A local exclusion for every window point hence
applies to an arbitrary guard in the other region. -/
theorem exists_visible_window_point {P room : Polygon} {H : Set Point}
    (hjoined : P.filled = room.filled ∪ H) (hH : IsClosed H)
    (hwindow : Convex ℝ (room.filled ∩ H)) {a b : Point}
    (ha : a ∈ room.filled) (hb : b ∈ H) (hs : P.Sees a b) :
    ∃ q ∈ room.filled ∩ H, q ∈ segment a b ∧ room.Sees a q := by
  have hall : segment a b ⊆ room.filled ∪ H := hjoined ▸ hs
  obtain ⟨q,hq,hW⟩ := segment_meets_window (Jordan.isClosed_filled _) hH ha hb hall
  refine ⟨q,hW,hq,(sees_iff hjoined hH hwindow ha hW.1).1 ?_⟩
  exact (Geometry.segment_subset_of_convex (Geometry.segment_convex a b)
    (Geometry.left_mem_segment _ _) hq).trans hs

end ArtGallery.Orthogonal.BoundaryPoint.SingleWindow
end
