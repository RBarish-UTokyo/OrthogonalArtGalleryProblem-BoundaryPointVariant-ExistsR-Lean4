module

public import ArtGallery.Orthogonal.BoundaryPoint.SingleWindow

/-! # Several one-window attachments and horizontal-door exclusions

Each construction step joins a closed wing to the region built so far at a
convex interface. Sight between any two points of a previously attached room
can be checked before subsequent wings are attached.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WindowTree

open Set

/-- A finite sequence of closed additions to one fixed starting region. -/
inductive Attachments (base : Set Point) : Set Point → Prop
  | start (hc : IsClosed base) : Attachments base base
  | attach {previous wing : Set Point} (prior : Attachments base previous)
      (closedWing : IsClosed wing) (window : Convex ℝ (previous ∩ wing)) :
      Attachments base (previous ∪ wing)

/-- Every intermediate region is closed. -/
theorem Attachments.closed {base total : Set Point} (tree : Attachments base total) :
    IsClosed total := by
  induction tree with
  | start hc => exact hc
  | attach _ closedWing _ h => exact h.union closedWing

/-- Former points persist under further attachments. -/
theorem Attachments.subset {base total : Set Point} (tree : Attachments base total) :
    base ⊆ total := by
  induction tree with
  | start _ => exact Subset.rfl
  | attach _ _ _ h => exact h.trans subset_union_left

/-- A segment with both endpoints in the starting room stays there when
it lies in the final union. -/
theorem Attachments.segment_iff {base total : Set Point} (tree : Attachments base total)
    {a b : Point} (ha : a ∈ base) (hb : b ∈ base) :
    segment a b ⊆ total ↔ segment a b ⊆ base := by
  constructor
  · induction tree with
    | start _ => exact id
    | attach prior cw window ih =>
      exact fun hs => ih (SingleWindow.segment_subset_room prior.closed cw window
        (prior.subset ha) (prior.subset hb) hs)
  · exact fun hs => hs.trans tree.subset

/-- Local visibility transfers through any number of one-window additions. -/
theorem Attachments.sees_iff {room P : Polygon} (tree : Attachments room.filled P.filled)
    {a b : Point} (ha : a ∈ room.filled) (hb : b ∈ room.filled) :
    P.Sees a b ↔ room.Sees a b := tree.segment_iff ha hb

/-- A sightline to a target at interface height from a guard at another
height can reach that height only at the target. This eliminates a
foreign guard when the target lies beyond the door interval. -/
theorem not_sees_target_on_door_line {P : Polygon} {R H : Set Point}
    (hcover : P.filled ⊆ R ∪ H) (hR : IsClosed R) (hH : IsClosed H)
    {height : ℝ} (hlevel : ∀ q ∈ R ∩ H, q.2 = height) {a b : Point}
    (ha : a ∈ R) (hb : b ∈ H) (haht : a.2 ≠ height) (hbht : b.2 = height)
    (hoff : b ∉ R ∩ H) : ¬ P.Sees a b := by
  intro hs
  obtain ⟨q, hq, hdoor⟩ := SingleWindow.segment_meets_window hR hH ha hb (hs.trans hcover)
  obtain ⟨t, _, _, rfl⟩ := hq
  change Geometry.lerp a b t ∈ R ∩ H at hdoor
  have hv := hlevel _ hdoor
  rw [Geometry.lerp_snd, hbht] at hv
  have he : (t-1)*(height-a.2)=0 := by nlinarith only [hv]
  have ht : t = 1 := sub_eq_zero.1 ((mul_eq_zero.1 he).resolve_right (sub_ne_zero.2 haht.symm))
  rw [ht, Geometry.lerp_one] at hdoor
  exact hoff hdoor

/-- A sightline whose endpoints are strictly above a horizontal interface
between closed regions cannot meet that interface. -/
theorem not_sees_above_door {P : Polygon} {R H : Set Point}
    (hcover : P.filled ⊆ R ∪ H) (hR : IsClosed R) (hH : IsClosed H)
    {height : ℝ} (hlevel : ∀ q ∈ R ∩ H, q.2 ≤ height) {a b : Point}
    (ha : a ∈ R) (hb : b ∈ H) (haht : height < a.2) (hbht : height < b.2) :
    ¬ P.Sees a b := by
  intro hs
  obtain ⟨q, hq, hdoor⟩ := SingleWindow.segment_meets_window hR hH ha hb (hs.trans hcover)
  obtain ⟨t, ht0, ht1, rfl⟩ := hq
  change Geometry.lerp a b t ∈ R ∩ H at hdoor
  have hv := hlevel _ hdoor
  rw [Geometry.lerp_snd] at hv
  rcases le_total a.2 b.2 with hab | hba
  · nlinarith only [hv, haht, mul_nonneg ht0 (sub_nonneg.2 hab)]
  · nlinarith only [hv, hbht, mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hba)]

end ArtGallery.Orthogonal.BoundaryPoint.WindowTree
end
