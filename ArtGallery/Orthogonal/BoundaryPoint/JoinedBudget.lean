module

public import ArtGallery.Vis.Pinning
public import Mathlib.Data.Fintype.Sum

/-! # Counting on a hub with arbitrarily many one-door wings

Buried hub anchors supply the first lower bound. Once every private guard
is localized, the remaining hub witnesses can only be served from the hub.
The second count then uses the hub's stronger anchors. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.JoinedBudget
open Set

structure Group (ι : Type) where
  w : ι → Fin 3 → Point
  anc : ι → Fin 3
  spot : ι → Set Point

def Group.mark {ι} (a : Group ι) (i : ι) := a.w i (a.anc i)

private theorem direct {ι : Type} [Fintype ι] {P : Polygon} {G : Finset Point} {Ω : Set Point}
    (hG : (G:Set Point) ⊆ Ω) (cov : ∀ q∈P.filled, ∃ g∈(G:Set Point), P.Sees g q)
    (W : ι → Set Point) (m : ι → Point) (spot : ι → Set Point)
    (hw : ∀ i, W i ⊆ P.filled) (hm : ∀ i,m i ∈ W i)
    (hforeign : ∀ i j, i≠j → ∀ g∈Ω, P.Sees g (m i) → ∀ w∈W j, ¬P.Sees g w)
    (hloc : ∀ i, ∀ g∈Ω, (∀ w∈W i,P.Sees g w) → g∈spot i)
    (hb : G.card≤Fintype.card ι) :
    G.card=Fintype.card ι ∧
    (∀ i, ∃ g∈G, P.Sees g (m i) ∧ g∈spot i ∧ ∀ p∈G,P.Sees p (m i) → p=g) ∧
    (∀ g∈G,∃ i,P.Sees g (m i) ∧ g∈spot i) := by
  have hm' (i) := hw i (hm i)
  have sep (i j : ι) (ne : i≠j) (g : Point) (hg : g∈Ω) (hs : P.Sees g (m i)) :=
    hforeign i j ne g hg hs _ (hm j)
  have hc := le_antisymm hb (P.card_le_of_witnesses_on hG cov m hm' sep)
  refine ⟨hc,?_⟩
  apply P.guards_pinned_on hG cov m hm' sep hc W hw spot hloc (fun _ _ => False)
  · exact ⟨fun i => Acc.intro i (fun _ h => h.elim)⟩
  · rintro _ _ _ h; exact h.elim
  · exact fun i j ne _ w hw g hg hs => hforeign j i ne g hg hs w hw

structure Geometry (H J K : Type) (P : Polygon) (a : Group H) (b : Group J) where
  hub : Set Point
  wing : K → Set Point
  site : J → K
  buried : H → Point
  buriedFilled : ∀ i, buried i ∈ P.filled
  hubFilled : ∀ i j, a.w i j ∈ P.filled
  privFilled : ∀ i j, b.w i j ∈ P.filled
  hubWing : ∀ k, Disjoint hub (wing k)
  wings : ∀ k l, k≠l → Disjoint (wing k) (wing l)
  /-- The closed hub door misses each of these deep witnesses. -/
  buriedView : ∀ i, ∀ g∈P.boundary, P.Sees g (buried i) → g∈hub
  privateView : ∀ i j, ∀ g∈P.boundary, P.Sees g (b.w i j) → g∈wing (site i)
  /-- All four exclusion conditions below concern one component at a time. -/
  buriedSeparate : ∀ i j, i≠j → ∀ g∈P.boundary, g∈hub → P.Sees g (buried i) → ¬P.Sees g (buried j)
  hubSeparate : ∀ i j, i≠j → ∀ g∈P.boundary, g∈hub → P.Sees g (a.mark i) → ∀ t, ¬P.Sees g (a.w j t)
  privateSeparate : ∀ i j, i≠j → site i=site j → ∀ g∈P.boundary, g∈wing (site i) →
    P.Sees g (b.mark i) → ∀ t, ¬P.Sees g (b.w j t)
  pinnedMissHub : ∀ i, ∀ g∈b.spot i, ∀ j t, ¬P.Sees g (a.w j t)
  hubSpot : ∀ i, ∀ g∈P.boundary, g∈hub → (∀ j,P.Sees g (a.w i j)) → g∈a.spot i
  privateSpot : ∀ i, ∀ g∈P.boundary, g∈wing (site i) → (∀ j,P.Sees g (b.w i j)) → g∈b.spot i

theorem force {H J K : Type} [Fintype H] [Fintype J] {P : Polygon}
    {a : Group H} {b : Group J} (d : Geometry H J K P a b) (G : Finset Point)
    (hc : P.IsGuardSetOnBoundary (G:Set Point)) (hb : G.card≤Fintype.card H+Fintype.card J) :
    G.card=Fintype.card H+Fintype.card J ∧
    (∀ i : H⊕J, ∃ g∈G, P.Sees g (Sum.elim a.mark b.mark i) ∧
      g∈Sum.elim a.spot b.spot i ∧ ∀ p∈G,P.Sees p (Sum.elim a.mark b.mark i) → p=g) ∧
    (∀ g∈G,∃ i : H⊕J,P.Sees g (Sum.elim a.mark b.mark i) ∧ g∈Sum.elim a.spot b.spot i) := by
  have hb' : G.card≤Fintype.card (H⊕J) := by simpa only [Fintype.card_sum] using hb
  have pp (i j : J) (hne : i≠j) (g : Point) (hg : g∈P.boundary)
      (h : P.Sees g (b.mark i)) (t : Fin 3) : ¬P.Sees g (b.w j t) := by
    have hgi := d.privateView i (b.anc i) g hg h
    by_cases eq : d.site i=d.site j
    · exact d.privateSeparate i j hne eq g hg hgi h t
    · exact fun h₂ => Set.disjoint_left.mp (d.wings _ _ eq) hgi (d.privateView j t g hg h₂)
  let B : H⊕J → Set Point := Sum.elim (fun i => {d.buried i}) (fun i => range (b.w i))
  let U : H⊕J → Set Point := Sum.elim (fun _ => d.hub) b.spot
  let m : H⊕J → Point := Sum.elim d.buried b.mark
  have first := direct hc.1 hc.2 B m U
  have bval (i) : B i ⊆ P.filled := by
    cases i with
    | inl h => rintro w rfl; exact d.buriedFilled h
    | inr j => rintro w ⟨t,rfl⟩; exact d.privFilled j t
  have bmark (i) : m i∈B i := by cases i with
    | inl h => exact rfl
    | inr j => exact ⟨b.anc j,rfl⟩
  have fsep : ∀ i j, i≠j → ∀ g∈P.boundary, P.Sees g (m i) → ∀ w∈B j, ¬P.Sees g w := by
    intro i j ne g hg h w hw
    cases i with
    | inl i =>
      have hH := d.buriedView i g hg h
      cases j with
      | inl j => obtain rfl := hw; exact d.buriedSeparate i j (fun e => ne (congrArg Sum.inl e)) g hg hH h
      | inr j => obtain ⟨t,rfl⟩ := hw; exact fun hs => Set.disjoint_left.mp (d.hubWing _) hH (d.privateView j t g hg hs)
    | inr i =>
      cases j with
      | inl j => obtain rfl := hw; exact fun hs => Set.disjoint_left.mp (d.hubWing _) (d.buriedView j g hg hs) (d.privateView i _ g hg h)
      | inr j => obtain ⟨t,rfl⟩ := hw; exact pp i j (fun e => ne (congrArg Sum.inr e)) g hg h t
  have floc : ∀ i, ∀ g∈P.boundary, (∀ w∈B i,P.Sees g w) → g∈U i := by
    intro i g hg h
    cases i with
    | inl i => exact d.buriedView i g hg (h _ rfl)
    | inr j =>
      have all (t) := h _ (show b.w j t∈B (.inr j) from ⟨t,rfl⟩)
      exact d.privateSpot j g hg (d.privateView j _ g hg (all 0)) all
  have firstStage := first bval bmark fsep floc hb'
  let Ω : Set Point := {g | g∈P.boundary ∧ (g∈d.hub ∨ ∃ j,g∈b.spot j)}
  have hΩ : (G:Set Point)⊆Ω := by
    intro g hg
    obtain ⟨i,_,hS⟩ := firstStage.2.2 g hg
    refine ⟨hc.1 hg,?_⟩
    cases i with
    | inl _ => exact Or.inl hS
    | inr j => exact Or.inr ⟨j,hS⟩
  have onlyHub {g : Point} (hg : g∈Ω) (i t) (h : P.Sees g (a.w i t)) : g∈d.hub := by
    rcases hg.2 with hH | ⟨j,hj⟩
    · exact hH
    · exact (d.pinnedMissHub j g hj i t h).elim
  let W : H⊕J → Set Point := Sum.elim (fun i => range (a.w i)) (fun j => range (b.w j))
  have final := direct hΩ hc.2 W (Sum.elim a.mark b.mark) (Sum.elim a.spot b.spot)
  have wf (i) : W i⊆P.filled := by
    cases i with
    | inl h => rintro _ ⟨t,rfl⟩; exact d.hubFilled h t
    | inr j => rintro _ ⟨t,rfl⟩; exact d.privFilled j t
  have wm (i) : Sum.elim a.mark b.mark i∈W i := by
    cases i with
    | inl h => exact ⟨a.anc h,rfl⟩
    | inr j => exact ⟨b.anc j,rfl⟩
  have se : ∀ i j, i≠j → ∀ g∈Ω, P.Sees g (Sum.elim a.mark b.mark i) → ∀ w∈W j, ¬P.Sees g w := by
    intro i j ne g hg h w hw
    cases i with
    | inl i =>
      have hH := onlyHub hg i (a.anc i) h
      cases j with
      | inl j => obtain ⟨t,rfl⟩ := hw; exact d.hubSeparate i j (fun e => ne (congrArg Sum.inl e)) g hg.1 hH h t
      | inr j => obtain ⟨t,rfl⟩ := hw; exact fun hs => Set.disjoint_left.mp (d.hubWing _) hH (d.privateView j t g hg.1 hs)
    | inr i =>
      cases j with
      | inl j =>
        obtain ⟨t,rfl⟩ := hw
        exact fun hs => Set.disjoint_left.mp (d.hubWing _) (onlyHub hg j t hs) (d.privateView i _ g hg.1 h)
      | inr j => obtain ⟨t,rfl⟩ := hw; exact pp i j (fun e => ne (congrArg Sum.inr e)) g hg.1 h t
  have loc : ∀ i, ∀ g∈Ω, (∀ w∈W i,P.Sees g w) → g∈Sum.elim a.spot b.spot i := by
    intro i g hg h
    cases i with
    | inl i =>
      have all (t) := h _ (show a.w i t∈W (.inl i) from ⟨t,rfl⟩)
      exact d.hubSpot i g hg.1 (onlyHub hg i 0 (all 0)) all
    | inr i =>
      have all (t) := h _ (show b.w i t∈W (.inr i) from ⟨t,rfl⟩)
      exact d.privateSpot i g hg.1 (d.privateView i _ g hg.1 (all 0)) all
  simpa only [Fintype.card_sum] using final wf wm se loc hb'

end ArtGallery.Orthogonal.BoundaryPoint.JoinedBudget
end
