module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomCoordinates
public import ArtGallery.Jordan.SegmentFacts

/-! # Guard segments and witnesses on parameterized room boundaries

The edge index in each mark is supplied by the generator. Visibility is a
separate obligation. This checker certifies the entire continuous guard
segment on the actual polygon boundary, including its endpoints. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GridPins
open Set RoomGrid ArtGallery.Orthogonal.Hard

abbrev Mark := Nat × (Index × Index)

def requirements (roles : List (List Index)) : List (Index × Index) := roles.flatMap fun
  | [g,a,b,x,y,z] => [(g,g),(a,b),(x,x),(y,y),(z,z)]
  | _ => []

def orderedHit (a b p : Index) : Prop :=
  (a.1=b.1 ∧ p.1=a.1 ∧ a.2≤p.2 ∧ p.2≤b.2) ∨
  (a.2=b.2 ∧ p.2=a.2 ∧ a.1≤p.1 ∧ p.1≤b.1)

instance (a b p : Index) : Decidable (orderedHit a b p) := by unfold orderedHit; infer_instance

def small (nx ny : Nat) (p : Index) : Prop := p.1 < nx ∧ p.2 < ny
instance (nx ny : Nat) (p : Index) : Decidable (small nx ny p) := by unfold small; infer_instance

def markOk (nx ny : Nat) (cycle : List Index) (m : Mark) : Bool :=
  let a := cycle.getD m.1 (0,0)
  let b := cycle.getD ((m.1+1)%cycle.length) (0,0)
  decide (m.1 < cycle.length ∧ small nx ny a ∧ small nx ny b ∧
    small nx ny m.2.1 ∧ small nx ny m.2.2 ∧
    (orderedHit a b m.2.1 ∨ orderedHit b a m.2.1) ∧
    (orderedHit a b m.2.2 ∨ orderedHit b a m.2.2))

theorem horizontal {a b p : Point} (h : a.2=b.2) (hz : p.2=a.2)
    (h₀ : a.1≤p.1) (h₁ : p.1≤b.1) : p ∈ segment a b := by
  rcases eq_or_lt_of_le (h₀.trans h₁) with e | e
  · have hp : p=a := Prod.ext (le_antisymm (by simpa [← e] using h₁) h₀) hz
    rw [hp]; exact Geometry.left_mem_segment _ _
  · rw [Jordan.mem_segment_iff_of_lt e]
    exact ⟨h₀,h₁,by rw [hz,h]; ring⟩

private theorem along {a b p : Index} {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    (ha : small xs.length ys.length a) (hb : small xs.length ys.length b) (hp : small xs.length ys.length p)
    (h : orderedHit a b p) : gridPt xs ys p ∈ segment (gridPt xs ys a) (gridPt xs ys b) := by
  have mx := (strictMonoOn_getD hx).monotoneOn
  have my := (strictMonoOn_getD hy).monotoneOn
  rcases h with ⟨h₁,h₂,h₃,h₄⟩ | ⟨h₁,h₂,h₃,h₄⟩
  · exact Jordan.mem_segment_of_vertical (congrArg (fun i => xs.getD i 0) h₁)
      (congrArg (fun i => xs.getD i 0) h₂) (my ha.2 hp.2 h₃) (my hp.2 hb.2 h₄)
  · exact horizontal (congrArg (fun i => ys.getD i 0) h₁)
      (congrArg (fun i => ys.getD i 0) h₂) (mx ha.1 hp.1 h₃) (mx hp.1 hb.1 h₄)

theorem whole_segment {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {cycle : List Index} {m : Mark} (hm : markOk xs.length ys.length cycle m = true) :
    segment (gridPt xs ys m.2.1) (gridPt xs ys m.2.2) ⊆
      (Polygon.mk (cycle.map (gridPt xs ys))).boundary := by
  obtain ⟨hi,ha,hb,hp,hq,h₁,h₂⟩ := of_decide_eq_true hm
  let i := m.1
  let j := (i+1)%cycle.length
  let a := cycle.getD i (0,0)
  let b := cycle.getD j (0,0)
  let f := gridPt xs ys
  have hit (p : Index) (hs : small xs.length ys.length p) (h : orderedHit a b p ∨ orderedHit b a p) :
      f p ∈ segment (f a) (f b) := by
    rcases h with h|h
    · exact along hx hy ha hb hs h
    · rw [Geometry.segment_comm]; exact along hx hy hb ha hs h
  have sub := Geometry.segment_subset_of_convex (Geometry.segment_convex (f a) (f b))
    (hit _ hp h₁) (hit _ hq h₂)
  let P : Polygon := ⟨cycle.map f⟩
  have hn : P.n=cycle.length := by simp [P,Polygon.n]
  have hi' : i<cycle.length := hi
  have hj : j<cycle.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hi')
  have atI (k : Nat) (h : k<cycle.length) : P.vtx k=f (cycle.getD k (0,0)) := by
    change (cycle.map f).getD k (0,0) = _
    rw [List.getD_eq_getElem (l := cycle.map f) (d := (0,0)) (by simpa using h),
        List.getD_eq_getElem (l := cycle) (d := (0,0)) h,List.getElem_map]
  intro z hz
  refine ⟨i,hn ▸ hi',?_⟩
  change z ∈ segment (P.vtx i) (P.vtx ((i+1)%P.n))
  rw [hn,atI i hi',atI j hj]
  exact sub hz

theorem all_segments {xs ys : List ℝ} (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    {cycle : List Index} {marks : List Mark}
    (h : marks.all (markOk xs.length ys.length cycle) = true) :
    ∀ p ∈ marks.map Prod.snd, segment (gridPt xs ys p.1) (gridPt xs ys p.2) ⊆
      (Polygon.mk (cycle.map (gridPt xs ys))).boundary := by
  rintro p hp
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hp
  exact whole_segment hx hy (List.all_eq_true.mp h _ hm)

end ArtGallery.Orthogonal.BoundaryPoint.GridPins
end
