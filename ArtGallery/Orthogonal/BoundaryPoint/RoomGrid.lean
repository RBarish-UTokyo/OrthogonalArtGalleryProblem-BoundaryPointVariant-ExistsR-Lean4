module

public import ArtGallery.Orthogonal.Hard.OrthChain
public import ArtGallery.Orthogonal.Spec
public import Mathlib.Tactic.Linarith

/-! # Closed orthogonal room boundaries on strictly ordered parameter grids

Three open-chain checks on integer grid indices certify the whole cyclic
boundary. Positive polynomial gaps preserve the order of the grids at
every allowed scale, including gaps that tend to zero. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomGrid

open Set ArtGallery.Stade.Chain ArtGallery.Orthogonal.Hard

abbrev Index := Nat × Nat

structure Cycle where
  first : Index
  middle : List Index
  beforeLast : Index
  last : Index

def Cycle.points (c : Cycle) : List Index := (c.first::c.middle) ++ [c.beforeLast,c.last]
def Cycle.longTurn (c : Cycle) : List Index := c.last::c.first::(c.middle ++ [c.beforeLast])
def Cycle.shortTurn (c : Cycle) : List Index := [c.first,c.last,c.beforeLast]

def Cycle.ok (c : Cycle) : Bool := oChainB c.points && (oChainB c.longTurn && oChainB c.shortTurn)

private theorem map_chain {l : List Index} {xs ys : List ℝ}
    (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    (hb : ∀ p ∈ l, p.1 < xs.length ∧ p.2 < ys.length) (h : oChainB l = true) :
    ChainSimple (l.map (gridPt xs ys)) := by
  apply oChainB_sound
  rw [gridPt_eq, oChainB_map (strictMonoOn_getD hx) (strictMonoOn_getD hy) hb]
  exact h

private theorem close_chain {a b z : Point} {l : List Point}
    (h : ChainSimple ((a::l)++[b,z]))
    (h' : ChainSimple (z::a::(l++[b]))) (h'' : ChainSimple [a,z,b]) :
    (Polygon.mk ((a::l)++[b,z])).Simple := by
  suffices hc : (Polygon.mk (a::((l++[b])++[z]))).Simple by
    simpa [List.append_assoc] using hc
  apply simple_of_chain (m := l++[b]) (by simp)
  · simpa [List.append_assoc] using h
  · intro q hq
    have hloc : q ∈ chainSet ((a::l)++(b::[z])) := by simpa [List.append_assoc] using hq.2
    rw [chainSet_append_cons] at hloc
    rcases hloc with hE | hE
    · exact Or.inl (h'.2.1 ⟨hq.1,hE⟩)
    · have hza : q ∈ segment a z := Geometry.segment_comm z a ▸ hq.1
      have hzb : q ∈ segment z b := by simpa [Geometry.segment_comm b z] using hE
      exact Or.inr (h''.2.1 ⟨hza,Or.inl hzb⟩)

theorem Cycle.simple {c : Cycle} {xs ys : List ℝ}
    (hx : xs.IsChain (· < ·)) (hy : ys.IsChain (· < ·))
    (hb : ∀ p ∈ c.points, p.1 < xs.length ∧ p.2 < ys.length) (h : c.ok = true) :
    (Polygon.mk (c.points.map (gridPt xs ys))).Simple := by
  obtain ⟨hf,hg,hh⟩ : oChainB c.points = true ∧ oChainB c.longTurn = true ∧ oChainB c.shortTurn = true := by
    simpa only [Cycle.ok,Bool.and_eq_true] using h
  have hlong (p) (hp : p ∈ c.longTurn) : p ∈ c.points := by
    simpa [Cycle.longTurn,Cycle.points,or_comm,or_left_comm,or_assoc] using hp
  have hshort (p) (hp : p ∈ c.shortTurn) : p ∈ c.points := by
    simp only [Cycle.shortTurn,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [Cycle.points]
  have h₁ := map_chain hx hy hb hf
  have h₂ := map_chain hx hy (fun p hp => hb p (hlong p hp)) hg
  have h₃ := map_chain hx hy (fun p hp => hb p (hshort p hp)) hh
  simp only [Cycle.points,Cycle.longTurn,Cycle.shortTurn,List.map_append,List.map_cons,List.map_nil] at *
  exact close_chain h₁ h₂ h₃

def cyclicAxis (l : List Index) : Prop :=
  ∀ i : Fin l.length,
    let j : Fin l.length := ⟨(i.val+1)%l.length,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩
    l[i].1 = l[j].1 ∨ l[i].2 = l[j].2

instance (l : List Index) : Decidable (cyclicAxis l) := by unfold cyclicAxis; infer_instance

theorem grid_orthogonal (l : List Index) (xs ys : List ℝ) (h : cyclicAxis l) :
    (Polygon.mk (l.map (gridPt xs ys))).Orthogonal := by
  let P : Polygon := ⟨l.map (gridPt xs ys)⟩
  have hn : P.n=l.length := by simp [P,Polygon.n]
  have atIdx (i : Nat) (hi : i < l.length) : P.vtx i=gridPt xs ys l[i] := by
    change (l.map (gridPt xs ys)).getD i (0,0) = _
    rw [List.getD_eq_getElem (l := l.map (gridPt xs ys)) (d := (0,0)) (by simpa using hi), List.getElem_map]
  intro i hi
  change i<P.n at hi
  rw [hn] at hi
  let j : Fin l.length := ⟨(i+1)%l.length,Nat.mod_lt _ (by omega)⟩
  change (P.vtx i).1 = (P.vtx ((i+1)%P.n)).1 ∨ (P.vtx i).2 = (P.vtx ((i+1)%P.n)).2
  rw [hn,atIdx i hi,atIdx j.val j.isLt]
  rcases h ⟨i,hi⟩ with he | he
  · exact Or.inl (congrArg (fun k => xs.getD k 0) he)
  · exact Or.inr (congrArg (fun k => ys.getD k 0) he)

end ArtGallery.Orthogonal.BoundaryPoint.RoomGrid
end
