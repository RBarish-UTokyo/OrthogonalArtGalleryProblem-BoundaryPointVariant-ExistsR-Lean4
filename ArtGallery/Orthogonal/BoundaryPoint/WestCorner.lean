module

public import ArtGallery.Orthogonal.BoundaryPoint.HubFeatures
public import ArtGallery.Orthogonal.BoundaryPoint.SimplePaths

/-! # Replacing the virtual western turn by the short physical side cap -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WestCorner
open ArtGallery.Stade.Chain ArtGallery.Orthogonal.Hard Geometry Set

private theorem simple_corner {l x f h t : ℝ} (across : l<x) (lo : f<h) (hi : h<t) :
    ChainSimple [(x,t),(x,h),(l,h),(l,f)] := by
  let xs := [l,x]
  let ys := [f,h,t]
  let ids : List (Nat × Nat) := [(1,2),(1,1),(0,1),(0,0)]
  have hx : xs.IsChain (·<·) := by simpa [xs,List.isChain_cons_cons] using across
  have hy : ys.IsChain (·<·) := by simpa [ys,List.isChain_cons_cons] using And.intro lo hi
  have bounded : ∀ p∈ids,p.1<xs.length ∧ p.2<ys.length := by
    dsimp [ids,xs,ys]; decide
  have shape : oChainB ids=true := by decide +kernel
  change ChainSimple (ids.map (gridPt xs ys))
  apply oChainB_sound
  rw [gridPt_eq,oChainB_map (strictMonoOn_getD hx) (strictMonoOn_getD hy) bounded]
  exact shape

private theorem limits {l x f h t : ℝ} (across : l<x) (lo : f<h) (hi : h<t) {p : Point}
    (atCorner : p∈chainSet [(x,t),(x,h),(l,h),(l,f)]) :
    p.1≤x ∧ (p.2=f → p=(l,f)) ∧ (p.2=t → p=(x,t)) := by
  simp only [chainSet_cons_cons,chainSet_single,Set.union_empty,Set.mem_union] at atCorner
  rcases atCorner with a|a|a
  · have E := vseg_fst a
    have H := vseg_snd hi.le (segment_comm (x,h) (x,t) ▸ a)
    exact ⟨E.le,fun e => by exfalso; linarith [H.1],fun e => Prod.ext E e⟩
  · obtain ⟨u,hu,hU,rfl⟩ := a
    dsimp
    simp only [sub_self,mul_zero,add_zero]
    exact ⟨by linarith [mul_nonpos_of_nonneg_of_nonpos hu (sub_nonpos.mpr across.le)],
      fun eq => (lo.ne' eq).elim,fun eq => (hi.ne eq).elim⟩
  · have E := vseg_fst a
    have H := vseg_snd lo.le (segment_comm (l,f) (l,h) ▸ a)
    exact ⟨E.le.trans across.le,fun e => Prod.ext E e,fun e => by exfalso; linarith [H.2]⟩

private theorem above_x {l : List Point} {x : ℝ} (all : ∀ p∈l,x<p.1) :
    ∀ p∈chainSet l,x<p.1 := by
  apply chainSet_subset_of_convex (K:={p : Point | x<p.1}) _ all
  intro a ha b hb s t hs ht sum
  change x<a.1 at ha; change x<b.1 at hb
  change x<s*a.1+t*b.1
  rcases hs.eq_or_lt with eq|pos
  · subst s; simp only [zero_add] at sum; subst t; simpa using hb
  · have combined : s*x+t*x=x := by rw [←add_mul,sum,one_mul]
    linarith [mul_lt_mul_of_pos_left ha pos,mul_le_mul_of_nonneg_left hb.le ht]

private theorem append_end (a : Point) (u : List Point) (b : Point) :
    chainSet ((a::u)++[b])=chainSet (a::u)∪ArtGallery.segment ((a::u).getLastD a) b := by
  induction u generalizing a with
  | nil => simp
  | cons z u ih =>
    simp only [List.cons_append,chainSet_cons_cons,List.getLastD_cons]
    rw [show chainSet (z::(u++[b]))=chainSet (z::u)∪ArtGallery.segment ((z::u).getLastD z) b from ih z]
    simp only [List.getLastD_cons,Set.union_assoc]

private theorem long_span {a b : Point} {inside : List Point} {x f t : ℝ}
    (ne : inside≠[]) (far : ∀ p∈inside,x<p.1)
    (start : ∀ p∈inside.head?,p.2=f) (finish : ∀ p∈inside.getLast?,p.2=t)
    (ay : a.2=f) (by' : b.2=t) {q : Point} (hq : q∈chainSet ((a::inside)++[b])) :
    x<q.1 ∨ q.2=f ∨ q.2=t := by
  cases inside with
  | nil => contradiction
  | cons z zs =>
    rw [append_end,chainSet_cons_cons] at hq
    rcases hq with (edge|middle)|last
    · have zy := start z (by simp)
      obtain ⟨u,_,_,rfl⟩ := edge
      exact Or.inr (Or.inl (by simp [ay,zy]))
    · exact Or.inl (above_x far q middle)
    · have entry : ((a::z::zs).getLastD a)∈(z::zs).getLast? := by
        simp [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast]
      have endY := finish _ entry
      obtain ⟨u,_,_,rfl⟩ := last
      exact Or.inr (Or.inr (by simp only [endY,by',sub_self,mul_zero,add_zero]))

theorem replace {l x f h t : ℝ} (across : l<x) (lo : f<h) (hi : h<t)
    (inside : List Point) (ne : inside≠[]) (far : ∀ p∈inside,x<p.1)
    (start : ∀ p∈inside.head?,p.2=f) (finish : ∀ p∈inside.getLast?,p.2=t)
    (old₁ old₂ : Point) (old : (Polygon.mk (((l,f)::inside)++[(x,t),old₁,old₂])).Simple) :
    (Polygon.mk (((l,f)::inside)++[(x,t),(x,h),(l,h)])).Simple := by
  let a : Point := (l,f)
  let b : Point := (x,t)
  let long := (a::inside)++[b]
  have chain : ChainSimple (long++[old₁,old₂]) := by
    simpa only [long,a,b,List.append_assoc,List.singleton_append] using SimplePaths.open_simple old
  have rev : ChainSimple (old₂::old₁::long.reverse) := by simpa using WindowSplice.reverse_simple _ chain
  have longSimple : ChainSimple long := by simpa using WindowSplice.reverse_simple _ rev.tail.tail
  have cut : chainSet long∩chainSet [b,(x,h),(l,h),a] ⊆ {a,b} := by
    intro q both
    obtain ⟨left,Y,Z⟩ := limits across lo hi both.2
    rcases long_span ne far start finish (a:=a) (b:=b) rfl rfl both.1 with ex|floor|roof
    · exact (not_lt_of_ge left ex).elim
    · exact Or.inl (Y floor)
    · exact Or.inr (Z roof)
  simpa only [a,b,List.cons_append,List.append_assoc,List.nil_append] using
    WindowSplice.simple (u:=inside) (v:=[(x,h)]) longSimple (simple_corner across lo hi) cut

end ArtGallery.Orthogonal.BoundaryPoint.WestCorner
end
