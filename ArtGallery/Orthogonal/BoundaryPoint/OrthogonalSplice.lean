module

public import ArtGallery.Orthogonal.BoundaryPoint.OrthogonalWalk

/-! # Replacing any number of horizontal door subedges by orthogonal wing paths -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.OrthogonalSplice
open RectContour ContourJoin OrthogonalWalk

def insertions (w : ℚ) (wings : List Entrance) (a b : Vertex) : List Vertex :=
  (wings.filter (compat w (a,b))).flatMap Prod.snd

private theorem step (w : ℚ) (wings : List Entrance)
    (good : ∀ e∈wings,Level 1 e.2) {a b : Vertex} (edge : aligned a b) :
    (a::(insertions w wings a b++[b])).IsChain aligned := by
  let ws := wings.filter (compat w (a,b))
  have hpath : Level 1 (insertions w wings a b) :=
    level_flat 1 ws Prod.snd (fun e he => good e (List.mem_filter.mp he).1)
  by_cases h : ws=[]
  · change (a::(ws.flatMap Prod.snd++[b])).IsChain aligned
    simpa [h] using edge
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil ws h
  have compatible := (List.mem_filter.mp he).2
  simp only [compat,Bool.and_eq_true,beq_iff_eq] at compatible
  have first : Level 1 [a] := compatible.1.1.1.1 ▸ level_single a
  have last : Level 1 [b] := compatible.1.1.1.2 ▸ level_single b
  simpa only [List.singleton_append,List.cons_append,List.nil_append] using ((first.append hpath).append last).path

def woven (f : Vertex → Vertex → List Vertex) (close : Vertex) : List Vertex → List Vertex
  | [] => []
  | a::l => a::(f a (l.headD close) ++ woven f close l)

private theorem along (f : Vertex → Vertex → List Vertex) (close : Vertex) (a : Vertex) (l : List Vertex) :
    ((a::l).zip (l++[close])).flatMap (fun p => p.1::f p.1 p.2)=woven f close (a::l) := by
  induction l generalizing a with
  | nil => simp [woven]
  | cons b l ih =>
    simp only [List.cons_append,List.zip_cons_cons,List.flatMap_cons,ih]
    rfl

private theorem preserves (f : Vertex → Vertex → List Vertex) (close : Vertex)
    (hl : ∀ a b, aligned a b → (a::(f a b++[b])).IsChain aligned)
    (a : Vertex) (l : List Vertex) (walk : ((a::l)++[close]).IsChain aligned) :
    (woven f close (a::l)++[close]).IsChain aligned := by
  induction l generalizing a with
  | nil => simpa [woven] using hl a close (List.isChain_cons_cons.mp walk).1
  | cons b l ih =>
    have pair := List.isChain_cons_cons.mp walk
    have tail := ih b pair.2
    change (b::(f b (l.headD close)++woven f close l) ++ [close]).IsChain aligned at tail
    simp only [List.cons_append,List.append_assoc] at tail
    change ((a::(f a b++(b::(f b (l.headD close)++woven f close l))))++[close]).IsChain aligned
    simp only [List.cons_append,List.append_assoc]
    exact List.isChain_cons_split.mpr ⟨hl a b pair.1,tail⟩

theorem splice_orthogonal (w : ℚ) (hub : List Vertex) (wings : List Entrance) (out : List Vertex)
    (shape : loop hub) (paths : ∀ e∈wings,Level 1 e.2) (hit : splice w hub wings=some out) :
    loop out := by
  unfold splice at hit
  dsimp only at hit
  split at hit
  · obtain rfl := Option.some.inj hit
    cases hub with
    | nil => trivial
    | cons a l =>
      let f := insertions w wings
      have eq : ((sections w (a::l) wings).flatMap (fun b => b.1::b.2.flatten))=woven f a (a::l) := by
        simpa only [sections,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
          List.flatMap_map,List.map_map,Prod.mk.eta,Function.comp_def,insertions,List.flatMap_def,f] using along f a a l
      rw [eq]
      change (woven f a (a::l)++[a]).IsChain aligned
      exact preserves f a (fun _ _ e => step _ _ paths e) a l shape
  · contradiction

end ArtGallery.Orthogonal.BoundaryPoint.OrthogonalSplice
end
