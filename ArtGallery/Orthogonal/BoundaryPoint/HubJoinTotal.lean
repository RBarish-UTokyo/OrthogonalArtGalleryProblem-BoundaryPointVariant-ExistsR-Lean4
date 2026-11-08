module

public import ArtGallery.Orthogonal.BoundaryPoint.HubDoors

/-! # The hub splice accepts every extracted wing at its compiled address -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubJoinTotal
open RectContour ContourJoin BoundaryChart BankCoordinates HubDoors

private theorem compatible_high (w : ℚ) (e : Vertex × Vertex) (v : Entrance) (h : compat w e v=true) :
    high e=true := by
  simp only [compat,Bool.and_eq_true] at h
  simp only [high,Bool.and_eq_true]
  exact h.1.1.1

theorem one (n count i : Nat) (hn : 65≤n) (hi : i<count) (ss : List ℚ) (v : List Vertex) :
    let l := hubCycle n count ss
    ((l.zip (l.drop 1++l.take 1)).filter (fun e => compat (W n) e (door i,v))).length=1 := by
  let l := hubCycle n count ss
  let edges := l.zip (l.drop 1++l.take 1)
  let ok := fun e => compat (W n) e (door i,v)
  have pre : (edges.filter high).filter ok=edges.filter ok := by
    rw [List.filter_filter]
    apply List.filter_congr; intro e _
    cases h : ok e with
    | false => simp
    | true => simp [compatible_high _ _ _ h]
  change (edges.filter ok).length=1
  rw [← pre,show edges.filter high=(List.range count).map topEdge from ceiling n count ss hn,
    ← List.countP_eq_length_filter,List.countP_map]
  have eq : (ok ∘ topEdge)=(fun j => j==i) := by
    funext j
    change compat (W n) (topEdge j) _=_
    rw [slot n i j hn v]
    by_cases same : i=j
    · rw [same]
    · simp [same,Ne.symm same]
  rw [eq,← List.count_eq_countP]
  have le := (List.nodup_iff_count_le_one.mp (List.nodup_range (n:=count))) i
  have pos := List.count_pos_iff.mpr (List.mem_range.mpr hi)
  omega

private theorem sum_swap {α β : Type} (p : α → β → Bool) (as : List α) (bs : List β) :
    (as.map (fun a => (bs.filter (p a)).length)).sum =
      (bs.map (fun b => (as.filter (fun a => p a b)).length)).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have increment (l : List α) :
        (l.map (fun a => ((b::bs).filter (p a)).length)).sum =
        (l.filter (fun a => p a b)).length+(l.map (fun a => (bs.filter (p a)).length)).sum := by
      induction l with
      | nil => simp
      | cons a l hh =>
        simp only [List.map_cons,List.sum_cons]
        rw [hh]
        cases eq : p a b <;> simp [List.filter_cons,eq] <;> omega
    rw [increment,ih]; rfl

theorem accepts (n count : Nat) (hn : 65≤n) (ss : List ℚ) (ws : List Entrance)
    (registered : ∀ e∈ws,∃ i, i<count ∧ e.1=door i) :
    (splice (W n) (hubCycle n count ss) ws).isSome=true := by
  let hub := hubCycle n count ss
  let edges := hub.zip (hub.drop 1++hub.take 1)
  have matched (e : Entrance) (he : e∈ws) : (edges.filter (fun k => compat (W n) k e)).length=1 := by
    obtain ⟨i,hi,equal⟩ := registered e he
    obtain ⟨d,v⟩ := e
    change d=door i at equal
    subst d
    exact one n count i hn hi ss v
  have total : ((sections (W n) hub ws).map (fun p => p.2.length)).sum=ws.length := by
    simp only [sections,List.map_map,Function.comp_def,List.length_map]
    change (edges.map (fun e => (ws.filter (compat (W n) e)).length)).sum=_
    rw [sum_swap]
    have all : ws.map (fun e => (edges.filter (fun k => compat (W n) k e)).length)=ws.map (fun _ => 1) := by
      apply List.map_congr_left
      exact matched
    rw [all]; simp
  change (splice (W n) hub ws).isSome=true
  simp only [splice,total,ite_true,Option.isSome_some]

end ArtGallery.Orthogonal.BoundaryPoint.HubJoinTotal
end
