module

public import ArtGallery.Orthogonal.BoundaryPoint.CompiledSize

/-! # A linear bound on the number of rational corners actually serialized -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.VertexCount
open CatalogPlan CompiledSize BoundaryChart ChartDrawing RectContour ContourJoin

private theorem flatBound {α β : Type} (l : List α) (f : α → List β) {k : Nat}
    (h : ∀ a∈l,(f a).length≤k) : (l.flatMap f).length≤k*l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun b hb => h _ (List.mem_cons_of_mem _ hb))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
    omega

theorem hub_count (n c : Nat) (ss : List ℚ) : (hubCycle n c ss).length≤5+10*c+10*ss.length := by
  let f := 1-BankCoordinates.D n
  have feet := flatBound (List.range c).reverse (foot f) (k:=4) (fun _ _ => by rfl)
  have floor := flatBound ss.tail (divider f) (k:=6) (fun _ _ => by rfl)
  have top := flatBound ss.reverse (shaft f) (k:=4) (fun _ _ => by rfl)
  have caps := flatBound (List.range c) (capPath c) (k:=6) (fun j _ => by unfold capPath; split <;> simp)
  simp only [List.length_reverse,List.length_range,List.length_tail] at feet floor top caps
  dsimp only [f] at feet floor top
  unfold hubCycle
  dsimp only
  simp only [List.length_append,List.length_cons,List.length_nil]
  change 1+_+_+2+_+_+2≤_
  omega

theorem at_door_length {d w : ℚ} {cycle path : List Vertex} (h : atDoor d w cycle=some path) :
    path.length=cycle.length := by
  unfold atDoor at h; dsimp only at h
  split at h
  · contradiction
  · obtain rfl := Option.some.inj h
    simp only [List.length_map,List.length_append,List.length_drop,List.length_take]
    omega

theorem catalog_length : catalog.all (fun t => decide (t.chart.cycle.points.length≤198))=true := by decide +kernel

private theorem chosen {tables : List Template} (n j i : Nat) (ranks : List Nat) {e : Entrance}
    (hs : tables.all (fun t => decide (t.chart.cycle.points.length≤198))=true)
    (h : (choose tables (fun t => drawOne t n j ranks) i (none,0)).1=some e) : e.2.length≤198 := by
  induction tables generalizing i with
  | nil => contradiction
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at hs
    simp only [choose] at h; split at h
    · obtain ⟨path,hp,rfl⟩ := Option.map_eq_some_iff.mp h
      have len := at_door_length hp
      simp only [Chart.draw,List.length_map] at len
      exact len ▸ hs.1
    · exact ih _ hs.2 h

private theorem rows_length (rows : List (Vertex × List (List Vertex)))
    (h : ∀ r∈rows, ∀ w∈r.2,w.length≤198) :
    (rows.flatMap (fun r => r.1::r.2.flatten)).length≤rows.length+198*(rows.map (fun r => r.2.length)).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    have hr : r.2.flatten.length≤198*r.2.length := by
      simpa using flatBound r.2 id (h _ List.mem_cons_self)
    have tail := ih (fun b hb => h _ (List.mem_cons_of_mem _ hb))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,List.map_cons,List.sum_cons,Nat.mul_add]
    omega

theorem splice_count {w : ℚ} {hub out : List Vertex} {ws : List Entrance}
    (bound : ∀ e∈ws, e.2.length≤198) (h : splice w hub ws=some out) :
    out.length≤hub.length+198*ws.length := by
  let rs := sections w hub ws
  have rr : ∀ r∈rs, ∀ v∈r.2,v.length≤198 := by
    intro r hr v hv
    obtain ⟨edge,_,rfl⟩ := List.mem_map.mp hr
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hv
    exact bound g (List.mem_filter.mp hg).1
  have rows := rows_length rs rr
  have n : rs.length≤hub.length := by simp [rs,sections]
  unfold splice at h; dsimp only at h
  split at h
  next equal =>
    obtain rfl := Option.some.inj h
    change (rs.map (fun r => r.2.length)).sum=ws.length at equal
    rw [equal] at rows
    exact rows.trans (by omega)
  · contradiction

theorem emitted {eqs : List ETRINV.Constraint} {v g} (out : CandidateWord.vertices eqs=some (v,g)) :
    v.length≤36890*eqs.length+5 := by
  let p := compile eqs
  let n := scale eqs
  have slot : p.2.length≤3*p.1.length := slot_count eqs
  have row : p.1.length≤155*eqs.length := (row_bounds eqs).2
  change ChartDrawing.vertices p=some (v,g) at out
  unfold ChartDrawing.vertices at out; split at out
  · obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj out); simp
  · dsimp only at out; split at out
    · obtain ⟨polygon,hp,hh⟩ := Option.map_eq_some_iff.mp out
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh
      let drawn := batch n p.1
      have filtered : (drawn.filterMap Prod.fst).length≤p.1.length :=
        (List.length_filterMap_le _ _).trans_eq (by simp [drawn,batch])
      have bnd := splice_count (ws:=drawn.filterMap Prod.fst) (fun e he => ?_) hp
      · have hc := hub_count n p.1.length (p.2.map fun a => BankCoordinates.slotX n a.1 a.2)
        simp only [List.length_map] at hc
        change polygon.length≤(hubCycle n p.1.length (p.2.map fun a => BankCoordinates.slotX n a.1 a.2)).length+198*(drawn.filterMap Prod.fst).length at bnd
        omega
      · obtain ⟨d,hd,h⟩ := List.mem_filterMap.mp he
        obtain ⟨⟨r,j⟩,_,rfl⟩ := List.mem_map.mp hd
        exact chosen n j r.1 r.2 catalog_length h
    · contradiction

end ArtGallery.Orthogonal.BoundaryPoint.VertexCount
end
