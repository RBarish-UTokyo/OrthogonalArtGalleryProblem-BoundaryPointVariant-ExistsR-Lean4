module

public import ArtGallery.Orthogonal.BoundaryPoint.OrthogonalSplice
public import ArtGallery.Orthogonal.BoundaryPoint.CandidateWord

/-! # All cyclic edges of the hub and the fully spliced gallery are orthogonal -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubTurn
open RectContour ContourJoin OrthogonalWalk BoundaryChart BankCoordinates ChartDrawing CatalogPlan

private theorem feet (f : ℚ) (j : Nat) : Level f (foot f j) := by
  constructor <;> simp [foot,aligned,List.isChain_cons_cons]
private theorem dividers (f p : ℚ) : Level f (divider f p) := by
  constructor <;> simp [divider,aligned,List.isChain_cons_cons]
private theorem shafts (f p : ℚ) : Level (-6) (shaft f p) := by
  constructor <;> simp [shaft,aligned,List.isChain_cons_cons]
private theorem caps {j n : Nat} (hj : j+1<n) : Level (-6) (capPath n j) := by
  constructor <;> simp [capPath,hj,aligned,List.isChain_cons_cons]

private theorem between {y : ℚ} {l : List Vertex} (hl : Level y l) {a b : Vertex}
    (ha : a.2=y) (hb : b.2=y) : (a::(l++[b])).IsChain aligned := by
  have one : Level y [a] := ha ▸ level_single a
  have two : Level y [b] := hb ▸ level_single b
  simpa only [List.singleton_append,List.cons_append,List.nil_append] using ((one.append hl).append two).path

theorem hub (n count : Nat) (slots : List ℚ) (nonempty : 0<count) : loop (hubCycle n count slots) := by
  cases count with
  | zero => contradiction
  | succ k =>
    let f := 1-D n
    let l := door k-30
    let r := slots.getLastD 0+10
    let a : Vertex := (l-1/10,f)
    let low := (List.range (k+1)).reverse.flatMap (foot f) ++ slots.tail.flatMap (divider f)
    let high := slots.reverse.flatMap (shaft f) ++ (List.range k).flatMap (capPath (k+1))
    have split : (List.range (k+1)).flatMap (capPath (k+1))=
        (List.range k).flatMap (capPath (k+1)) ++ capPath (k+1) k := by rw [List.range_succ]; simp
    have endCap : capPath (k+1) k=[(door k+110,-6),(door k+110,1-1/10000),
        (door k+110+1/10,1-1/10000),(door k+110+1/10,1),(l,1)] := by simp [capPath,l]
    have arrange : hubCycle n (k+1) slots =
        a::(low++(r,f)::(r,-6)::(high++(capPath (k+1) k++[(l,f+1/100000000),(l-1/10,f+1/100000000)]))) := by
      unfold hubCycle
      rw [split]
      simp only [low,high,a,f,l,r,Nat.add_sub_cancel,List.singleton_append,List.cons_append,List.append_assoc,
        List.nil_append]
    have down : Level f low :=
      (level_flat f _ _ fun j _ => feet f j).append (level_flat f _ _ fun v _ => dividers f v)
    have up : Level (-6) high :=
      (level_flat _ _ _ (fun v _ => shafts f v)).append (level_flat _ _ _ fun j hj => caps (Nat.succ_lt_succ (List.mem_range.mp hj)))
    rw [arrange,endCap]
    simp only [loop,List.cons_append,List.append_assoc,List.nil_append]
    apply List.isChain_cons_split.mpr
    refine ⟨between down (a:=a) (b:=(r,f)) rfl rfl,?_⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨Or.inl rfl,?_⟩
    apply List.isChain_cons_split.mpr
    refine ⟨between up (a:=(r,-6)) (b:=(door k+110,-6)) rfl rfl,?_⟩
    simp [aligned,List.isChain_cons_cons,a]

theorem catalog_orthogonal : catalog.all (fun t => decide (RoomGrid.cyclicAxis t.chart.cycle.points))=true := by
  apply List.all_eq_true.mpr
  intro t h
  simp only [catalog,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact decide_eq_true WingChart.Ordinary_40_200_520.axis_edges
  · exact decide_eq_true WingChart.Shifted_40_200_520.axis_edges
  · exact decide_eq_true WingChart.Lower_40_200_1000.axis_edges
  · exact decide_eq_true WingChart.Lower_10_40_1000.axis_edges
  · exact decide_eq_true WingChart.Lower_10_200_1000.axis_edges
  · exact decide_eq_true WingChart.Lower_10_360_1000.axis_edges
  · exact decide_eq_true WingChart.Lower_10_520_1000.axis_edges
  · exact decide_eq_true WingChart.InvLe_1_40.axis_edges
  · exact decide_eq_true WingChart.InvLe_1_200.axis_edges
  · exact decide_eq_true WingChart.InvLe_1_360.axis_edges
  · exact decide_eq_true WingChart.InvLe_1_520.axis_edges
  · exact decide_eq_true WingChart.InvRevGe_1_10.axis_edges
  · exact decide_eq_true WingChart.InvLe_40_200.axis_edges
  · exact decide_eq_true WingChart.InvRevGe_40_200.axis_edges

private theorem drawn (t : Template) (h : RoomGrid.cyclicAxis t.chart.cycle.points) (n j : Nat)
    (rs : List Nat) (e : Entrance) (hit : (drawOne t n j rs).1=some e) : Level 1 e.2 := by
  let s := (1:ℚ)/n
  let c := t.corridor.coords (s::((j:ℚ)*s)::(rs.map fun (i : Nat) => (i:ℚ)*s))
  let r := t.room.coords s
  let data := (c.1++r.1,c.2++r.2)
  change (atDoor (door j) (W n) (t.chart.draw data)).map (fun v => (door j,v))=some e at hit
  obtain ⟨path,hp,rfl⟩ := Option.map_eq_some_iff.mp hit
  exact at_door ((polygon _).2 (BoundaryChart.orthogonal _ h data)) hp

private theorem selected (ts : List Template) (n j i : Nat) (ranks : List Nat)
    (ok : ts.all (fun t => decide (RoomGrid.cyclicAxis t.chart.cycle.points))=true) {e : Entrance}
    (hit : (choose ts (fun t => drawOne t n j ranks) i (none,0)).1=some e) : Level 1 e.2 := by
  induction ts generalizing i with
  | nil => contradiction
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at ok
    simp only [choose] at hit
    split at hit
    · exact drawn t ok.1 _ _ _ _ hit
    · exact ih _ ok.2 hit

theorem emitted (p : Input) {v g} (out : ChartDrawing.vertices p=some (v,g)) :
    (Polygon.mk (v.map ratPoint)).Orthogonal := by
  apply (polygon v).1
  unfold ChartDrawing.vertices at out
  split at out
  · obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj out)
    simp [loop,aligned,List.isChain_cons_cons]
  next nonempty =>
    dsimp only at out
    split at out
    · obtain ⟨v',join,hv⟩ := Option.map_eq_some_iff.mp out
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hv
      have hasRows : p.1≠[] := by simpa using nonempty
      apply OrthogonalSplice.splice_orthogonal _ _ _ _ (hub _ _ _ (List.length_pos_iff.mpr hasRows)) _ join
      intro e he
      obtain ⟨d,hd,h⟩ := List.mem_filterMap.mp he
      obtain ⟨⟨row,j⟩,_,rfl⟩ := List.mem_map.mp hd
      exact selected catalog _ j _ row.2 catalog_orthogonal h
    · contradiction

theorem word_vertices (eqs : List ETRINV.Constraint) {v g} (out : CandidateWord.vertices eqs=some (v,g)) :
    (Polygon.mk (v.map ratPoint)).Orthogonal := emitted (compile eqs) out

end ArtGallery.Orthogonal.BoundaryPoint.HubTurn
end
