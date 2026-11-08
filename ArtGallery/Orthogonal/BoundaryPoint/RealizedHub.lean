module

public import ArtGallery.Orthogonal.BoundaryPoint.HubComb
public import ArtGallery.Orthogonal.BoundaryPoint.WestCorner
public import ArtGallery.Orthogonal.BoundaryPoint.RealizedDoors

/-! # Simplicity of the shared hub actually emitted by the reduction -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RealizedHub
open RectContour BoundaryChart BankCoordinates HubFeatures HubComb

def terrace (j : Nat) : List Vertex :=
  [(door j+110,-6),(door j+110,1-1/10000),(door j+110+1/10,1-1/10000),(door j+110+1/10,1)]

def inner (n k : Nat) (ss : List ℚ) : List Vertex :=
  let f := 1-D n
  (List.range (k+1)).reverse.flatMap (foot f) ++ ss.tail.flatMap (divider f) ++
    [(R ss,f),(R ss,-6)] ++ ss.reverse.flatMap (shaft f) ++ (List.range k).flatMap (capPath (k+1)) ++ terrace k

private theorem tagged {α : Type} (l : List α) (f : ℚ) (tag : α → Feature) (path : α → List Vertex)
    (each : ∀ a∈l, trace f (tag a)=(path a).map ratPoint) :
    ((l.map tag).map (trace f)).flatten=(l.flatMap path).map ratPoint := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,List.map_append,each a List.mem_cons_self,
      ih (fun z hz => each z (List.mem_cons_of_mem _ hz))]

private theorem floor_map (n k : Nat) (ss : List ℚ) :
    ((floorTags (k+1) ss).map (trace (1-D n))).flatten=
      ((List.range (k+1)).reverse.flatMap (foot (1-D n))++ss.tail.flatMap (divider (1-D n))).map ratPoint := by
  rw [floorTags,List.map_append,List.flatten_append,List.map_append]
  rw [tagged _ _ footTag _ (fun j _ => foot_trace _ j),tagged _ _ dividerTag _ (fun x _ => divider_trace _ x)]

private theorem roof_map (n k : Nat) (ss : List ℚ) :
    ((ceilTags (k+1) ss).map (trace (1-D n))).flatten=
      (ss.reverse.flatMap (shaft (1-D n))++(List.range k).flatMap (capPath (k+1))++
        terrace k++[(door k-30,1),(door k-30,-6)]).map ratPoint := by
  let f := 1-D n
  have part (j : Nat) (hj : j∈List.range k) : trace f (capTag j)=(capPath (k+1) j).map ratPoint := by
    rw [cap_trace]; simp [capPath,show j+1<k+1 by have := List.mem_range.mp hj; omega]
  simp only [ceilTags,List.map_append,List.flatten_append,List.map_append,List.range_succ,List.map_singleton,
    List.flatten_singleton]
  rw [tagged _ _ shaftTag _ (fun x _ => shaft_trace _ x),tagged _ _ capTag _ part,cap_trace]
  simp [capPath,terrace,List.append_assoc]

private theorem turns (n k : Nat) (ss : List ℚ) :
    let d := door k
    let f := 1-D n
    let a : Vertex := (L k,f)
    let b : Vertex := (d-30,1)
    hubCycle n (k+1) ss=(a::inner n k ss)++[b,(d-30,f+1/100000000),(L k,f+1/100000000)] := by
  have split : (List.range (k+1)).flatMap (capPath (k+1))=(List.range k).flatMap (capPath (k+1))++capPath (k+1) k := by
    rw [List.range_succ]; simp
  simp only [inner,hubCycle,split,L,R,terrace,capPath,lt_self_iff_false,ite_false,List.append_assoc,
    List.cons_append,List.singleton_append,List.nil_append,Nat.add_sub_cancel]

private theorem virtual_turns (n k : Nat) (ss : List ℚ) :
    let d := door k
    let f := 1-D n
    let a := ratPoint (L k,f)
    (virtual n k ss).vertices=(a::(inner n k ss).map ratPoint)++
        [ratPoint (d-30,1),ratPoint (d-30,-6),ratPoint (L k,-6)] := by
  simp only [virtual,floor_map,roof_map,inner,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
    List.cons_append,List.nil_append]

private theorem west_of_inner {ss : List ℚ} (h : Placed ss) (n k : Nat) {z : Vertex} (hz : z∈inner n k ss) :
    door k-30<z.1 := by
  have notPos : door k≤0 := by unfold door; exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have far := h.far (ss.getLast h.exists_slot) (ss.getLast_mem h.exists_slot)
  have upper := last_bound h _ (ss.getLast_mem h.exists_slot)
  simp only [inner,List.mem_append] at hz
  rcases hz with ((((foot|divider)|side)|shaft)|cap)|top
  · obtain ⟨j,hj,atFoot⟩ := List.mem_flatMap.mp foot
    have jle := Nat.le_of_lt_succ (List.mem_range.mp (List.mem_reverse.mp hj))
    have lower : door k≤door j := mul_le_mul_of_nonpos_left (by exact_mod_cast jle) (by norm_num : (-2000:ℚ)≤0)
    simp only [BoundaryChart.foot,List.mem_cons,List.not_mem_nil,or_false] at atFoot
    rcases atFoot with rfl|rfl|rfl|rfl <;> dsimp <;> linarith
  · obtain ⟨x,hx,atDivider⟩ := List.mem_flatMap.mp divider
    have room := h.far x (List.mem_of_mem_tail hx)
    simp only [BoundaryChart.divider,List.mem_cons,List.not_mem_nil,or_false] at atDivider
    rcases atDivider with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp <;> linarith
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at side
    rcases side with rfl|rfl <;> change door k-30<ss.getLastD 0+10 <;> linarith
  · obtain ⟨x,hx,atShaft⟩ := List.mem_flatMap.mp shaft
    have room := h.far x (List.mem_reverse.mp hx)
    simp only [BoundaryChart.shaft,List.mem_cons,List.not_mem_nil,or_false] at atShaft
    rcases atShaft with rfl|rfl|rfl|rfl <;> dsimp <;> linarith
  · obtain ⟨j,hj,atCap⟩ := List.mem_flatMap.mp cap
    have lt := List.mem_range.mp hj
    have apart : door k<door j := mul_lt_mul_of_neg_left (by exact_mod_cast lt) (by norm_num : (-2000:ℚ)<0)
    simp [capPath,show j+1<k+1 by omega] at atCap
    rcases atCap with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp <;> linarith
  · simp [terrace] at top
    rcases top with rfl|rfl|rfl|rfl <;> dsimp <;> linarith

theorem simple {ss : List ℚ} (placed : Placed ss) (n k : Nat) (hn : 65≤n) :
    (Polygon.mk ((hubCycle n (k+1) ss).map ratPoint)).Simple := by
  let f : ℚ := 1-D n
  let x : ℝ := (door k:ℝ)-30
  let g : ℝ := (f:ℝ)+1/100000000
  let l : ℝ := (L k:ℝ)
  let u := (inner n k ss).map ratPoint
  have startQ : (inner n k ss).head?=some (door k+100-1/1000,f) := by
    simp only [inner,List.range_succ (n:=k),List.reverse_append,List.reverse_singleton,List.singleton_append,
      List.flatMap_cons,foot,List.cons_append,List.head?_cons,f]
  have endQ : (inner n k ss).getLast?=some (door k+110+1/10,1) := by
    have ep : (terrace k).getLast?=some (door k+110+1/10,1) := rfl
    simp only [inner,List.getLast?_append,ep,Option.some_or]
  have ne : u≠[] := by intro e; have p := congrArg List.head? e; simp [u,startQ] at p
  have far (p) (hp : p∈u) : x<p.1 := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    simpa only [x,ratPoint,Rat.cast_sub,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr (west_of_inner placed n k hv)
  have start (p : Point) (hp : p∈u.head?) : p.2=f := by
    have eq : ratPoint (door k+100-1/1000,f)=p := by simpa only [u,List.head?_map,startQ,Option.map_some,Option.mem_some_iff] using hp
    rw [← eq]; rfl
  have finish (p : Point) (hp : p∈u.getLast?) : p.2=1 := by
    have eq : ratPoint (door k+110+1/10,1)=p := by simpa only [u,List.getLast?_map,endQ,Option.map_some,Option.mem_some_iff] using hp
    rw [← eq]; norm_num [ratPoint]
  have bn : (65:ℚ)≤n := by exact_mod_cast hn
  have low : f< -7 := by dsimp [f,D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) bn]
  have fLow : (f:ℝ)< -7 := by exact_mod_cast low
  have eq : virtual n k ss=⟨((l,(f:ℝ))::u)++[(x,1),(x,-6),(l,-6)]⟩ := by
    apply congrArg Polygon.mk
    simpa only [virtual,x,l,u,f,ratPoint,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg] using virtual_turns n k ss
  have old := simple_virtual placed n k hn
  rw [eq] at old
  have result := WestCorner.replace (l:=l) (x:=x) (f:=(f:ℝ)) (h:=g) (t:=1)
    (by dsimp [l,L,x]; push_cast; linarith) (by dsimp [g]; linarith) (by dsimp [g]; linarith)
    u ne far start finish (x,-6) (l,-6) old
  rw [turns]
  simpa only [u,x,g,l,f,List.map_append,List.map_cons,List.map_nil,ratPoint,Rat.cast_add,
    Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using result

open CompiledSize CatalogPlan CatalogRanks CatalogLogic

theorem placed {eqs : List ETRINV.Constraint} (ne : eqs≠[]) : Placed (PlacedSlots.starts eqs) := by
  have positive : 0<(compile eqs).1.length := by
    have count := (row_bounds eqs).1
    have len := List.length_pos_iff.mpr ne
    omega
  have nonempty : (PlacedSlots.starts eqs)≠[] := by
    intro empty
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp positive)
    have ⟨tag,arity⟩ := CandidateTotal.valid_row hr
    have ar : 0<(profileBanks r.1).length := by generalize e : r.1=i at tag ⊢; interval_cases i <;> decide
    have len : 0<r.2.length := arity ▸ ar
    change r∈(expanded eqs).map (fun q => (q.1,q.2.map (CatalogPlan.rank (keysOf eqs)))) at hr
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have qlen : 0<q.2.length := by simpa using len
    obtain ⟨v,hv⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp qlen)
    have used := address_used eqs v (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨q,hq,hv⟩))
    have member : slotX (scale eqs) (loc (keysOf eqs) v).1 (loc (keysOf eqs) v).2∈PlacedSlots.starts eqs :=
      List.mem_map.mpr ⟨_,used,rfl⟩
    rw [empty] at member
    exact List.not_mem_nil member
  have pitch : (10:ℚ)≤delta (scale eqs) := by
    have hn : (65:ℚ)≤scale eqs := by exact_mod_cast (scale_bounds ne).1
    unfold delta; linarith
  exact ⟨nonempty,fun _ h => PlacedSlots.right_of_all_wings ne h,
    (PlacedSlots.increasing ne).imp (fun h => by linarith)⟩

theorem production {eqs : List ETRINV.Constraint} (ne : eqs≠[]) : (RealizedDoors.hub eqs).Simple := by
  have positive : 0<(compile eqs).1.length := by
    have count := (row_bounds eqs).1
    have len := List.length_pos_iff.mpr ne
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  change (Polygon.mk ((hubCycle (scale eqs) (compile eqs).1.length (PlacedSlots.starts eqs)).map ratPoint)).Simple
  rw [hk]
  exact simple (placed ne) _ k (scale_bounds ne).1

end ArtGallery.Orthogonal.BoundaryPoint.RealizedHub
end
