module

public import ArtGallery.Orthogonal.BoundaryPoint.LinearRegister
public import ArtGallery.Orthogonal.BoundaryPoint.BoundaryChart

/-! # A checked door in a physical wing chart
The rectangle pool precedes room coordinates and guard marks. A finite
prefix certificate identifies the door from original staircase registers and
excludes all earlier vertices from its left endpoint. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.DoorRead
open RoomGrid BoundaryChart CorridorProgram MarginCert LinearRegister RectContour ContourJoin

def entries (y : Bool) (cells : List (Rect Nat)) :=
  cells.flatMap fun r => if y then [r.2.2.1,r.2.2.2] else [r.1,r.2.1]

def coordRef (levels registers : List Nat) (gridIndex : Nat) : Option Nat := do
  let poolIndex ← levels[gridIndex]?
  registers[poolIndex]?

def node (c : Chart) (cells : List (Rect Nat)) (v : Index) : Option (Nat × Nat) := do
  return (← coordRef c.x (entries false cells) v.1,← coordRef c.y (entries true cells) v.2)

def packed (cs : List (Rect Nat)) (xs : List ℚ) (extras : List (Rect ℚ)) (marks : List (List Vertex)) : Data ℚ :=
  (cs.map (readRect xs) ++extras,marks)

private theorem append_pool (y : Bool) (cs : List (Rect Nat)) (xs : List ℚ) (rs : List (Rect ℚ)) (marks : List (List Vertex)) :
    ∃ suffix, pool y (packed cs xs rs marks)=(entries y cs).map (getRat xs)++suffix := by
  let take (r : Rect ℚ) := if y then [r.2.2.1,r.2.2.2] else [r.1,r.2.1]
  let pick (v : Vertex) := if y then v.2 else v.1
  refine ⟨rs.flatMap take++marks.flatten.map pick,?_⟩
  unfold pool packed; dsimp only
  rw [List.flatMap_append,List.append_assoc]
  have H : (cs.map (readRect xs)).flatMap take=(entries y cs).map (getRat xs) := by
    induction cs with
    | nil => rfl
    | cons r cs ih =>
      cases y <;> simp_all [entries,take,readRect,List.flatMap_cons,List.map_append]
  exact congrArg (fun t => t++(rs.flatMap take++marks.flatten.map pick)) H

private theorem coord {levels registers : List Nat} {i ref : Nat} (h : coordRef levels registers i=some ref)
    {xs p : List ℚ} (pool_eq : ∃ r, p=registers.map (getRat xs)++r) :
    (selected p levels).getD i 0=getRat xs ref := by
  unfold coordRef at h
  obtain ⟨j,hj,m⟩ := Option.bind_eq_some_iff.mp h
  have bound : j<registers.length := (List.getElem?_eq_some_iff.mp m).choose
  obtain ⟨extra,rfl⟩ := pool_eq
  simp only [selected,List.getD_eq_getElem?_getD,List.getElem?_map,hj,Option.map_some,Option.getD_some]
  rw [List.getElem?_append_left (by simpa using bound),List.getElem?_map,m]
  rfl

theorem node_value {c : Chart} {cs : List (Rect Nat)} {v : Index} {u : Nat × Nat} (h : node c cs v=some u)
    (xs : List ℚ) (rs : List (Rect ℚ)) (marks : List (List Vertex)) :
    let d := packed cs xs rs marks
    chartPt (selected (pool false d) c.x) (selected (pool true d) c.y) v =
      (getRat xs u.1,getRat xs u.2) := by
  unfold node at h
  obtain ⟨i,hi,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨j,hj,h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  exact Prod.ext (coord hi (append_pool false ..)) (coord hj (append_pool true ..))

def fixed (program : List Row) (i : Nat) (b a : ℚ) : Bool :=
  (read 8 program i).any fun f => decide (f.1=b ∧ f.2=a)

def misses (program : List Row) (boxes : List Box) (i : Nat) (q : ℚ) : Bool :=
  let box := getBox boxes i
  decide (box.hi<q ∨ q<box.lo) ||
    (read 8 program i).any fun a => decide (a.1=q ∧ a.2≠0)

def outside (c : Chart) (cs : List (Rect Nat)) (p : List Row) (bs : List Box) (v : Index) :=
  (node c cs v).any fun u => misses p bs u.1 0 || misses p bs u.2 1

def atCorner (c : Chart) (cs : List (Rect Nat)) (p : List Row) (v : Index) (dx : ℚ) :=
  (node c cs v).any fun u => fixed p u.1 0 dx && fixed p u.2 1 0

def check (c : Chart) (cs : List (Rect Nat)) (program : List Row) (bs : List Box) (j : Nat) :=
  let q := c.cycle.points
  decide (j+1<q.length) && ((q.take j).all (outside c cs program bs) &&
    (atCorner c cs program (q.getD j (0,0)) 0 && atCorner c cs program (q.getD (j+1) (0,0)) (1/320)))

private theorem andParts {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by simpa only [Bool.and_eq_true] using h
private theorem from_any {α} {o : Option α} {p : α → Bool} (h : o.any p=true) :
    ∃ x, o=some x ∧ p x=true := by cases o <;> simp_all

private theorem fixed_value {args xs : List ℚ} {ps : List Row} (h : Ledger args ps xs) {i : Nat} {b a : ℚ}
    (passed : fixed ps i b a=true) : getRat xs i=b+a*getRat args 0 := by
  obtain ⟨⟨b',a'⟩,ok,ab⟩ := from_any passed
  obtain ⟨rfl,rfl⟩ := of_decide_eq_true ab
  exact read_value h 8 i ok

private theorem misses_value {args xs : List ℚ} {ps : List Row} {bs : List Box} (h : Ledger args ps xs)
    (positive : 0<getRat args 0) (bound : ∀ i, (getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    {i : Nat} {q : ℚ} (passed : misses ps bs i q=true) : getRat xs i≠q := by
  simp only [misses,Bool.or_eq_true] at passed
  rcases passed with separated|aff
  · rcases of_decide_eq_true separated with low|high
    · exact ((bound i).2.trans_lt low).ne
    · exact (high.trans_le (bound i).1).ne'
  · obtain ⟨⟨c,k⟩,good,test⟩ := from_any aff
    obtain ⟨rfl,hk⟩ := of_decide_eq_true test
    have v := read_value h 8 i good
    dsimp only [val] at v
    rw [v]
    intro e
    exact (mul_ne_zero hk positive.ne') (by linarith [e])

private theorem first_index {α} [BEq α] [LawfulBEq α] (l : List α) (t : α) {j : Nat}
    (hj : j<l.length) (atJ : l[j]=t) (before : ∀ v∈l.take j,v≠t) : l.idxOf t=j := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simp only [List.getElem_cons_zero] at atJ; subst t; simp
    | succ j =>
      have ne : a≠t := before _ (by simp)
      have h := ih (j:=j) (by simpa using hj) (by simpa using atJ)
        (fun v hv => before v (by simp [hv]))
      simp [List.idxOf_cons,ne,Ne.symm ne,h]

theorem opening {c : Chart} {cs : List (Rect Nat)} {args xs : List ℚ} {p : List Row} {bs : List Box}
    {j : Nat} (ledger : Ledger args p xs) (pos : 0<getRat args 0)
    (bounds : ∀ i, (getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    (ok : check c cs p bs j=true) (rs : List (Rect ℚ)) (marks : List (List Vertex)) (d : ℚ) :
    (atDoor d ((1/320)*getRat args 0) (c.draw (packed cs xs rs marks))).isSome=true := by
  let data := packed cs xs rs marks
  let f := chartPt (selected (pool false data) c.x) (selected (pool true data) c.y)
  let q := c.cycle.points
  obtain ⟨sz,rest⟩ := andParts ok
  obtain ⟨prev,last⟩ := andParts rest
  obtain ⟨before,after⟩ := andParts last
  have size : j+1<q.length := of_decide_eq_true sz
  have corner (v : Index) (dx : ℚ) (hv : atCorner c cs p v dx=true) : f v=(dx*getRat args 0,1) := by
    obtain ⟨u,hu,hi⟩ := from_any hv
    obtain ⟨l,r⟩ := andParts hi
    have value := node_value hu xs rs marks
    change f v=_ at value
    rw [value,fixed_value ledger l,fixed_value ledger r]
    simp
  have earlier (v) (hv : v∈q.take j) : f v≠(0,1) := by
    obtain ⟨u,hu,h⟩ := from_any (List.all_eq_true.mp prev v hv)
    have value := node_value hu xs rs marks
    change f v=_ at value
    intro eq
    rw [value] at eq
    rcases Bool.or_eq_true_iff.mp h with x|y
    · exact misses_value ledger pos bounds x (congrArg Prod.fst eq)
    · exact misses_value ledger pos bounds y (congrArg Prod.snd eq)
  have J : j<q.length := by omega
  have L : f q[j]=(0,1) := by
    have h := corner _ _ before
    change f (q.getD j (0,0))=(0*getRat args 0,1) at h
    simpa only [List.getD_eq_getElem (l:=q) (d:=(0,0)) J,zero_mul] using h
  have R : f q[j+1]=((1/320)*getRat args 0,1) := by
    have h := corner _ _ after
    change f (q.getD (j+1) (0,0))=((1/320)*getRat args 0,1) at h
    simpa only [List.getD_eq_getElem (l:=q) (d:=(0,0)) size] using h
  have first : (q.map f).idxOf (0,1)=j := by
    apply first_index _ _ (by simpa using J) (by simpa using L)
    rw [← List.map_take]
    intro z hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    exact earlier v hv
  change (atDoor d _ (q.map f)).isSome=true
  unfold atDoor
  simp only [first,List.length_map,Nat.not_le.mpr J,decide_false,Bool.false_or,Nat.mod_eq_of_lt size,
    List.getD_eq_getElem (l:=q.map f) (d:=(0,0)) (by simpa using size),List.getElem_map,R]
  simp

theorem coordinate_open (t : Layout) (c : Chart) {ab : List Box} {args : List ℚ}
    (parameters : Encloses ab (args.map ((↑) : ℚ → ℝ))) (pos : 0<getRat args 0)
    (checked : ok ab [] (t.baseRows++t.rest)=true) {j : Nat}
    (prefixCheck : check c t.cells (t.baseRows++t.rest).reverse (stack [] (t.baseRows++t.rest)) j=true)
    (extra : Data ℚ) (d : ℚ) :
    let g := t.coords args
    (atDoor d ((1/320)*getRat args 0) (c.draw (g.1++extra.1,g.2++extra.2))).isSome=true := by
  let allRows := t.baseRows++t.rest
  let xs := execRat args [] allRows
  have data : Ledger args allRows.reverse xs := by simpa using exec_ledger (Ledger.nil (args:=args)) allRows
  have bound := lookup_bound (xs:=[]) parameters (by exact empty_encloses) checked
  have found := opening data pos bound prefixCheck extra.1 (t.roles.map (readRole xs)++extra.2) d
  simpa only [packed,xs,allRows,exec_append,Layout.coords] using found

end ArtGallery.Orthogonal.BoundaryPoint.DoorRead
end
