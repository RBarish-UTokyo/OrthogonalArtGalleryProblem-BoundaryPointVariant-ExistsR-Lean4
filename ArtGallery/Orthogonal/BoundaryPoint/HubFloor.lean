module

public import ArtGallery.Orthogonal.BoundaryPoint.HubColumns
public import ArtGallery.Orthogonal.BoundaryPoint.HubComb

/-! # The hub boundary inside a shaft column

Every edge of the hub cycle is horizontal on the floor or on the low roof,
lies in a vertical strip between two shaft columns (dividers, the east side,
the west end), or lies in a foot, a shaft or a cap rectangle. Hence a hub
boundary point in the column of a base shaft is on the floor or at least at
the low roof. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubFloor
open RectContour BoundaryChart BankCoordinates Geometry HubColumns HubComb

/-- A closed vertical strip meeting no shaft column and no foot column. -/
def Gap (count : Nat) (ss : List ℚ) (u v : ℚ) : Prop :=
  (∀ x∈ss, v<x ∨ x+3/2<u) ∧ ∀ j<count, v<door j+100-1/1000 ∨ door j+100+1/1000<u

/-- Hub edges: on the floor, on the low roof, in a gap strip, in a foot, in a shaft, or on a cap top. -/
def Sec2 (f : ℚ) (count : Nat) (ss : List ℚ) (a b : Vertex) : Prop :=
  (a.2=f ∧ b.2=f) ∨ (a.2=-6 ∧ b.2=-6) ∨ (∃ u v, Gap count ss u v ∧ u≤a.1 ∧ a.1≤v ∧ u≤b.1 ∧ b.1≤v) ∨
    (∃ j<count, FootC f j a ∧ FootC f j b) ∨ (∃ x∈ss, ShaftC f x a ∧ ShaftC f x b) ∨
    (a.2=1 ∧ b.2=1)

section Chains
variable {f : ℚ} {count : Nat} {ss : List ℚ}

/-- A nonempty chain whose ends satisfy `E`. -/
structure Piece (E : Vertex → Prop) (f : ℚ) (count : Nat) (ss : List ℚ) (l : List Vertex) : Prop where
  chain : l.IsChain (Sec2 f count ss)
  first : ∀ p∈l.head?, E p
  last : ∀ p∈l.getLast?, E p
  ne : l≠[]

private theorem append_or {α : Type} {a b : Option α} {p : α} (h : p∈a.or b) : p∈a ∨ p∈b := by
  cases a <;> simp_all

theorem Piece.append {E : Vertex → Prop} (EE : ∀ a b, E a → E b → Sec2 f count ss a b) {l r : List Vertex}
    (a : Piece E f count ss l) (b : Piece E f count ss r) : Piece E f count ss (l++r) := by
  refine ⟨a.chain.append b.chain (fun u hu v hv => EE _ _ (a.last _ hu) (b.first _ hv)),?_,?_,by simp [a.ne]⟩
  · intro p hp; rw [List.head?_append] at hp
    exact (append_or hp).elim (a.first p) (b.first p)
  · intro p hp; rw [List.getLast?_append] at hp
    exact (append_or hp).elim (b.last p) (a.last p)

theorem flatten {E : Vertex → Prop} (EE : ∀ a b, E a → E b → Sec2 f count ss a b) {α : Type}
    (l : List α) (g : α → List Vertex) (h : ∀ a∈l,Piece E f count ss (g a)) :
    (l.flatMap g).IsChain (Sec2 f count ss) ∧ (∀ p∈(l.flatMap g).head?, E p) ∧ (∀ p∈(l.flatMap g).getLast?, E p) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    obtain ⟨c,fi,la⟩ := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [List.flatMap_cons]
    refine ⟨ha.chain.append c (fun u hu v hv => EE _ _ (ha.last _ hu) (fi _ hv)),?_,?_⟩
    · intro p hp; rw [List.head?_append] at hp
      exact (append_or hp).elim (ha.first p) (fi p)
    · intro p hp; rw [List.getLast?_append] at hp
      exact (append_or hp).elim (la p) (ha.last p)

theorem one_type {l : List Vertex} {P : Vertex → Prop} (E : Vertex → Prop) (cover : ∀ p∈l,P p)
    (edge : ∀ a b, P a → P b → Sec2 f count ss a b) (start : ∀ p∈l.head?,E p) (finish : ∀ p∈l.getLast?,E p)
    (ne : l≠[]) : Piece E f count ss l := by
  refine ⟨List.isChain_iff_getElem.mpr ?_,start,finish,ne⟩
  intro i hi
  exact edge _ _ (cover _ (List.getElem_mem (by omega))) (cover _ (List.getElem_mem hi))

end Chains

theorem pw_cases {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {x y : α}, x∈l → y∈l →
    x=y ∨ R x y ∨ R y x
  | [],_,_,_,hx,_ => by simp at hx
  | a::l,h,x,y,hx,hy => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with rfl|hx' <;> rcases List.mem_cons.mp hy with rfl|hy'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (h.1 _ hy'))
    · exact Or.inr (Or.inr (h.1 _ hx'))
    · exact pw_cases h.2 hx' hy'

theorem pair_gap {ss : List ℚ} (placed : Placed ss) {x y : ℚ} (hx : x∈ss) (hy : y∈ss) :
    x=y ∨ x+10≤y ∨ y+10≤x := pw_cases placed.sorted hx hy

/-- Appending a chain whose head satisfies `E` to a chain whose last vertex satisfies `E`. -/
theorem app {R : Vertex → Vertex → Prop} {E : Vertex → Prop} (EE : ∀ a b, E a → E b → R a b) {l r : List Vertex}
    (hl : l.IsChain R ∧ ∀ p∈l.getLast?, E p) (hr : r.IsChain R ∧ (∀ p∈r.head?, E p) ∧ ∀ p∈r.getLast?, E p) :
    (l++r).IsChain R ∧ ∀ p∈(l++r).getLast?, E p := by
  refine ⟨hl.1.append hr.1 (fun u hu v hv => EE _ _ (hl.2 _ hu) (hr.2.1 _ hv)),?_⟩
  intro p hp; rw [List.getLast?_append] at hp
  cases h : r.getLast? with
  | none => rw [h] at hp; exact hl.2 p (by simpa using hp)
  | some q => rw [h] at hp; simp at hp; subst hp; exact hr.2.2 _ h

theorem door_sub (i j : Nat) : door i-door j=2000*((j:ℚ)-i) := by unfold door; ring

/-- A strip near door `j`, east of its foot or west of it, within its cap's reach. -/
theorem gap_near {count : Nat} {ss : List ℚ} (far : ∀ x∈ss, 1970<x) {j : Nat} {u v : ℚ}
    (side : door j+100+1/1000<u ∨ v<door j+100-1/1000) (lo : door j-1890≤u) (hi : v≤door j+1101/10)
    (huv : u≤v) : Gap count ss u v := by
  have dle : door j≤0 := by unfold door; exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  refine ⟨fun x hx => Or.inl (by linarith [far x hx]),fun i _ => ?_⟩
  rcases lt_trichotomy i j with h|h|h
  · left
    have h1 : (i:ℚ)+1≤j := by exact_mod_cast h
    have := door_sub i j
    nlinarith
  · subst h; exact side.symm
  · right
    have h1 : (j:ℚ)+1 ≤ i := by exact_mod_cast h
    have := door_sub i j
    nlinarith

theorem contour2 (n k : Nat) (ss : List ℚ) (hn : 65≤n) (placed : Placed ss) :
    let l := hubCycle n (k+1) ss
    (l++l.take 1).IsChain (Sec2 (1-D n) (k+1) ss) := by
  let f := 1-D n
  let left := door k-30
  let right := ss.getLastD 0+10
  let start : Vertex := (left-1/10,f)
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have hf : f < -7 := by dsimp [f,D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) big]
  have dle (j : Nat) : door j≤0 := by unfold door; exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  let Fl : Vertex → Prop := fun p => p.2=f
  let Ce : Vertex → Prop := fun p => p.2=-6
  have FF : ∀ a b, Fl a → Fl b → Sec2 f (k+1) ss a b := fun a b ha hb => Or.inl ⟨ha,hb⟩
  have CC : ∀ a b, Ce a → Ce b → Sec2 f (k+1) ss a b := fun a b ha hb => Or.inr (Or.inl ⟨ha,hb⟩)
  have west (u v : ℚ) (hu : door k-1890≤u) (hv : v<door k+100-1/1000) (huv : u≤v) : Gap (k+1) ss u v :=
    gap_near (j:=k) placed.far (Or.inr hv) hu (by linarith) huv
  have feet (j : Nat) (hj : j<k+1) : Piece Fl f (k+1) ss (foot f j) := by
    refine one_type (P:=FootC f j) Fl ?_ (fun _ _ a b => Or.inr (Or.inr (Or.inr (Or.inl ⟨j,hj,a,b⟩)))) ?_ ?_ (by simp [foot])
    · intro z hz
      simp only [foot,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> dsimp [FootC] <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith
    · simp [foot,Fl]
    · simp [foot,Fl]
  have divs (x : ℚ) (hx : x∈ss) : Piece Fl f (k+1) ss (divider f x) := by
    have g : Gap (k+1) ss (x-3) (x-2) := by
      refine ⟨fun y hy => ?_,fun j _ => Or.inr ?_⟩
      · rcases pair_gap placed hy hx with rfl|h|h
        · left; linarith
        · right; linarith
        · left; linarith
      · have := dle j; have := placed.far x hx; linarith
    refine one_type (P:=fun p => x-3≤p.1 ∧ p.1≤x-2) Fl ?_
      (fun a b ha hb => Or.inr (Or.inr (Or.inl ⟨x-3,x-2,g,ha.1,ha.2,hb.1,hb.2⟩))) ?_ ?_ (by simp [divider])
    · intro z hz
      simp only [divider,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> dsimp <;> linarith
    · simp [divider,Fl]
    · simp [divider,Fl]
  have shafts (x : ℚ) (hx : x∈ss) : Piece Ce f (k+1) ss (shaft f x) := by
    refine one_type (P:=ShaftC f x) Ce ?_ (fun _ _ a b => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x,hx,a,b⟩))))) ?_ ?_
      (by simp [shaft])
    · intro z hz
      simp only [shaft,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> dsimp [ShaftC] <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith
    · simp [shaft,Ce]
    · simp [shaft,Ce]
  have capEdges (j : Nat) (hj : j<k+1) :
      [(door j+110,-6),(door j+110,1-1/10000),(door j+110+1/10,1-1/10000),(door j+110+1/10,1),(door j-30,(1:ℚ))].IsChain
        (Sec2 f (k+1) ss) := by
    have g1 : Gap (k+1) ss (door j+110) (door j+110) := gap_near (j:=j) placed.far (Or.inl (by linarith)) (by linarith) (by linarith) le_rfl
    have g2 : Gap (k+1) ss (door j+110) (door j+110+1/10) := gap_near (j:=j) placed.far (Or.inl (by linarith)) (by linarith) (by linarith) (by linarith)
    have g3 : Gap (k+1) ss (door j+110+1/10) (door j+110+1/10) := gap_near (j:=j) placed.far (Or.inl (by linarith)) (by linarith) (by linarith) le_rfl
    simp only [List.isChain_cons_cons,List.isChain_singleton,and_true]
    refine ⟨Or.inr (Or.inr (Or.inl ⟨_,_,g1,le_rfl,le_rfl,le_rfl,le_rfl⟩)),Or.inr (Or.inr (Or.inl ⟨_,_,g2,le_rfl,by linarith,by linarith,le_rfl⟩)),
      Or.inr (Or.inr (Or.inl ⟨_,_,g3,le_rfl,le_rfl,le_rfl,le_rfl⟩)),Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))))⟩
  have g30 (j : Nat) : Gap (k+1) ss (door j-30) (door j-30) :=
    gap_near (j:=j) placed.far (Or.inr (by linarith)) (by linarith) (by linarith) le_rfl
  have caps (j : Nat) (hj : j+1<k+1) : Piece Ce f (k+1) ss (capPath (k+1) j) := by
    refine ⟨?_,by simp [capPath,hj,Ce],by simp [capPath,hj,Ce],by simp [capPath]⟩
    have e : capPath (k+1) j=[(door j+110,-6),(door j+110,1-1/10000),(door j+110+1/10,1-1/10000),(door j+110+1/10,1),
        (door j-30,(1:ℚ))]++[(door j-30,-6)] := by simp [capPath,hj]
    rw [e]
    exact (capEdges j (by omega)).append (by simp) (fun u hu v hv => by
      simp at hu hv; subst hu; subst hv
      exact Or.inr (Or.inr (Or.inl ⟨_,_,g30 j,le_rfl,le_rfl,le_rfl,le_rfl⟩)))
  -- the floor run: start, feet, dividers, east side bottom
  have fs := flatten FF (List.range (k+1)).reverse (foot f) (fun j hj => feet j (List.mem_range.mp (List.mem_reverse.mp hj)))
  have ds := flatten FF ss.tail (divider f) (fun x hx => divs x (List.mem_of_mem_tail hx))
  have rs := flatten CC ss.reverse (shaft f) (fun x hx => shafts x (List.mem_reverse.mp hx))
  have cs := flatten CC (List.range k) (capPath (k+1)) (fun j hj => caps j (Nat.succ_lt_succ (List.mem_range.mp hj)))
  have hr : ∀ x∈ss, x+3/2<right := fun x hx => by have := last_bound placed x hx; simp only [right]; linarith
  have lastC : (capPath (k+1) k++[(door k-30,f+1/100000000)]).IsChain (Sec2 f (k+1) ss) := by
    have e : capPath (k+1) k=[(door k+110,-6),(door k+110,1-1/10000),(door k+110+1/10,1-1/10000),(door k+110+1/10,1),
        (door k-30,(1:ℚ))] := by simp [capPath]
    rw [e]
    exact (capEdges k (by omega)).append (by simp) (fun u hu v hv => by
      simp at hu hv; subst hu; subst hv
      exact Or.inr (Or.inr (Or.inl ⟨_,_,g30 k,le_rfl,le_rfl,le_rfl,le_rfl⟩)))
  -- assemble
  have s0 : ([start]:List Vertex).IsChain (Sec2 f (k+1) ss) ∧ ∀ p∈([start]:List Vertex).getLast?, Fl p := by
    simp [start,Fl]
  have s1 := app FF s0 fs
  have s2 := app FF s1 ds
  have s3 := app FF s2 (r:=[(right,f)]) (by simp [Fl])
  have r0 : ([(right,-6)]:List Vertex).IsChain (Sec2 f (k+1) ss) ∧ ∀ p∈([(right,-6)]:List Vertex).getLast?, Ce p := by
    simp [Ce]
  have r1 := app CC r0 rs
  have r2 := app CC r1 cs
  have R3 := r2.1.append lastC (fun u hu v hv => CC _ _ (r2.2 _ hu) (by simp [capPath] at hv; subst hv; simp [Ce]))
  have FR := s3.1.append R3 (fun u hu v hv => by
    simp [List.getLast?_append,List.getLast?_cons] at hu hv; subst hu; subst hv
    exact Or.inr (Or.inr (Or.inl ⟨right,right,⟨fun x hx => Or.inr (hr x hx),fun j _ => Or.inr (by
      have := dle j; have := placed.far _ (List.getLast_mem placed.exists_slot); have := last_bound placed _ (List.getLast_mem placed.exists_slot)
      simp only [right]; linarith)⟩,le_refl _,le_refl _,le_refl _,le_refl _⟩)))
  have fin : ([(left-1/10,f+1/100000000),start]:List Vertex).IsChain (Sec2 f (k+1) ss) := by
    have := dle k
    simp only [List.isChain_cons_cons,List.isChain_singleton,and_true]
    exact Or.inr (Or.inr (Or.inl ⟨left-1/10,left-1/10,west _ _ (by simp only [left]; linarith) (by simp only [left]; linarith) le_rfl,
      le_refl _,le_refl _,le_refl _,le_refl _⟩))
  have all := FR.append fin (fun u hu v hv => by
    have := dle k
    simp [List.getLast?_append,List.getLast?_cons] at hu hv; subst hu; subst hv
    exact Or.inr (Or.inr (Or.inl ⟨left-1/10,left,west _ _ (by simp only [left]; linarith) (by simp only [left]; linarith) (by simp only [left]; linarith),
      by simp only [left]; linarith,by norm_num [left],by norm_num [left],by norm_num [left]⟩)))
  have split : (List.range (k+1)).flatMap (capPath (k+1))=(List.range k).flatMap (capPath (k+1))++capPath (k+1) k := by
    rw [List.range_succ]; simp
  have beg : (hubCycle n (k+1) ss).take 1=[start] := rfl
  change ((hubCycle n (k+1) ss)++(hubCycle n (k+1) ss).take 1).IsChain _
  rw [beg]
  simp only [hubCycle,split,Nat.add_sub_cancel]
  simpa only [start,left,right,f,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using all

private theorem adjacent2 {f : ℚ} {count : Nat} {slots : List ℚ} {l : List Vertex}
    (c : (l++l.take 1).IsChain (Sec2 f count slots)) (i : Nat) (h : i<l.length) :
    Sec2 f count slots (l.getD i (0,0)) (l.getD ((i+1)%l.length) (0,0)) := by
  have le : 0<l.length := by omega
  have sz : (l.take 1).length=1 := by simp; omega
  have step := List.isChain_iff_getElem.mp c i (by simp only [List.length_append,sz]; omega)
  rw [List.getElem_append_left h] at step
  rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (Nat.mod_lt _ le)]
  by_cases next : i+1<l.length
  · simpa [List.getElem_append_left next,Nat.mod_eq_of_lt next] using step
  · have endEq : i+1=l.length := by omega
    simpa [endEq,List.getElem_append_right] using step

/-- A hub boundary point in the column of a base shaft is on the floor or at least at the low roof. -/
theorem column {rows n : Nat} (hr : 0<rows) (hn : 65≤n) {ss : List ℚ} (placed : Placed ss) {q : Point}
    (hq : q∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).boundary) {x : ℚ} (hx : x∈ss)
    (h0 : (x:ℝ)≤q.1) (h1 : q.1≤((x+3/2:ℚ):ℝ)) : q.2=((1-D n:ℚ):ℝ) ∨ -6≤q.2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let l := hubCycle n (k+1) ss
  let P : Polygon := ⟨l.map ratPoint⟩
  obtain ⟨i,hi,edge⟩ := hq
  have size : P.n=l.length := by simp [P,Polygon.n]
  rw [size] at hi
  change q∈ArtGallery.segment (P.vtx i) (P.vtx ((i+1)%P.n)) at edge
  rw [size] at edge
  have vertex (j : Nat) (hj : j<l.length) : P.vtx j=ratPoint (l.getD j (0,0)) := by
    change (l.map ratPoint).getD j (0,0)=_
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map,List.getD_eq_getElem _ _ hj]
  rw [vertex _ hi,vertex _ (Nat.mod_lt _ (by omega))] at edge
  have sec := adjacent2 (contour2 n k ss hn placed) i hi
  set a := l.getD i (0,0)
  set b := l.getD ((i+1)%l.length) (0,0)
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp edge
  simp only [lerp_fst,lerp_snd,ratPoint] at h0 h1 ⊢
  have hfar := placed.far x hx
  have dle (j : Nat) : (door j:ℝ)≤0 := by
    unfold door; push_cast; nlinarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]
  have xa := HighStep.interpolated (a.1:ℝ) (b.1:ℝ) ht hu
  have ya := HighStep.interpolated (a.2:ℝ) (b.2:ℝ) ht hu
  rcases sec with ⟨A,B⟩|⟨A,B⟩|⟨u,v,g,A1,A2,B1,B2⟩|⟨j,_,A,B⟩|⟨y,_,A,B⟩|⟨A,B⟩
  · left; rw [A,B]; push_cast; ring
  · right; rw [A,B]; push_cast; linarith
  · exfalso
    have l1 : (u:ℝ)≤min (a.1:ℝ) b.1 := le_min (by exact_mod_cast A1) (by exact_mod_cast B1)
    have l2 : max (a.1:ℝ) b.1≤v := max_le (by exact_mod_cast A2) (by exact_mod_cast B2)
    rcases g.1 x hx with c|c
    · have : (v:ℝ)<x := by exact_mod_cast c
      linarith [xa.2]
    · have : ((x+3/2:ℚ):ℝ)<u := by exact_mod_cast c
      linarith [xa.1]
  · exfalso
    simp only [FootC] at A B
    have := dle j
    have c1 : (a.1:ℝ)≤((door j+100+1/1000:ℚ):ℝ) := by exact_mod_cast A.2.1
    have c2 : (b.1:ℝ)≤((door j+100+1/1000:ℚ):ℝ) := by exact_mod_cast B.2.1
    push_cast at c1 c2 hfar
    have : (1970:ℝ)<x := by exact_mod_cast hfar
    linarith [xa.2,max_le c1 c2]
  · right
    simp only [ShaftC] at A B
    have c1 : (-6:ℝ)≤a.2 := by exact_mod_cast A.2.2.1
    have c2 : (-6:ℝ)≤b.2 := by exact_mod_cast B.2.2.1
    linarith [ya.1,le_min c1 c2]
  · right; rw [A,B]; push_cast; linarith

/-- A hub boundary point in the column of a foot is at most on the floor, on the low roof, or on a cap top. -/
theorem foot_col {rows n : Nat} (hr : 0<rows) (hn : 65≤n) {ss : List ℚ} (placed : Placed ss) {q : Point}
    (hq : q∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).boundary) {m : Nat} (hm : m<rows)
    (h0 : ((door m+100-1/1000:ℚ):ℝ)≤q.1) (h1 : q.1≤((door m+100+1/1000:ℚ):ℝ)) :
    q.2≤((1-D n:ℚ):ℝ) ∨ q.2=-6 ∨ q.2=1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let l := hubCycle n (k+1) ss
  let P : Polygon := ⟨l.map ratPoint⟩
  obtain ⟨i,hi,edge⟩ := hq
  have size : P.n=l.length := by simp [P,Polygon.n]
  rw [size] at hi
  change q∈ArtGallery.segment (P.vtx i) (P.vtx ((i+1)%P.n)) at edge
  rw [size] at edge
  have vertex (j : Nat) (hj : j<l.length) : P.vtx j=ratPoint (l.getD j (0,0)) := by
    change (l.map ratPoint).getD j (0,0)=_
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map,List.getD_eq_getElem _ _ hj]
  rw [vertex _ hi,vertex _ (Nat.mod_lt _ (by omega))] at edge
  have sec := adjacent2 (contour2 n k ss hn placed) i hi
  set a := l.getD i (0,0)
  set b := l.getD ((i+1)%l.length) (0,0)
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp edge
  simp only [lerp_fst,lerp_snd,ratPoint] at h0 h1 ⊢
  have dle (j : Nat) : (door j:ℝ)≤0 := by
    unfold door; push_cast; nlinarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]
  have xa := HighStep.interpolated (a.1:ℝ) (b.1:ℝ) ht hu
  have ya := HighStep.interpolated (a.2:ℝ) (b.2:ℝ) ht hu
  have hf : ((1-D n:ℚ):ℝ)< -7 := HubColumns.f_lt hn
  rcases sec with ⟨A,B⟩|⟨A,B⟩|⟨u,v,g,A1,A2,B1,B2⟩|⟨j,_,A,B⟩|⟨y,hy,A,B⟩|⟨A,B⟩
  · left; rw [A,B]; push_cast; linarith
  · right; left; rw [A,B]; push_cast; ring
  · exfalso
    have l1 : (u:ℝ)≤min (a.1:ℝ) b.1 := le_min (by exact_mod_cast A1) (by exact_mod_cast B1)
    have l2 : max (a.1:ℝ) b.1≤v := max_le (by exact_mod_cast A2) (by exact_mod_cast B2)
    rcases g.2 m (by omega) with c|c
    · have : (v:ℝ)<((door m+100-1/1000:ℚ):ℝ) := by exact_mod_cast c
      linarith [xa.2]
    · have : ((door m+100+1/1000:ℚ):ℝ)<u := by exact_mod_cast c
      linarith [xa.1]
  · left
    simp only [FootC] at A B
    have c1 : (a.2:ℝ)≤((1-D n:ℚ):ℝ) := by exact_mod_cast A.2.2.2
    have c2 : (b.2:ℝ)≤((1-D n:ℚ):ℝ) := by exact_mod_cast B.2.2.2
    linarith [ya.2,max_le c1 c2]
  · exfalso
    simp only [ShaftC] at A B
    have hfar := placed.far y hy
    have c1 : (y:ℝ)≤a.1 := by exact_mod_cast A.1
    have c2 : (y:ℝ)≤b.1 := by exact_mod_cast B.1
    have : (1970:ℝ)<y := by exact_mod_cast hfar
    have di := dle m
    push_cast at h1
    linarith [xa.1,le_min c1 c2]
  · right; right; rw [A,B]; push_cast; ring

end ArtGallery.Orthogonal.BoundaryPoint.HubFloor
end
