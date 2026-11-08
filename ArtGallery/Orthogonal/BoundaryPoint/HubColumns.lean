module

public import ArtGallery.Orthogonal.BoundaryPoint.HubSky

/-! # Shaft and foot columns of the actual hub

Every edge of the emitted hub cycle lies in one of four kinds of closed
rectangles: the floor band between the floor `y = f` and the low roof
`y = -6`, a foot below the floor at `door j + 100`, a base shaft above the low
roof at a slot, or a cap at a door. Casting a vertical ray from a filled point
therefore shows:

* a filled point above the low roof and east of every cap lies in the column of
  one base shaft, below its top;
* a filled point below the floor lies in the column of one foot, above its
  bottom. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubColumns
open RectContour BoundaryChart BankCoordinates Geometry

def Mid (f : ℚ) (p : Vertex) := f≤p.2 ∧ p.2≤ -6
def FootC (f : ℚ) (j : Nat) (p : Vertex) :=
  door j+100-1/1000≤p.1 ∧ p.1≤door j+100+1/1000 ∧ 2*f≤p.2 ∧ p.2≤f
def ShaftC (f x : ℚ) (p : Vertex) := x≤p.1 ∧ p.1≤x+3/2 ∧ -6≤p.2 ∧ p.2≤ -6-f
def CapC (f : ℚ) (j : Nat) (p : Vertex) := door j-30≤p.1 ∧ p.1≤door j+1101/10 ∧ f≤p.2 ∧ p.2≤1

def Sec (f : ℚ) (count : Nat) (slots : List ℚ) (a b : Vertex) : Prop :=
  (Mid f a ∧ Mid f b) ∨ (∃ j<count, FootC f j a ∧ FootC f j b) ∨
    (∃ x∈slots, ShaftC f x a ∧ ShaftC f x b) ∨ (∃ j<count, CapC f j a ∧ CapC f j b)

structure Piece (f : ℚ) (count : Nat) (slots : List ℚ) (l : List Vertex) : Prop where
  chain : l.IsChain (Sec f count slots)
  first : ∀ p∈l.head?, Mid f p
  last : ∀ p∈l.getLast?, Mid f p

section Pieces
variable {f : ℚ} {count : Nat} {slots : List ℚ}

private theorem append_or {α : Type} {a b : Option α} {p : α} (h : p∈a.or b) : p∈a ∨ p∈b := by
  cases a <;> simp_all

theorem Piece.append {l r : List Vertex} (a : Piece f count slots l) (b : Piece f count slots r) :
    Piece f count slots (l++r) := by
  refine ⟨a.chain.append b.chain (fun u hu v hv => Or.inl ⟨a.last _ hu,b.first _ hv⟩),?_,?_⟩
  · intro p hp; rw [List.head?_append] at hp
    exact (append_or hp).elim (a.first p) (b.first p)
  · intro p hp; rw [List.getLast?_append] at hp
    exact (append_or hp).elim (b.last p) (a.last p)

private theorem one_type {l : List Vertex} {P : Vertex → Prop}
    (cover : ∀ p∈l,P p) (edge : ∀ a b, P a → P b → Sec f count slots a b)
    (start : ∀ p∈l.head?,Mid f p) (finish : ∀ p∈l.getLast?,Mid f p) : Piece f count slots l := by
  refine ⟨List.isChain_iff_getElem.mpr ?_,start,finish⟩
  intro i hi
  exact edge _ _ (cover _ (List.getElem_mem (by omega))) (cover _ (List.getElem_mem hi))

private theorem low {l : List Vertex} (L : ∀ p∈l,Mid f p) : Piece f count slots l :=
  one_type L (fun _ _ a b => Or.inl ⟨a,b⟩)
    (fun _ h => L _ (List.mem_of_mem_head? h)) (fun _ h => L _ (List.mem_of_mem_getLast? h))

private theorem flatten {α : Type} (l : List α) (g : α → List Vertex) (h : ∀ a∈l,Piece f count slots (g a)) :
    Piece f count slots (l.flatMap g) := by
  induction l with
  | nil => exact low (by simp)
  | cons a l ih => exact (h _ List.mem_cons_self).append (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)))

end Pieces

theorem contour (n k : Nat) (slots : List ℚ) (hn : 65≤n) :
    let l := hubCycle n (k+1) slots
    (l++l.take 1).IsChain (Sec (1-D n) (k+1) slots) := by
  let f := 1-D n
  let left := door k-30
  let right := slots.getLastD 0+10
  let start : Vertex := (left-1/10,f)
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have hf : f < -7 := by dsimp [f,D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) big]
  have feet (j : Nat) (hj : j<k+1) : Piece f (k+1) slots (foot f j) := by
    refine one_type (P:=FootC f j) ?_ (fun _ _ a b => Or.inr (Or.inl ⟨j,hj,a,b⟩)) ?_ ?_
    · intro z hz
      simp only [foot,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> dsimp [FootC] <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith
    · simp [foot,Mid]; linarith
    · simp [foot,Mid]; linarith
  have divs (x : ℚ) : Piece f (k+1) slots (divider f x) := by
    apply low; intro z hz
    simp only [divider,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp [Mid] <;> constructor <;> linarith
  have shafts (x : ℚ) (hx : x∈slots) : Piece f (k+1) slots (shaft f x) := by
    refine one_type (P:=ShaftC f x) ?_ (fun _ _ a b => Or.inr (Or.inr (Or.inl ⟨x,hx,a,b⟩))) ?_ ?_
    · intro z hz
      simp only [shaft,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> dsimp [ShaftC] <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith
    · simp [shaft,Mid]; linarith
    · simp [shaft,Mid]; linarith
  have caps (j : Nat) (hj : j+1<k+1) : Piece f (k+1) slots (capPath (k+1) j) := by
    refine one_type (P:=CapC f j) ?_ (fun _ _ a b => Or.inr (Or.inr (Or.inr ⟨j,by omega,a,b⟩))) ?_ ?_
    · intro z hz
      simp only [capPath,hj,ite_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with (rfl|rfl|rfl|rfl|rfl)|rfl <;> dsimp [CapC] <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith
    · simp [capPath,hj,Mid]; linarith
    · simp [capPath,hj,Mid]; linarith
  have lastCap : Piece f (k+1) slots (capPath (k+1) k++[(door k-30,f+1/100000000)]) := by
    refine one_type (P:=CapC f k) ?_ (fun _ _ a b => Or.inr (Or.inr (Or.inr ⟨k,by omega,a,b⟩))) ?_ ?_
    · intro z hz
      simp [capPath] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp [CapC] <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith
    · simp [capPath,Mid]; linarith
    · simp [capPath,Mid]; first | linarith | (constructor <;> linarith)
  have side : Piece f (k+1) slots [(right,f),(right,-6)] := by
    apply low; intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> dsimp [Mid] <;> constructor <;> linarith
  have a : Piece f (k+1) slots [start] := low (by simp [start,Mid]; linarith)
  have finish : Piece f (k+1) slots [(left-1/10,f+1/100000000),start] := by
    apply low; intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> dsimp [Mid,start] <;> constructor <;> linarith
  have floor := ((a.append (flatten (List.range (k+1)).reverse (foot f)
      (fun j hj => feet j (List.mem_range.mp (List.mem_reverse.mp hj))))).append
    (flatten slots.tail (divider f) (fun x _ => divs x))).append side
  have roof := (flatten slots.reverse (shaft f) (fun x hx => shafts x (List.mem_reverse.mp hx))).append
    (flatten (List.range k) (capPath (k+1)) (fun j hj => caps j (Nat.succ_lt_succ (List.mem_range.mp hj))))
  have full := (((floor.append roof).append lastCap).append finish).chain
  have split : (List.range (k+1)).flatMap (capPath (k+1))=(List.range k).flatMap (capPath (k+1))++capPath (k+1) k := by
    rw [List.range_succ]; simp
  have beg : (hubCycle n (k+1) slots).take 1=[start] := rfl
  change ((hubCycle n (k+1) slots)++(hubCycle n (k+1) slots).take 1).IsChain _
  rw [beg]
  simp only [hubCycle,split,Nat.add_sub_cancel]
  simpa only [start,left,right,f,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using full

private theorem adjacent {f : ℚ} {count : Nat} {slots : List ℚ} {l : List Vertex}
    (c : (l++l.take 1).IsChain (Sec f count slots)) (i : Nat) (h : i<l.length) :
    Sec f count slots (l.getD i (0,0)) (l.getD ((i+1)%l.length) (0,0)) := by
  have le : 0<l.length := by omega
  have sz : (l.take 1).length=1 := by simp; omega
  have step := List.isChain_iff_getElem.mp c i (by simp only [List.length_append,sz]; omega)
  rw [List.getElem_append_left h] at step
  rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (Nat.mod_lt _ le)]
  by_cases next : i+1<l.length
  · simpa [List.getElem_append_left next,Nat.mod_eq_of_lt next] using step
  · have endEq : i+1=l.length := by omega
    simpa [endEq,List.getElem_append_right] using step

/-- Real regions of the four kinds. -/
def RMid (f : ℚ) (q : Point) := (f:ℝ)≤q.2 ∧ q.2≤ -6
def RFoot (f : ℚ) (j : Nat) (q : Point) :=
  ((door j+100-1/1000:ℚ):ℝ)≤q.1 ∧ q.1≤((door j+100+1/1000:ℚ):ℝ) ∧ ((2*f:ℚ):ℝ)≤q.2 ∧ q.2≤(f:ℝ)
def RShaft (f x : ℚ) (q : Point) := (x:ℝ)≤q.1 ∧ q.1≤((x+3/2:ℚ):ℝ) ∧ -6≤q.2 ∧ q.2≤((-6-f:ℚ):ℝ)
def RCap (f : ℚ) (j : Nat) (q : Point) :=
  ((door j-30:ℚ):ℝ)≤q.1 ∧ q.1≤((door j+1101/10:ℚ):ℝ) ∧ (f:ℝ)≤q.2 ∧ q.2≤1

private theorem box {u v : ℚ} {a b : Vertex} (ha : u≤a.1 ∧ a.1≤v) (hb : u≤b.1 ∧ b.1≤v) {t : ℝ}
    (ht : 0≤t) (hu : t≤1) : (u:ℝ)≤(a.1:ℝ)+t*((b.1:ℝ)-a.1) ∧ (a.1:ℝ)+t*((b.1:ℝ)-a.1)≤(v:ℝ) := by
  have x := HighStep.interpolated (a.1:ℝ) (b.1:ℝ) ht hu
  constructor
  · exact (le_min (by exact_mod_cast ha.1) (by exact_mod_cast hb.1)).trans x.1
  · exact x.2.trans (max_le (by exact_mod_cast ha.2) (by exact_mod_cast hb.2))

private theorem boxY {u v : ℚ} {a b : Vertex} (ha : u≤a.2 ∧ a.2≤v) (hb : u≤b.2 ∧ b.2≤v) {t : ℝ}
    (ht : 0≤t) (hu : t≤1) : (u:ℝ)≤(a.2:ℝ)+t*((b.2:ℝ)-a.2) ∧ (a.2:ℝ)+t*((b.2:ℝ)-a.2)≤(v:ℝ) := by
  have x := HighStep.interpolated (a.2:ℝ) (b.2:ℝ) ht hu
  constructor
  · exact (le_min (by exact_mod_cast ha.1) (by exact_mod_cast hb.1)).trans x.1
  · exact x.2.trans (max_le (by exact_mod_cast ha.2) (by exact_mod_cast hb.2))

private theorem on_side {f : ℚ} {count : Nat} {slots : List ℚ} {a b : Vertex} (c : Sec f count slots a b)
    {q : Point} (mem : q∈ArtGallery.segment (ratPoint a) (ratPoint b)) :
    RMid f q ∨ (∃ j<count, RFoot f j q) ∨ (∃ x∈slots, RShaft f x q) ∨ ∃ j<count, RCap f j q := by
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp mem
  simp only [lerp_fst,lerp_snd,ratPoint]
  rcases c with ⟨A,B⟩|⟨j,hj,A,B⟩|⟨x,hx,A,B⟩|⟨j,hj,A,B⟩
  · left
    have y := boxY (u:=f) (v:=-6) ⟨A.1,A.2⟩ ⟨B.1,B.2⟩ ht hu
    exact ⟨y.1,by simpa using y.2⟩
  · right; left
    have x' := box ⟨A.1,A.2.1⟩ ⟨B.1,B.2.1⟩ ht hu
    have y := boxY ⟨A.2.2.1,A.2.2.2⟩ ⟨B.2.2.1,B.2.2.2⟩ ht hu
    exact ⟨j,hj,x'.1,x'.2,y.1,y.2⟩
  · right; right; left
    have x' := box ⟨A.1,A.2.1⟩ ⟨B.1,B.2.1⟩ ht hu
    have y := boxY (u:=-6) ⟨A.2.2.1,A.2.2.2⟩ ⟨B.2.2.1,B.2.2.2⟩ ht hu
    exact ⟨x,hx,x'.1,x'.2,by simpa using y.1,y.2⟩
  · right; right; right
    have x' := box ⟨A.1,A.2.1⟩ ⟨B.1,B.2.1⟩ ht hu
    have y := boxY (v:=1) ⟨A.2.2.1,A.2.2.2⟩ ⟨B.2.2.1,B.2.2.2⟩ ht hu
    exact ⟨j,hj,x'.1,x'.2,y.1,by simpa using y.2⟩

/-- Every boundary point of the hub lies in one of the four kinds of rectangles. -/
theorem wall {rows n : Nat} (hr : 0<rows) (hn : 65≤n) {ss : List ℚ} {q : Point}
    (hq : q∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).boundary) :
    RMid (1-D n) q ∨ (∃ j<rows, RFoot (1-D n) j q) ∨ (∃ x∈ss, RShaft (1-D n) x q) ∨ ∃ j<rows, RCap (1-D n) j q := by
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
  exact on_side (adjacent (contour n k ss hn) i hi) edge

private theorem ray_hits {P : Polygon} {q d : Point} (hd : d≠0) (hq : q∈P.filled) :
    ∃ t : ℝ,0≤t ∧ q+t • d∈P.boundary := by
  by_contra! no
  have outside : q∉P.boundary := by simpa using no 0 (le_refl _)
  exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray P (d:=d) hd
    (by rintro _ ⟨t,ht,rfl⟩; exact no t ht) ((Jordan.mem_filled_iff_bounded P outside).mp hq)

private theorem door_le (j : Nat) : (door j:ℝ)≤0 := by
  unfold door; push_cast; nlinarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]

theorem f_lt {n : Nat} (hn : 65≤n) : (((1-D n):ℚ):ℝ)< -7 := by
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have : (1-D n:ℚ)< -7 := by dsimp [D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) big]
  exact_mod_cast this

/-- A filled hub point above the low roof and east of every cap lies in one shaft column. -/
theorem shaft_column {rows n : Nat} (hr : 0<rows) (hn : 65≤n) {ss : List ℚ} {q : Point}
    (hq : q∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).filled) (high : -6<q.2) (east : 1101/10<q.1) :
    ∃ x∈ss, (x:ℝ)≤q.1 ∧ q.1≤((x+3/2:ℚ):ℝ) ∧ q.2≤((-6-(1-D n):ℚ):ℝ) := by
  obtain ⟨t,ht,hm⟩ := ray_hits (d:=((0,1):Point)) (by simp) hq
  have hf := f_lt hn
  rcases wall hr hn hm with c|⟨j,_,c⟩|⟨x,hx,c⟩|⟨j,_,c⟩ <;>
    simp only [RMid,RFoot,RShaft,RCap,Geometry.add_fst,Geometry.smul_fst,Geometry.add_snd,Geometry.smul_snd,
      mul_zero,add_zero,mul_one] at c
  · linarith [c.2]
  · linarith [c.2.2.2]
  · exact ⟨x,hx,c.1,c.2.1,by linarith [c.2.2.2]⟩
  · have := door_le j
    push_cast at c
    linarith [c.2.1]

/-- A filled hub point below the floor lies in one foot column. -/
theorem foot_column {rows n : Nat} (hr : 0<rows) (hn : 65≤n) {ss : List ℚ} {q : Point}
    (hq : q∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).filled) (deep : q.2<(((1-D n):ℚ):ℝ)) :
    ∃ j<rows, ((door j+100-1/1000:ℚ):ℝ)≤q.1 ∧ q.1≤((door j+100+1/1000:ℚ):ℝ) ∧ (((2*(1-D n)):ℚ):ℝ)≤q.2 := by
  obtain ⟨t,ht,hm⟩ := ray_hits (d:=((0,-1):Point)) (by simp) hq
  have hf := f_lt hn
  rcases wall hr hn hm with c|⟨j,hj,c⟩|⟨x,hx,c⟩|⟨j,_,c⟩ <;>
    simp only [RMid,RFoot,RShaft,RCap,Geometry.add_fst,Geometry.smul_fst,Geometry.add_snd,Geometry.smul_snd,
      mul_zero,add_zero,mul_neg,mul_one] at c
  · linarith [c.1]
  · exact ⟨j,hj,c.1,c.2.1,by linarith [c.2.2.1]⟩
  · linarith [c.2.2.1]
  · linarith [c.2.2.1]

/-- Every filled hub point lies between the foot bottoms and the shaft tops. -/
theorem hub_range {rows n : Nat} (hr : 0<rows) (hn : 65≤n) {ss : List ℚ} {q : Point}
    (hq : q∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).filled) :
    (((2*(1-D n)):ℚ):ℝ)≤q.2 ∧ q.2≤((-6-(1-D n):ℚ):ℝ) := by
  have hf := f_lt hn
  constructor
  · obtain ⟨t,ht,hm⟩ := ray_hits (d:=((0,-1):Point)) (by simp) hq
    rcases wall hr hn hm with c|⟨j,hj,c⟩|⟨x,hx,c⟩|⟨j,_,c⟩ <;>
      simp only [RMid,RFoot,RShaft,RCap,Geometry.add_fst,Geometry.smul_fst,Geometry.add_snd,Geometry.smul_snd,
        mul_zero,add_zero,mul_neg,mul_one] at c <;> push_cast at c hf ⊢ <;> linarith
  · obtain ⟨t,ht,hm⟩ := ray_hits (d:=((0,1):Point)) (by simp) hq
    rcases wall hr hn hm with c|⟨j,hj,c⟩|⟨x,hx,c⟩|⟨j,_,c⟩ <;>
      simp only [RMid,RFoot,RShaft,RCap,Geometry.add_fst,Geometry.smul_fst,Geometry.add_snd,Geometry.smul_snd,
        mul_zero,add_zero,mul_one] at c <;> push_cast at c hf ⊢ <;> linarith

end ArtGallery.Orthogonal.BoundaryPoint.HubColumns
end
