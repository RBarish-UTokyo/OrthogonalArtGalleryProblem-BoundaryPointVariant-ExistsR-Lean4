module

public import ArtGallery.Orthogonal.BoundaryPoint.HubFloor

/-! # The edges of the hub on explicit lines

Every edge of the emitted hub cycle lies on the floor `y = f`, the low roof `y = -6`, a cap top
`y = 1`, a shaft top `y = -6-f`, a foot bottom `y = 2f`, or on one of finitely many explicit
vertical or horizontal pieces: shaft and foot sides, the five pieces of each floor divider, the cap
sides and terraces, the closed western step and the eastern side. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubEdges
open RectContour BoundaryChart BankCoordinates Geometry HubComb HubFloor

/-- A horizontal piece at height `y` between `x₀` and `x₁`. -/
def HS (y x₀ x₁ : ℚ) (a b : Vertex) : Prop := a.2=y ∧ b.2=y ∧ x₀≤a.1 ∧ a.1≤x₁ ∧ x₀≤b.1 ∧ b.1≤x₁
/-- A vertical piece at abscissa `x` between `y₀` and `y₁`. -/
def VS (x y₀ y₁ : ℚ) (a b : Vertex) : Prop := a.1=x ∧ b.1=x ∧ y₀≤a.2 ∧ a.2≤y₁ ∧ y₀≤b.2 ∧ b.2≤y₁

def eps : ℚ := 1/100000000

/-- The pieces of a divider of the slot at `x`. -/
def DivP (f x : ℚ) (a b : Vertex) : Prop :=
  VS (x-3) f (f+1/4) a b ∨ HS (f+1/4) (x-3) (x-2) a b ∨ VS (x-2) (f+eps) (f+1/4) a b ∨
    HS (f+eps) (x-2-1/10) (x-2) a b ∨ VS (x-2-1/10) f (f+eps) a b

/-- The pieces of a foot and a cap of door `j`. -/
def DoorP (f : ℚ) (j : Nat) (a b : Vertex) : Prop :=
  VS (door j+100-1/1000) (2*f) f a b ∨ VS (door j+100+1/1000) (2*f) f a b ∨
    VS (door j-30) (-6) 1 a b ∨ VS (door j+110) (-6) (1-1/10000) a b ∨
    HS (1-1/10000) (door j+110) (door j+110+1/10) a b ∨ VS (door j+110+1/10) (1-1/10000) 1 a b

/-- The western step of the last door `k` and the eastern side. -/
def EndP (f : ℚ) (k : Nat) (ss : List ℚ) (a b : Vertex) : Prop :=
  VS (door k-30) (f+eps) 1 a b ∨ HS (f+eps) (door k-30-1/10) (door k-30) a b ∨
    VS (door k-30-1/10) f (f+eps) a b ∨ VS (ss.getLastD 0+10) f (-6) a b

def Sec3 (f : ℚ) (k : Nat) (ss : List ℚ) (a b : Vertex) : Prop :=
  (a.2=f ∧ b.2=f) ∨ (a.2=-6 ∧ b.2=-6) ∨ (∃ j<k+1, HS 1 (door j-30) (door j+110+1/10) a b) ∨
    (∃ x∈ss, HS (-6-f) x (x+3/2) a b) ∨ (∃ j<k+1, HS (2*f) (door j+100-1/1000) (door j+100+1/1000) a b) ∨
    (∃ x∈ss, VS x (-6) (-6-f) a b ∨ VS (x+3/2) (-6) (-6-f) a b) ∨ (∃ x∈ss.tail, DivP f x a b) ∨
    (∃ j<k+1, DoorP f j a b) ∨ EndP f k ss a b

section Chains
variable {R : Vertex → Vertex → Prop}

private theorem append_or {α : Type} {a b : Option α} {p : α} (h : p∈a.or b) : p∈a ∨ p∈b := by
  cases a <;> simp_all

/-- A nonempty chain whose ends satisfy `E`. -/
structure Piece (R : Vertex → Vertex → Prop) (E : Vertex → Prop) (l : List Vertex) : Prop where
  chain : l.IsChain R
  first : ∀ p∈l.head?, E p
  last : ∀ p∈l.getLast?, E p
  ne : l≠[]

theorem flatten {E : Vertex → Prop} (EE : ∀ a b, E a → E b → R a b) {α : Type}
    (l : List α) (g : α → List Vertex) (h : ∀ a∈l,Piece R E (g a)) :
    (l.flatMap g).IsChain R ∧ (∀ p∈(l.flatMap g).head?, E p) ∧ (∀ p∈(l.flatMap g).getLast?, E p) := by
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

theorem app {E : Vertex → Prop} (EE : ∀ a b, E a → E b → R a b) {l r : List Vertex}
    (hl : l.IsChain R ∧ ∀ p∈l.getLast?, E p) (hr : r.IsChain R ∧ (∀ p∈r.head?, E p) ∧ ∀ p∈r.getLast?, E p) :
    (l++r).IsChain R ∧ ∀ p∈(l++r).getLast?, E p := by
  refine ⟨hl.1.append hr.1 (fun u hu v hv => EE _ _ (hl.2 _ hu) (hr.2.1 _ hv)),?_⟩
  intro p hp; rw [List.getLast?_append] at hp
  cases h : r.getLast? with
  | none => rw [h] at hp; exact hl.2 p (by simpa using hp)
  | some q => rw [h] at hp; simp at hp; subst hp; exact hr.2.2 _ h

end Chains

theorem contour3 (n k : Nat) (ss : List ℚ) (hn : 65≤n) (placed : Placed ss) :
    let l := hubCycle n (k+1) ss
    (l++l.take 1).IsChain (Sec3 (1-D n) k ss) := by
  let f := 1-D n
  let left := door k-30
  let right := ss.getLastD 0+10
  let start : Vertex := (left-1/10,f)
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have hf : f < -7 := by dsimp [f,D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) big]
  have he : (0:ℚ)<eps := by norm_num [eps]
  have he4 : eps<1/4 := by norm_num [eps]
  let Fl : Vertex → Prop := fun p => p.2=f
  let Ce : Vertex → Prop := fun p => p.2=-6
  have FF : ∀ a b, Fl a → Fl b → Sec3 f k ss a b := fun a b ha hb => Or.inl ⟨ha,hb⟩
  have CC : ∀ a b, Ce a → Ce b → Sec3 f k ss a b := fun a b ha hb => Or.inr (Or.inl ⟨ha,hb⟩)
  have DP (j : Nat) (hj : j<k+1) {a b : Vertex} (h : DoorP f j a b) : Sec3 f k ss a b :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j,hj,h⟩)))))))
  have EP {a b : Vertex} (h : EndP f k ss a b) : Sec3 f k ss a b :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  have SP (x : ℚ) (hx : x∈ss) {a b : Vertex} (h : VS x (-6) (-6-f) a b ∨ VS (x+3/2) (-6) (-6-f) a b) :
      Sec3 f k ss a b :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x,hx,h⟩)))))
  have VP (x : ℚ) (hx : x∈ss.tail) {a b : Vertex} (h : DivP f x a b) : Sec3 f k ss a b :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x,hx,h⟩))))))
  have feet (j : Nat) (hj : j<k+1) : Piece (Sec3 f k ss) Fl (foot f j) := by
    refine ⟨?_,by simp [foot,Fl],by simp [foot,Fl],by simp [foot]⟩
    simp only [foot,List.isChain_cons_cons,List.isChain_singleton,and_true]
    refine ⟨DP j hj (Or.inl ⟨rfl,rfl,by linarith,le_rfl,le_rfl,by linarith⟩),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j,hj,rfl,rfl,le_rfl,by linarith,by linarith,le_rfl⟩)))),
      DP j hj (Or.inr (Or.inl ⟨rfl,rfl,le_rfl,by linarith,by linarith,le_rfl⟩))⟩
  have divs (x : ℚ) (hx : x∈ss.tail) : Piece (Sec3 f k ss) Fl (divider f x) := by
    refine ⟨?_,by simp [divider,Fl],by simp [divider,Fl],by simp [divider]⟩
    simp only [divider,List.isChain_cons_cons,List.isChain_singleton,and_true]
    refine ⟨VP x hx (Or.inl ⟨by ring,by ring,le_rfl,by linarith,by linarith,le_rfl⟩),
      VP x hx (Or.inr (Or.inl ⟨rfl,rfl,by linarith,by linarith,by linarith,by linarith⟩)),
      VP x hx (Or.inr (Or.inr (Or.inl ⟨by ring,by ring,by linarith,le_rfl,le_rfl,by linarith⟩))),
      VP x hx (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,by linarith,by linarith,by linarith,by linarith⟩)))),
      VP x hx (Or.inr (Or.inr (Or.inr (Or.inr ⟨by ring,by ring,by linarith,le_rfl,le_rfl,by linarith⟩))))⟩
  have shafts (x : ℚ) (hx : x∈ss) : Piece (Sec3 f k ss) Ce (shaft f x) := by
    refine ⟨?_,by simp [shaft,Ce],by simp [shaft,Ce],by simp [shaft]⟩
    simp only [shaft,List.isChain_cons_cons,List.isChain_singleton,and_true]
    refine ⟨SP x hx (Or.inr ⟨rfl,rfl,le_rfl,by linarith,by linarith,le_rfl⟩),
      Or.inr (Or.inr (Or.inr (Or.inl ⟨x,hx,rfl,rfl,by linarith,le_rfl,le_rfl,by linarith⟩))),
      SP x hx (Or.inl ⟨rfl,rfl,by linarith,le_rfl,le_rfl,by linarith⟩)⟩
  have capEdges (j : Nat) (hj : j<k+1) :
      [(door j+110,-6),(door j+110,1-1/10000),(door j+110+1/10,1-1/10000),(door j+110+1/10,1),(door j-30,(1:ℚ))].IsChain
        (Sec3 f k ss) := by
    simp only [List.isChain_cons_cons,List.isChain_singleton,and_true]
    refine ⟨DP j hj (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,le_rfl,by norm_num,by norm_num,le_rfl⟩)))),
      DP j hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,le_rfl,by linarith,by linarith,le_rfl⟩))))),
      DP j hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,le_rfl,by norm_num,by norm_num,le_rfl⟩))))),
      Or.inr (Or.inr (Or.inl ⟨j,hj,rfl,rfl,by linarith,le_rfl,le_rfl,by linarith⟩))⟩
  have caps (j : Nat) (hj : j+1<k+1) : Piece (Sec3 f k ss) Ce (capPath (k+1) j) := by
    refine ⟨?_,by simp [capPath,hj,Ce],by simp [capPath,hj,Ce],by simp [capPath]⟩
    have e : capPath (k+1) j=[(door j+110,-6),(door j+110,1-1/10000),(door j+110+1/10,1-1/10000),(door j+110+1/10,1),
        (door j-30,(1:ℚ))]++[(door j-30,-6)] := by simp [capPath,hj]
    rw [e]
    exact (capEdges j (by omega)).append (by simp) (fun u hu v hv => by
      simp at hu hv; subst hu; subst hv
      exact DP j (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,by norm_num,le_rfl,le_rfl,by norm_num⟩))))
  -- the floor run: start, feet, dividers, east side bottom
  have fs := flatten FF (List.range (k+1)).reverse (foot f) (fun j hj => feet j (List.mem_range.mp (List.mem_reverse.mp hj)))
  have ds := flatten FF ss.tail (divider f) (fun x hx => divs x hx)
  have rs := flatten CC ss.reverse (shaft f) (fun x hx => shafts x (List.mem_reverse.mp hx))
  have cs := flatten CC (List.range k) (capPath (k+1)) (fun j hj => caps j (Nat.succ_lt_succ (List.mem_range.mp hj)))
  have lastC : (capPath (k+1) k++[(door k-30,f+eps)]).IsChain (Sec3 f k ss) := by
    have e : capPath (k+1) k=[(door k+110,-6),(door k+110,1-1/10000),(door k+110+1/10,1-1/10000),(door k+110+1/10,1),
        (door k-30,(1:ℚ))] := by simp [capPath]
    rw [e]
    exact (capEdges k (by omega)).append (by simp) (fun u hu v hv => by
      simp at hu hv; subst hu; subst hv
      exact EP (Or.inl ⟨rfl,rfl,by linarith,le_rfl,le_rfl,by norm_num [eps]; linarith⟩))
  -- assemble
  have s0 : ([start]:List Vertex).IsChain (Sec3 f k ss) ∧ ∀ p∈([start]:List Vertex).getLast?, Fl p := by
    simp [start,Fl]
  have s1 := app FF s0 fs
  have s2 := app FF s1 ds
  have s3 := app FF s2 (r:=[(right,f)]) (by simp [Fl])
  have r0 : ([(right,-6)]:List Vertex).IsChain (Sec3 f k ss) ∧ ∀ p∈([(right,-6)]:List Vertex).getLast?, Ce p := by
    simp [Ce]
  have r1 := app CC r0 rs
  have r2 := app CC r1 cs
  have R3 := r2.1.append lastC (fun u hu v hv => CC _ _ (r2.2 _ hu) (by simp [capPath] at hv; subst hv; simp [Ce]))
  have FR := s3.1.append R3 (fun u hu v hv => by
    simp [List.getLast?_append,List.getLast?_cons] at hu hv; subst hu; subst hv
    exact EP (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,le_rfl,by linarith,by linarith,le_rfl⟩))))
  have fin : ([(left-1/10,f+eps),start]:List Vertex).IsChain (Sec3 f k ss) := by
    simp only [List.isChain_cons_cons,List.isChain_singleton,and_true]
    exact EP (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,by linarith,le_rfl,le_rfl,by linarith⟩)))
  have all := FR.append fin (fun u hu v hv => by
    simp [List.getLast?_append,List.getLast?_cons] at hu hv; subst hu; subst hv
    exact EP (Or.inr (Or.inl ⟨rfl,rfl,by simp only [left]; linarith,by simp only [left]; linarith,
      by simp only [left]; linarith,by simp only [left]; linarith⟩)))
  have split : (List.range (k+1)).flatMap (capPath (k+1))=(List.range k).flatMap (capPath (k+1))++capPath (k+1) k := by
    rw [List.range_succ]; simp
  have beg : (hubCycle n (k+1) ss).take 1=[start] := rfl
  change ((hubCycle n (k+1) ss)++(hubCycle n (k+1) ss).take 1).IsChain _
  rw [beg]
  simp only [hubCycle,split,Nat.add_sub_cancel]
  simpa only [start,left,right,f,eps,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using all

/-! ## Boundary points on the pieces -/

def rHS (y x₀ x₁ : ℚ) (q : Point) : Prop := q.2=(y:ℝ) ∧ (x₀:ℝ)≤q.1 ∧ q.1≤(x₁:ℝ)
def rVS (x y₀ y₁ : ℚ) (q : Point) : Prop := q.1=(x:ℝ) ∧ (y₀:ℝ)≤q.2 ∧ q.2≤(y₁:ℝ)

def rDivP (f x : ℚ) (q : Point) : Prop :=
  rVS (x-3) f (f+1/4) q ∨ rHS (f+1/4) (x-3) (x-2) q ∨ rVS (x-2) (f+eps) (f+1/4) q ∨
    rHS (f+eps) (x-2-1/10) (x-2) q ∨ rVS (x-2-1/10) f (f+eps) q

def rDoorP (f : ℚ) (j : Nat) (q : Point) : Prop :=
  rVS (door j+100-1/1000) (2*f) f q ∨ rVS (door j+100+1/1000) (2*f) f q ∨
    rVS (door j-30) (-6) 1 q ∨ rVS (door j+110) (-6) (1-1/10000) q ∨
    rHS (1-1/10000) (door j+110) (door j+110+1/10) q ∨ rVS (door j+110+1/10) (1-1/10000) 1 q

def rEndP (f : ℚ) (k : Nat) (ss : List ℚ) (q : Point) : Prop :=
  rVS (door k-30) (f+eps) 1 q ∨ rHS (f+eps) (door k-30-1/10) (door k-30) q ∨
    rVS (door k-30-1/10) f (f+eps) q ∨ rVS (ss.getLastD 0+10) f (-6) q

def rSec3 (f : ℚ) (k : Nat) (ss : List ℚ) (q : Point) : Prop :=
  q.2=(f:ℝ) ∨ q.2=-6 ∨ (∃ j<k+1, rHS 1 (door j-30) (door j+110+1/10) q) ∨
    (∃ x∈ss, rHS (-6-f) x (x+3/2) q) ∨ (∃ j<k+1, rHS (2*f) (door j+100-1/1000) (door j+100+1/1000) q) ∨
    (∃ x∈ss, rVS x (-6) (-6-f) q ∨ rVS (x+3/2) (-6) (-6-f) q) ∨ (∃ x∈ss.tail, rDivP f x q) ∨
    (∃ j<k+1, rDoorP f j q) ∨ rEndP f k ss q

section Lift
variable {a b : Vertex} {q : Point} (hq : q∈ArtGallery.segment (ratPoint a) (ratPoint b))
include hq

theorem lift_y {y : ℚ} (ha : a.2=y) (hb : b.2=y) : q.2=(y:ℝ) := by
  obtain ⟨t,_,_,rfl⟩ := mem_segment_iff_lerp.mp hq
  simp only [lerp_snd,ratPoint,ha,hb]; ring

theorem lift_HS {y x₀ x₁ : ℚ} (h : HS y x₀ x₁ a b) : rHS y x₀ x₁ q := by
  obtain ⟨ha,hb,a0,a1,b0,b1⟩ := h
  refine ⟨lift_y hq ha hb,?_⟩
  obtain ⟨t,t0,t1,rfl⟩ := mem_segment_iff_lerp.mp hq
  have x := HighStep.interpolated (a.1:ℝ) (b.1:ℝ) t0 t1
  simp only [lerp_fst,ratPoint]
  exact ⟨(le_min (by exact_mod_cast a0) (by exact_mod_cast b0)).trans x.1,
    x.2.trans (max_le (by exact_mod_cast a1) (by exact_mod_cast b1))⟩

theorem lift_VS {x y₀ y₁ : ℚ} (h : VS x y₀ y₁ a b) : rVS x y₀ y₁ q := by
  obtain ⟨ha,hb,a0,a1,b0,b1⟩ := h
  obtain ⟨t,t0,t1,rfl⟩ := mem_segment_iff_lerp.mp hq
  have y := HighStep.interpolated (a.2:ℝ) (b.2:ℝ) t0 t1
  unfold rVS
  simp only [lerp_fst,lerp_snd,ratPoint,ha,hb]
  refine ⟨by ring,(le_min (by exact_mod_cast a0) (by exact_mod_cast b0)).trans y.1,
    y.2.trans (max_le (by exact_mod_cast a1) (by exact_mod_cast b1))⟩

theorem lift {f : ℚ} {k : Nat} {ss : List ℚ} (h : Sec3 f k ss a b) : rSec3 f k ss q := by
  rcases h with ⟨ha,hb⟩|⟨ha,hb⟩|ha|⟨x,hx,ha⟩|⟨j,hj,ha⟩|⟨x,hx,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|h
  · exact Or.inl (lift_y hq ha hb)
  · exact Or.inr (Or.inl (by simpa using lift_y hq ha hb))
  · obtain ⟨j,hj,h⟩ := ha
    exact Or.inr (Or.inr (Or.inl ⟨j,hj,lift_HS hq h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x,hx,lift_HS hq ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j,hj,lift_HS hq ha⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x,hx,?_⟩)))))
    rcases h with h|h
    · exact Or.inl (lift_VS hq h)
    · exact Or.inr (lift_VS hq h)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x,hx,?_⟩))))))
    rcases h with h|h|h|h|h
    · exact Or.inl (lift_VS hq h)
    · exact Or.inr (Or.inl (lift_HS hq h))
    · exact Or.inr (Or.inr (Or.inl (lift_VS hq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (lift_HS hq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (lift_VS hq h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j,hj,?_⟩)))))))
    rcases h with h|h|h|h|h|h
    · exact Or.inl (lift_VS hq h)
    · exact Or.inr (Or.inl (lift_VS hq h))
    · exact Or.inr (Or.inr (Or.inl (lift_VS hq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (lift_VS hq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lift_HS hq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (lift_VS hq h)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))))
    rcases h with h|h|h|h
    · exact Or.inl (lift_VS hq h)
    · exact Or.inr (Or.inl (lift_HS hq h))
    · exact Or.inr (Or.inr (Or.inl (lift_VS hq h)))
    · exact Or.inr (Or.inr (Or.inr (lift_VS hq h)))

end Lift

theorem adjacentR {R : Vertex → Vertex → Prop} {l : List Vertex}
    (c : (l++l.take 1).IsChain R) (i : Nat) (h : i<l.length) :
    R (l.getD i (0,0)) (l.getD ((i+1)%l.length) (0,0)) := by
  have le : 0<l.length := by omega
  have sz : (l.take 1).length=1 := by simp; omega
  have step := List.isChain_iff_getElem.mp c i (by simp only [List.length_append,sz]; omega)
  rw [List.getElem_append_left h] at step
  rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (Nat.mod_lt _ le)]
  by_cases next : i+1<l.length
  · simpa [List.getElem_append_left next,Nat.mod_eq_of_lt next] using step
  · have endEq : i+1=l.length := by omega
    simpa [endEq,List.getElem_append_right] using step

/-- Every boundary point of the hub lies on one of the explicit pieces. -/
theorem boundary_cases {n k : Nat} (hn : 65≤n) {ss : List ℚ} (placed : Placed ss) {q : Point}
    (hq : q∈(Polygon.mk ((hubCycle n (k+1) ss).map ratPoint)).boundary) : rSec3 (1-D n) k ss q := by
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
  exact lift edge (adjacentR (contour3 n k ss hn placed) i hi)

end ArtGallery.Orthogonal.BoundaryPoint.HubEdges
end
