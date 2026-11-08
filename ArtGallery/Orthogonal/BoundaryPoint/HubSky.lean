module

public import ArtGallery.Orthogonal.BoundaryPoint.HubDoors
public import ArtGallery.Orthogonal.BoundaryPoint.HighStep

/-! # Upper cross-sections of the actual hub
An upward ray from a filled point above the low roof meets either a base
shaft or a high step. All the horizontal pieces between features are below
this threshold, irrespective of their length. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubSky
open RectContour BoundaryChart BankCoordinates Geometry

def Low (p : Vertex) := p.2≤ -6
def East (p : Vertex) := 1970≤p.1
def Cap (j : Nat) (p : Vertex) := door j-30≤p.1 ∧ p.1≤door j+1101/10 ∧ p.2≤1

def Section (count : Nat) (a b : Vertex) : Prop :=
  (Low a ∧ Low b) ∨ (East a ∧ East b) ∨ ∃ j<count, Cap j a ∧ Cap j b

structure Piece (count : Nat) (l : List Vertex) : Prop where
  chain : l.IsChain (Section count)
  first : ∀ p∈l.head?, Low p
  last : ∀ p∈l.getLast?, Low p

private theorem append_or {α : Type} {a b : Option α} {p : α} (h : p∈a.or b) : p∈a ∨ p∈b := by
  cases a <;> simp_all

theorem Piece.append {n : Nat} {l r : List Vertex} (a : Piece n l) (b : Piece n r) : Piece n (l++r) := by
  refine ⟨a.chain.append b.chain (fun u hu v hv => Or.inl ⟨a.last _ hu,b.first _ hv⟩),?_,?_⟩
  · intro p hp; rw [List.head?_append] at hp
    exact (append_or hp).elim (a.first p) (b.first p)
  · intro p hp; rw [List.getLast?_append] at hp
    exact (append_or hp).elim (b.last p) (a.last p)

private theorem one_type {n : Nat} {l : List Vertex} {P : Vertex → Prop}
    (cover : ∀ p∈l,P p) (edge : ∀ a b, P a → P b → Section n a b)
    (start : ∀ p∈l.head?,Low p) (finish : ∀ p∈l.getLast?,Low p) : Piece n l := by
  refine ⟨List.isChain_iff_getElem.mpr ?_,start,finish⟩
  intro i hi
  exact edge _ _ (cover _ (List.getElem_mem (by omega))) (cover _ (List.getElem_mem hi))

private theorem low {n : Nat} {l : List Vertex} (L : ∀ p∈l,Low p) : Piece n l :=
  one_type L (fun _ _ a b => Or.inl ⟨a,b⟩)
    (fun _ h => L _ (List.mem_of_mem_head? h)) (fun _ h => L _ (List.mem_of_mem_getLast? h))

private theorem flatten {α : Type} {n} (l : List α) (f : α → List Vertex) (h : ∀ a∈l,Piece n (f a)) :
    Piece n (l.flatMap f) := by
  induction l with
  | nil => exact low (by simp)
  | cons a l ih => exact (h _ List.mem_cons_self).append (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)))

private theorem shaft_piece (n : Nat) (f x : ℚ) (hx : 1970≤x) : Piece n (shaft f x) := by
  refine one_type (P:=East) ?_ (fun _ _ a b => Or.inr (Or.inl ⟨a,b⟩)) ?_ ?_
  · intro z hz
    simp only [shaft,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> dsimp [East] <;> linarith
  all_goals simp [shaft,Low]

private theorem cap_piece (n j : Nat) (hj : j+1<n) : Piece n (capPath n j) := by
  refine one_type (P:=Cap j) ?_ (fun _ _ a b => Or.inr (Or.inr ⟨j,by omega,a,b⟩)) ?_ ?_
  · intro z hz
    simp only [capPath,hj,ite_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with (rfl|rfl|rfl|rfl|rfl)|rfl <;> dsimp [Cap] <;> constructor <;> first | constructor <;> linarith | linarith
  all_goals simp [capPath,hj,Low]

private theorem last_cap (k : Nat) (f : ℚ) (hf : f< -7) :
    Piece (k+1) (capPath (k+1) k++[(door k-30,f+1/100000000)]) := by
  refine one_type (P:=Cap k) ?_ (fun _ _ a b => Or.inr (Or.inr ⟨k,by omega,a,b⟩)) ?_ ?_
  · intro z hz
    simp [capPath] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp [Cap] <;> constructor <;> first | constructor <;> linarith | linarith
  · simp [capPath,Low]
  · simp [capPath,Low]; linarith

theorem contour (n k : Nat) (slots : List ℚ) (hn : 65≤n) (far : ∀ x∈slots,1970≤x) :
    let l := hubCycle n (k+1) slots
    (l++l.take 1).IsChain (Section (k+1)) := by
  let f := 1-D n
  let left := door k-30
  let right := slots.getLastD 0+10
  let start : Vertex := (left-1/10,f)
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have hf : f < -7 := by dsimp [f,D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) big]
  have feet (j : Nat) : Piece (k+1) (foot f j) := by
    apply low; intro z hz
    simp only [foot,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> dsimp [Low] <;> linarith
  have divs (x : ℚ) : Piece (k+1) (divider f x) := by
    apply low; intro z hz
    simp only [divider,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp [Low] <;> linarith
  have side : Piece (k+1) [(right,f),(right,-6)] := by
    apply low; intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> dsimp [Low] <;> linarith
  have a : Piece (k+1) [start] := low (by simpa [start,Low] using (show f≤ -6 by linarith))
  have finish : Piece (k+1) [(left-1/10,f+1/100000000),start] := by
    apply low; intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> dsimp [Low,start] <;> linarith
  have floor := ((a.append (flatten (List.range (k+1)).reverse (foot f) (fun j _ => feet j))).append
    (flatten slots.tail (divider f) (fun x _ => divs x))).append side
  have roof := (flatten slots.reverse (shaft f) (fun x hx => shaft_piece (k+1) f x (far x (List.mem_reverse.mp hx)))).append
    (flatten (List.range k) (capPath (k+1)) (fun j hj => cap_piece _ j (Nat.succ_lt_succ (List.mem_range.mp hj))))
  have full := (((floor.append roof).append (last_cap k f hf)).append finish).chain
  have split : (List.range (k+1)).flatMap (capPath (k+1))=(List.range k).flatMap (capPath (k+1))++capPath (k+1) k := by
    rw [List.range_succ]; simp
  have beg : (hubCycle n (k+1) slots).take 1=[start] := rfl
  change ((hubCycle n (k+1) slots)++(hubCycle n (k+1) slots).take 1).IsChain _
  rw [beg]
  simp only [hubCycle,split,Nat.add_sub_cancel]
  simpa only [start,left,right,f,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using full

private theorem adjacent {n : Nat} {l : List Vertex} (c : (l++l.take 1).IsChain (Section n))
    (i : Nat) (h : i<l.length) :
    Section n (l.getD i (0,0)) (l.getD ((i+1)%l.length) (0,0)) := by
  have le : 0<l.length := by omega
  have sz : (l.take 1).length=1 := by simp; omega
  have step := List.isChain_iff_getElem.mp c i (by simp only [List.length_append,sz]; omega)
  rw [List.getElem_append_left h] at step
  rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (Nat.mod_lt _ le)]
  by_cases next : i+1<l.length
  · simpa [List.getElem_append_left next,Nat.mod_eq_of_lt next] using step
  · have endEq : i+1=l.length := by omega
    simpa [endEq,List.getElem_append_right] using step

def AtCap (j : Nat) (q : Point) : Prop :=
  (door j:ℝ)-30≤q.1 ∧ q.1≤(door j:ℝ)+1101/10 ∧ q.2≤1

private theorem on_side {n : Nat} {a b : Vertex} (c : Section n a b) {q : Point}
    (mem : q∈ArtGallery.segment (ratPoint a) (ratPoint b)) :
    q.2≤ -6 ∨ 1970≤q.1 ∨ ∃ j<n,AtCap j q := by
  obtain ⟨t,ht,hu,rfl⟩ := mem_segment_iff_lerp.mp mem
  have x := HighStep.interpolated (a.1:ℝ) (b.1:ℝ) ht hu
  have y := HighStep.interpolated (a.2:ℝ) (b.2:ℝ) ht hu
  simp only [lerp_fst,lerp_snd,ratPoint,AtCap]
  rcases c with ⟨A,B⟩|⟨A,B⟩|⟨j,hj,A,B⟩
  · left; exact y.2.trans (max_le (by unfold Low at A; exact_mod_cast A) (by unfold Low at B; exact_mod_cast B))
  · right; left; exact (le_min (by unfold East at A; exact_mod_cast A) (by unfold East at B; exact_mod_cast B)).trans x.1
  · have conv (p : Vertex) (H : Cap j p) : (door j:ℝ)-30≤p.1 ∧ (p.1:ℝ)≤(door j:ℝ)+1101/10 ∧ (p.2:ℝ)≤1 := by
      obtain ⟨L,R,T⟩ := H
      exact ⟨by simpa only [Rat.cast_sub,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr L,
        by simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr R,
        by exact_mod_cast T⟩
    have A' := conv a A
    have B' := conv b B
    exact Or.inr (Or.inr ⟨j,hj,(le_min A'.1 B'.1).trans x.1,x.2.trans (max_le A'.2.1 B'.2.1),
      y.2.trans (max_le A'.2.2 B'.2.2)⟩)

theorem upper {rows n : Nat} (hr : 0<rows) (hn : 65≤n) {ss : List ℚ} (far : ∀ x∈ss,1970≤x)
    {q : Point} (hq : q∈(Polygon.mk ((hubCycle n rows ss).map ratPoint)).filled) (high : -5≤q.2) (west : q.1<1970) :
    ∃ j<rows,AtCap j q := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let l := hubCycle n (k+1) ss
  let P : Polygon := ⟨l.map ratPoint⟩
  have wall (p : Point) (hp : p∈P.boundary) : p.2≤ -6 ∨ 1970≤p.1 ∨ ∃ j<k+1,AtCap j p := by
    obtain ⟨i,hi,edge⟩ := hp
    have size : P.n=l.length := by simp [P,Polygon.n]
    rw [size] at hi
    change p∈ArtGallery.segment (P.vtx i) (P.vtx ((i+1)%P.n)) at edge
    rw [size] at edge
    have vertex (j : Nat) (hj : j<l.length) : P.vtx j=ratPoint (l.getD j (0,0)) := by
      change (l.map ratPoint).getD j (0,0)=_
      rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map,List.getD_eq_getElem _ _ hj]
    rw [vertex _ hi,vertex _ (Nat.mod_lt _ (by omega))] at edge
    exact on_side (adjacent (contour n k ss hn far) i hi) edge
  have meets : ∃ t : ℝ,0≤t ∧ q+t • ((0,1):Point)∈P.boundary := by
    by_contra! no
    have outside : q∉P.boundary := by simpa using no 0 (le_refl _)
    exact Jordan.not_isBoundedSet_connectedComponentIn_of_ray P (d:=(0,1)) (by simp)
      (by rintro _ ⟨t,ht,rfl⟩; exact no t ht) ((Jordan.mem_filled_iff_bounded P outside).mp hq)
  obtain ⟨t,ht,hm⟩ := meets
  rcases wall _ hm with low|east|⟨j,hj,cover⟩
  · simp at low; linarith
  · simp at east; linarith
  · refine ⟨j,hj,?_⟩
    simp only [AtCap,Geometry.add_fst,Geometry.smul_fst,Geometry.add_snd,Geometry.smul_snd,
      mul_zero,add_zero,mul_one] at cover
    exact ⟨cover.1,cover.2.1,by linarith [cover.2.2]⟩

end ArtGallery.Orthogonal.BoundaryPoint.HubSky
end
