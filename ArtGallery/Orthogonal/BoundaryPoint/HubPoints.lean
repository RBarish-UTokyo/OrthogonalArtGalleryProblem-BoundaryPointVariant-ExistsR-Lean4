module

public import ArtGallery.Orthogonal.BoundaryPoint.HubEdges

/-! # Points on the boundary of the hub

Consecutive vertices of the hub cycle bound an edge. The floor under every base slot, the top of
every cap, the top of every shaft and the bottom of every foot lie on edges. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubPoints
open RectContour BoundaryChart BankCoordinates Geometry HubComb HubFloor

/-- Two consecutive vertices of a cycle bound an edge. -/
theorem infix_boundary {l : List Vertex} {a b : Vertex} (h : [a,b]<:+:l) :
    ArtGallery.segment (ratPoint a) (ratPoint b)⊆(Polygon.mk (l.map ratPoint)).boundary := by
  obtain ⟨s,t,rfl⟩ := h
  intro q hq
  refine ⟨s.length,?_,?_⟩
  · simp [Polygon.n]
  · have n_eq : (Polygon.mk ((s++[a,b]++t).map ratPoint)).n=s.length+2+t.length := by
      simp [Polygon.n]; omega
    simp only [Polygon.edge,Polygon.vtx,n_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    have e1 : ((s++[a,b]++t).map ratPoint).getD s.length (0,0)=ratPoint a := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]
    have e2 : ((s++[a,b]++t).map ratPoint).getD (s.length+1) (0,0)=ratPoint b := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]
    rw [e1,e2]; exact hq

theorem infix_mid {α : Type} {m l : List α} (h : m<:+:l) (A B : List α) : m<:+:A++l++B :=
  h.trans (List.infix_append _ _ _)

theorem infix_flatMap {α : Type} {L : List α} {g : α → List Vertex} {x : α} (hx : x∈L) {m : List Vertex}
    (h : m<:+:g x) : m<:+:L.flatMap g := by
  obtain ⟨s,t,rfl⟩ := List.append_of_mem hx
  have e : (s++x::t).flatMap g=s.flatMap g++g x++t.flatMap g := by simp
  rw [e]; exact infix_mid h _ _

/-- A point of a horizontal segment between two rational vertices. -/
theorem hseg {a b : Vertex} (hy : a.2=b.2) {x : ℝ} (h : ((min a.1 b.1:ℚ):ℝ)≤x ∧ x≤((max a.1 b.1:ℚ):ℝ)) :
    (x,(a.2:ℝ))∈ArtGallery.segment (ratPoint a) (ratPoint b) := by
  rcases eq_or_ne a.1 b.1 with e|e
  · refine Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,?_⟩
    have : x=(a.1:ℝ) := by rw [e,min_self,max_self] at h; exact le_antisymm h.2 h.1 |>.symm ▸ by rw [e]
    ext <;> simp [Geometry.lerp,ratPoint,this]
  · have d : ((b.1:ℝ)-a.1)≠0 := sub_ne_zero.mpr (by exact_mod_cast e.symm)
    refine Geometry.mem_segment_iff_lerp.mpr ⟨(x-a.1)/((b.1:ℝ)-a.1),?_,?_,?_⟩
    · rcases lt_or_gt_of_ne e with l|l
      · have l' : (a.1:ℝ)<b.1 := by exact_mod_cast l
        rw [min_eq_left l.le] at h; exact div_nonneg (by linarith [h.1]) (by linarith)
      · have l' : (b.1:ℝ)<a.1 := by exact_mod_cast l
        rw [max_eq_left l.le] at h; exact div_nonneg_of_nonpos (by linarith [h.2]) (by linarith)
    · rcases lt_or_gt_of_ne e with l|l
      · have l' : (a.1:ℝ)<b.1 := by exact_mod_cast l
        rw [max_eq_right l.le] at h; exact (div_le_one (by linarith)).mpr (by push_cast at h; linarith [h.2])
      · have l' : (b.1:ℝ)<a.1 := by exact_mod_cast l
        rw [min_eq_right l.le] at h
        rw [div_le_one_of_neg (by linarith)]; push_cast at h; linarith [h.1]
    · ext
      · simp [Geometry.lerp,ratPoint]; field_simp; ring
      · simp [Geometry.lerp,ratPoint,hy]

/-- A point of a vertical segment between two rational vertices. -/
theorem vseg {a b : Vertex} (hx : a.1=b.1) {y : ℝ} (h : ((min a.2 b.2:ℚ):ℝ)≤y ∧ y≤((max a.2 b.2:ℚ):ℝ)) :
    ((a.1:ℝ),y)∈ArtGallery.segment (ratPoint a) (ratPoint b) := by
  have sw := hseg (a:=(a.2,a.1)) (b:=(b.2,b.1)) hx h
  obtain ⟨t,t0,t1,e⟩ := Geometry.mem_segment_iff_lerp.mp sw
  refine Geometry.mem_segment_iff_lerp.mpr ⟨t,t0,t1,?_⟩
  simp only [Geometry.lerp,ratPoint,Prod.mk.injEq] at e ⊢
  exact ⟨e.2,e.1⟩

theorem hseg_dn {a b : Vertex} (hy : a.2=b.2) (hab : b.1≤a.1) {x : ℝ} (h : (b.1:ℝ)≤x ∧ x≤(a.1:ℝ)) :
    (x,(a.2:ℝ))∈ArtGallery.segment (ratPoint a) (ratPoint b) :=
  hseg hy (by rw [min_eq_right hab,max_eq_left hab]; exact h)
theorem hseg_up {a b : Vertex} (hy : a.2=b.2) (hab : a.1≤b.1) {x : ℝ} (h : (a.1:ℝ)≤x ∧ x≤(b.1:ℝ)) :
    (x,(a.2:ℝ))∈ArtGallery.segment (ratPoint a) (ratPoint b) :=
  hseg hy (by rw [min_eq_left hab,max_eq_right hab]; exact h)
theorem vseg_dn {a b : Vertex} (hx : a.1=b.1) (hab : b.2≤a.2) {y : ℝ} (h : (b.2:ℝ)≤y ∧ y≤(a.2:ℝ)) :
    ((a.1:ℝ),y)∈ArtGallery.segment (ratPoint a) (ratPoint b) :=
  vseg hx (by rw [min_eq_right hab,max_eq_left hab]; exact h)
theorem vseg_up {a b : Vertex} (hx : a.1=b.1) (hab : a.2≤b.2) {y : ℝ} (h : (a.2:ℝ)≤y ∧ y≤(b.2:ℝ)) :
    ((a.1:ℝ),y)∈ArtGallery.segment (ratPoint a) (ratPoint b) :=
  vseg hx (by rw [min_eq_left hab,max_eq_right hab]; exact h)

section
variable {n k : Nat} {ss : List ℚ}

theorem cycle_eq (n k : Nat) (ss : List ℚ) :
    hubCycle n (k+1) ss=[(door k-30-1/10,1-D n)]++(List.range (k+1)).reverse.flatMap (foot (1-D n))++
      ss.tail.flatMap (divider (1-D n))++[(ss.getLastD 0+10,1-D n),(ss.getLastD 0+10,-6)]++
      ss.reverse.flatMap (shaft (1-D n))++(List.range (k+1)).flatMap (capPath (k+1))++
      [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)] := by
  simp [hubCycle]

/-- A pair inside the shafts block is consecutive in the cycle. -/
theorem in_shafts {a b : Vertex} (h : [a,b]<:+:ss.reverse.flatMap (shaft (1-D n))) :
    [a,b]<:+:hubCycle n (k+1) ss := by
  rw [cycle_eq]
  have := infix_mid h ([(door k-30-1/10,1-D n)]++(List.range (k+1)).reverse.flatMap (foot (1-D n))++
      ss.tail.flatMap (divider (1-D n))++[(ss.getLastD 0+10,1-D n),(ss.getLastD 0+10,-6)])
    ((List.range (k+1)).flatMap (capPath (k+1))++
      [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)])
  simpa only [List.append_assoc] using this

theorem in_caps {a b : Vertex} (h : [a,b]<:+:(List.range (k+1)).flatMap (capPath (k+1))) :
    [a,b]<:+:hubCycle n (k+1) ss := by
  rw [cycle_eq]
  have := infix_mid h ([(door k-30-1/10,1-D n)]++(List.range (k+1)).reverse.flatMap (foot (1-D n))++
      ss.tail.flatMap (divider (1-D n))++[(ss.getLastD 0+10,1-D n),(ss.getLastD 0+10,-6)]++
      ss.reverse.flatMap (shaft (1-D n)))
    [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)]
  simpa only [List.append_assoc] using this

theorem in_divs {a b : Vertex} (h : [a,b]<:+:ss.tail.flatMap (divider (1-D n))) :
    [a,b]<:+:hubCycle n (k+1) ss := by
  rw [cycle_eq]
  have := infix_mid h ([(door k-30-1/10,1-D n)]++(List.range (k+1)).reverse.flatMap (foot (1-D n)))
    ([(ss.getLastD 0+10,1-D n),(ss.getLastD 0+10,-6)]++
      ss.reverse.flatMap (shaft (1-D n))++(List.range (k+1)).flatMap (capPath (k+1))++
      [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)])
  simpa only [List.append_assoc] using this

theorem in_end {a b : Vertex} (h : [a,b]<:+:(List.range (k+1)).flatMap (capPath (k+1))++
      [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)]) :
    [a,b]<:+:hubCycle n (k+1) ss := by
  rw [cycle_eq]
  have := infix_mid h ([(door k-30-1/10,1-D n)]++(List.range (k+1)).reverse.flatMap (foot (1-D n))++
      ss.tail.flatMap (divider (1-D n))++[(ss.getLastD 0+10,1-D n),(ss.getLastD 0+10,-6)]++
      ss.reverse.flatMap (shaft (1-D n))) []
  simpa only [List.append_assoc,List.append_nil] using this

theorem in_feet {a b : Vertex} (h : [a,b]<:+:(List.range (k+1)).reverse.flatMap (foot (1-D n))) :
    [a,b]<:+:hubCycle n (k+1) ss := by
  rw [cycle_eq]
  have := infix_mid h [(door k-30-1/10,1-D n)]
    (ss.tail.flatMap (divider (1-D n))++[(ss.getLastD 0+10,1-D n),(ss.getLastD 0+10,-6)]++
      ss.reverse.flatMap (shaft (1-D n))++(List.range (k+1)).flatMap (capPath (k+1))++
      [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)])
  simpa only [List.append_assoc] using this

abbrev HP (n k : Nat) (ss : List ℚ) : Polygon := Polygon.mk ((hubCycle n (k+1) ss).map ratPoint)

theorem f_le {n : Nat} (hn : 65≤n) : (1-D n:ℚ)< -7 := by
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  dsimp [D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) big]

/-- The top of a shaft. -/
theorem shaft_top (hn : 65≤n) {p : ℚ} (hp : p∈ss) {x : ℝ} (hx : (p:ℝ)≤x ∧ x≤((p+3/2:ℚ):ℝ)) :
    (x,((-6-(1-D n):ℚ):ℝ))∈(HP n k ss).boundary := by
  have hi : [((p+3/2:ℚ),(-6-(1-D n):ℚ)),(p,-6-(1-D n))]<:+:shaft (1-D n) p :=
    ⟨[(p+3/2,-6)],[(p,-6)],by simp [shaft]⟩
  have hb := infix_boundary (in_shafts (n:=n) (k:=k) (infix_flatMap (List.mem_reverse.mpr hp) hi))
  exact hb (hseg_dn (a:=((p+3/2:ℚ),(-6-(1-D n):ℚ))) (b:=(p,-6-(1-D n))) rfl (by dsimp only; linarith) hx)

/-- The western side of a shaft. -/
theorem shaft_west (hn : 65≤n) {p : ℚ} (hp : p∈ss) {y : ℝ} (hy : (-6:ℝ)≤y ∧ y≤((-6-(1-D n):ℚ):ℝ)) :
    ((p:ℝ),y)∈(HP n k ss).boundary := by
  have hf := f_le hn
  have hi : [(p,(-6-(1-D n):ℚ)),(p,-6)]<:+:shaft (1-D n) p := ⟨[(p+3/2,-6),(p+3/2,-6-(1-D n))],[],by simp [shaft]⟩
  have hb := infix_boundary (in_shafts (n:=n) (k:=k) (infix_flatMap (List.mem_reverse.mpr hp) hi))
  exact hb (vseg_dn (a:=(p,(-6-(1-D n):ℚ))) (b:=(p,-6)) rfl (by dsimp only; linarith)
    (by dsimp only; push_cast at hy ⊢; exact hy))

/-- The top of a cap. -/
theorem cap_top {j : Nat} (hj : j<k+1) {x : ℝ} (hx : ((door j-30:ℚ):ℝ)≤x ∧ x≤((door j+110+1/10:ℚ):ℝ)) :
    (x,(1:ℝ))∈(HP n k ss).boundary := by
  have hi : [(door j+110+1/10,(1:ℚ)),(door j-30,1)]<:+:capPath (k+1) j := by
    refine ⟨[(door j+110,-6),(door j+110,1-1/10000),(door j+110+1/10,1-1/10000)],
      if j+1<k+1 then [(door j-30,-6)] else [],?_⟩
    simp only [capPath]; split <;> simp
  have hb := infix_boundary (in_caps (n:=n) (ss:=ss) (infix_flatMap (List.mem_range.mpr hj) hi))
  have := hb (hseg_dn (a:=(door j+110+1/10,(1:ℚ))) (b:=(door j-30,1)) rfl (by dsimp only; linarith) hx)
  simpa using this

/-- The bottom of a foot. -/
theorem foot_bottom {j : Nat} (hj : j<k+1) {x : ℝ}
    (hx : ((door j+100-1/1000:ℚ):ℝ)≤x ∧ x≤((door j+100+1/1000:ℚ):ℝ)) :
    (x,((2*(1-D n):ℚ):ℝ))∈(HP n k ss).boundary := by
  have hi : [(door j+100-1/1000,2*(1-D n)),(door j+100+1/1000,(2*(1-D n):ℚ))]<:+:foot (1-D n) j :=
    ⟨[(door j+100-1/1000,1-D n)],[(door j+100+1/1000,1-D n)],by simp [foot]⟩
  have hb := infix_boundary (in_feet (n:=n) (k:=k) (ss:=ss) (infix_flatMap (List.mem_reverse.mpr (List.mem_range.mpr hj)) hi))
  exact hb (hseg_up (a:=(door j+100-1/1000,2*(1-D n))) (b:=(door j+100+1/1000,(2*(1-D n):ℚ))) rfl
    (by dsimp only; linarith) hx)

/-- A pair `[a,b]` with `a` the last vertex of the feet block and `b` the first vertex after it. -/
theorem feet_last (n k : Nat) : ∃ X, (List.range (k+1)).reverse.flatMap (foot (1-D n))=X++[(door 0+100+1/1000,1-D n)] := by
  rw [List.range_succ_eq_map,List.reverse_cons,List.flatMap_append]
  refine ⟨(List.map Nat.succ (List.range k)).reverse.flatMap (foot (1-D n))++
    [(door 0+100-1/1000,1-D n),(door 0+100-1/1000,2*(1-D n)),(door 0+100+1/1000,2*(1-D n))],?_⟩
  simp [foot]

theorem last_concat {α : Type} (A : List α) (b : α) : (A++[b]).getLast?=some b := by simp

theorem join_pair {α : Type} {M1 M2 : List α} {a b : α} (h1 : M1.getLast?=some a) (h2 : M2.head?=some b) :
    [a,b]<:+:M1++M2 := by
  obtain ⟨L1,rfl⟩ : ∃ L1, M1=L1++[a] := List.getLast?_eq_some_iff.mp h1
  obtain ⟨L2,rfl⟩ : ∃ L2, M2=b::L2 := by
    cases M2 with
    | nil => simp at h2
    | cons c l => simp at h2; exact ⟨l,by rw [h2]⟩
  exact ⟨L1,L2,by simp⟩

/-- The top of a floor divider. -/
theorem divider_top {p : ℚ} (hp : p∈ss.tail) {x : ℝ} (hx : ((p-2-1:ℚ):ℝ)≤x ∧ x≤((p-2:ℚ):ℝ)) :
    (x,((1-D n+1/4:ℚ):ℝ))∈(HP n k ss).boundary := by
  have hi : [(p-2-1,1-D n+1/4),(p-2,(1-D n+1/4:ℚ))]<:+:divider (1-D n) p :=
    ⟨[(p-2-1,1-D n)],[(p-2,1-D n+1/100000000),(p-2-1/10,1-D n+1/100000000),(p-2-1/10,1-D n)],by simp [divider]⟩
  have hb := infix_boundary (in_divs (n:=n) (k:=k) (infix_flatMap hp hi))
  exact hb (hseg_up (a:=(p-2-1,1-D n+1/4)) (b:=(p-2,(1-D n+1/4:ℚ))) rfl (by dsimp only; linarith) hx)

/-- The eastern side of a cap below its terrace. -/
theorem cap_right {j : Nat} (hj : j<k+1) {y : ℝ} (hy : (-6:ℝ)≤y ∧ y≤((1-1/10000:ℚ):ℝ)) :
    (((door j+110:ℚ):ℝ),y)∈(HP n k ss).boundary := by
  have hi : [(door j+110,(-6:ℚ)),(door j+110,1-1/10000)]<:+:capPath (k+1) j := by
    refine ⟨[],[(door j+110+1/10,1-1/10000),(door j+110+1/10,1),(door j-30,1)]++
      (if j+1<k+1 then [(door j-30,-6)] else []),?_⟩
    simp only [capPath]; split <;> simp
  have hb := infix_boundary (in_caps (n:=n) (ss:=ss) (infix_flatMap (List.mem_range.mpr hj) hi))
  exact hb (vseg_up (a:=(door j+110,(-6:ℚ))) (b:=(door j+110,1-1/10000)) rfl (by dsimp only; norm_num)
    (by dsimp only; push_cast at hy ⊢; exact hy))

/-- The western wall of the last door, from its cap top down to the closed step. -/
theorem west_wall (hn : 65≤n) {y : ℝ} (hy : ((1-D n+1/100000000:ℚ):ℝ)≤y ∧ y≤1) :
    (((door k-30:ℚ):ℝ),y)∈(HP n k ss).boundary := by
  have split : (List.range (k+1)).flatMap (capPath (k+1))=(List.range k).flatMap (capPath (k+1))++capPath (k+1) k := by
    rw [List.range_succ]; simp
  have hi : [(door k-30,(1:ℚ)),(door k-30,1-D n+1/100000000)]<:+:(List.range (k+1)).flatMap (capPath (k+1))++
      [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)] := by
    rw [split]
    refine ⟨(List.range k).flatMap (capPath (k+1))++
      [(door k+110,-6),(door k+110,1-1/10000),(door k+110+1/10,1-1/10000),(door k+110+1/10,1)],
      [(door k-30-1/10,1-D n+1/100000000)],?_⟩
    simp [capPath]
  have hb := infix_boundary (in_end (n:=n) (ss:=ss) hi)
  have hf := f_le hn
  refine hb (vseg_dn (a:=(door k-30,(1:ℚ))) (b:=(door k-30,1-D n+1/100000000)) rfl ?_ (by push_cast at hy ⊢; exact hy))
  dsimp only
  linarith

/-- The floor run under a base slot lies between two consecutive floor vertices. -/
theorem floor_run (placed : Placed ss) {p : ℚ} (hp : p∈ss) :
    ∃ a b : ℚ, [(a,1-D n),(b,1-D n)]<:+:hubCycle n (k+1) ss ∧ a≤p ∧ p+3/2≤b := by
  obtain ⟨s0,rest,hss⟩ : ∃ s0 rest, ss=s0::rest := by
    cases ss with
    | nil => exact absurd rfl placed.exists_slot
    | cons a l => exact ⟨a,l,rfl⟩
  have srt := placed.sorted
  rw [hss] at srt
  have far := placed.far
  have hr : ∀ x∈ss, x+10≤ss.getLastD 0+10 := fun x hx => by have := last_bound placed x hx; linarith
  have tailEq : ss.tail=rest := by rw [hss]; rfl
  obtain ⟨X,hX⟩ := feet_last n k
  let T : List Vertex := [(ss.getLastD 0+10,1-D n),(ss.getLastD 0+10,-6)]++
      ss.reverse.flatMap (shaft (1-D n))++(List.range (k+1)).flatMap (capPath (k+1))++
      [(door k-30,1-D n+1/100000000),(door k-30-1/10,1-D n+1/100000000)]
  have cyc : hubCycle n (k+1) ss=([(door k-30-1/10,1-D n)]++X++[(door 0+100+1/1000,1-D n)])++
      (rest.flatMap (divider (1-D n))++T) := by
    rw [cycle_eq,hX,tailEq]; simp [T]
  have hd0 : door 0+100+1/1000≤(1970:ℚ) := by unfold door; norm_num
  rcases List.mem_cons.mp (hss ▸ hp) with rfl|hpr
  · cases rest with
    | nil =>
      refine ⟨door 0+100+1/1000,ss.getLastD 0+10,?_,by linarith [far p hp],by linarith [hr p hp]⟩
      rw [cyc]; exact join_pair (last_concat _ _) (by simp [T])
    | cons q rest' =>
      refine ⟨door 0+100+1/1000,q-2-1,?_,by linarith [far p hp],?_⟩
      · rw [cyc]; exact join_pair (last_concat _ _) (by simp [divider])
      · have := (List.pairwise_cons.mp srt).1 q List.mem_cons_self; linarith
  · obtain ⟨A,B,hAB⟩ := List.append_of_mem hpr
    have srt' := (List.pairwise_cons.mp srt).2
    rw [hAB] at srt'
    have after : ∀ q∈B, p+10≤q := fun q hq => by
      have := List.pairwise_append.mp srt'
      exact (List.pairwise_cons.mp this.2.1).1 q hq
    have cyc2 : hubCycle n (k+1) ss=([(door k-30-1/10,1-D n)]++X++[(door 0+100+1/1000,1-D n)]++
        A.flatMap (divider (1-D n))++divider (1-D n) p)++(B.flatMap (divider (1-D n))++T) := by
      rw [cyc,hAB]; simp
    have lastDiv : ([(door k-30-1/10,1-D n)]++X++[(door 0+100+1/1000,1-D n)]++
        A.flatMap (divider (1-D n))++divider (1-D n) p).getLast?=some (p-2-1/10,1-D n) := by
      have e : [(door k-30-1/10,1-D n)]++X++[(door 0+100+1/1000,1-D n)]++A.flatMap (divider (1-D n))++
          divider (1-D n) p=([(door k-30-1/10,1-D n)]++X++[(door 0+100+1/1000,1-D n)]++A.flatMap (divider (1-D n))++
          [(p-2-1,1-D n),(p-2-1,1-D n+1/4),(p-2,1-D n+1/4),(p-2,1-D n+1/100000000),
            (p-2-1/10,1-D n+1/100000000)])++[(p-2-1/10,1-D n)] := by
        simp [divider]
      rw [e]; exact last_concat _ _
    cases B with
    | nil =>
      refine ⟨p-2-1/10,ss.getLastD 0+10,?_,by linarith,by linarith [hr p hp]⟩
      rw [cyc2]; exact join_pair lastDiv (by simp [T])
    | cons q B' =>
      refine ⟨p-2-1/10,q-2-1,?_,by linarith,by linarith [after q List.mem_cons_self]⟩
      rw [cyc2]; exact join_pair lastDiv (by simp [divider])

/-- The floor under every base slot is on the boundary. -/
theorem floor_slot (placed : Placed ss) {p : ℚ} (hp : p∈ss) {x : ℝ} (hx : (p:ℝ)≤x ∧ x≤((p+3/2:ℚ):ℝ)) :
    (x,((1-D n:ℚ):ℝ))∈(HP n k ss).boundary := by
  obtain ⟨a,b,hi,ha,hb⟩ := floor_run (n:=n) (k:=k) placed hp
  have hB := infix_boundary hi
  refine hB (hseg_up (a:=(a,1-D n)) (b:=(b,1-D n)) rfl (by dsimp only; linarith) ⟨?_,?_⟩)
  · have : (a:ℝ)≤p := by exact_mod_cast ha
    dsimp only; linarith [hx.1]
  · have : ((p+3/2:ℚ):ℝ)≤b := by exact_mod_cast hb
    dsimp only; linarith [hx.2]

end

end ArtGallery.Orthogonal.BoundaryPoint.HubPoints
end
