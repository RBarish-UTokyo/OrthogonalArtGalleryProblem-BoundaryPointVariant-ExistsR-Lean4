module

public import ArtGallery.Orthogonal.BoundaryPoint.HubCells

/-! # Regions outside the hub

The hub lies between its closed western step and its eastern side; above the low roof and west of
the slots only the caps are filled; inside each floor divider only its slit is filled; beside each
terrace and west of the western wall nothing is filled. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubOutside
open Set RectContour BoundaryChart BankCoordinates HubComb HubFloor HubEdges HubPoints HubRegion HubCells

section
variable {n k : Nat} {ss : List ℚ}

/-- Every vertex of the hub cycle lies between the western step and the eastern side. -/
theorem vertex_x (hn : 65≤n) (placed : Placed ss) {v : Vertex} (hv : v∈hubCycle n (k+1) ss) :
    door k-30-1/10≤v.1 ∧ v.1≤ss.getLastD 0+10 := by
  have hdk : door k≤0 := by unfold door; exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have dmono (j : Nat) (hj : j<k+1) : door k≤door j ∧ door j≤0 := by
    unfold door; constructor
    · have : (j:ℚ)≤k := by exact_mod_cast Nat.lt_succ_iff.mp hj
      linarith
    · exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  obtain ⟨p,hp⟩ : ∃ p, p∈ss := by
    cases ss with
    | nil => exact absurd rfl placed.exists_slot
    | cons a l => exact ⟨a,List.mem_cons_self⟩
  have far : ∀ x∈ss, 1970<x := placed.far
  have lb : ∀ x∈ss, x≤ss.getLastD 0 := fun x hx => last_bound placed x hx
  have rp := lb p hp
  have fp := far p hp
  rw [cycle_eq] at hv
  simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,List.mem_flatMap,
    List.mem_reverse,List.mem_range] at hv
  rcases hv with (((((h|⟨j,hj,h⟩)|⟨x,hx,h⟩)|h|h)|⟨x,hx,h⟩)|⟨j,hj,h⟩)|h|h
  · subst h; constructor <;> dsimp only <;> linarith
  · have := dmono j hj
    simp only [foot,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> constructor <;> dsimp only <;> linarith
  · have hx' := List.mem_of_mem_tail hx
    have := far x hx'; have := lb x hx'
    simp only [divider,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> dsimp only <;> linarith
  · subst h; constructor <;> dsimp only <;> linarith
  · subst h; constructor <;> dsimp only <;> linarith
  · have := far x hx; have := lb x hx
    simp only [shaft,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> constructor <;> dsimp only <;> linarith
  · have := dmono j hj
    simp only [capPath] at h
    split at h
    · simp only [List.mem_cons,List.not_mem_nil,or_false,List.mem_append,List.mem_singleton] at h
      rcases h with (rfl|rfl|rfl|rfl|rfl)|rfl <;> constructor <;> dsimp only <;> linarith
    · simp only [List.mem_cons,List.not_mem_nil,or_false,List.mem_append,List.append_nil] at h
      rcases h with rfl|rfl|rfl|rfl|rfl <;> constructor <;> dsimp only <;> linarith
  · subst h; constructor <;> dsimp only <;> linarith
  · subst h; constructor <;> dsimp only <;> linarith

/-- Every boundary point of the hub lies between the western step and the eastern side. -/
theorem boundary_x (hn : 65≤n) (placed : Placed ss) {q : Point} (hq : q∈(HP n k ss).boundary) :
    ((door k-30-1/10:ℚ):ℝ)≤q.1 ∧ q.1≤((ss.getLastD 0+10:ℚ):ℝ) := by
  obtain ⟨i,hi,edge⟩ := hq
  let l := hubCycle n (k+1) ss
  have size : (HP n k ss).n=l.length := by simp [HP,Polygon.n,l]
  rw [size] at hi
  have vtx (j : Nat) (hj : j<l.length) : (HP n k ss).vtx j=ratPoint (l.getD j (0,0)) ∧ l.getD j (0,0)∈l := by
    refine ⟨?_,?_⟩
    · change (l.map ratPoint).getD j (0,0)=_
      rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map,List.getD_eq_getElem _ _ hj]
    · rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  change q∈ArtGallery.segment ((HP n k ss).vtx i) ((HP n k ss).vtx ((i+1)%(HP n k ss).n)) at edge
  rw [size] at edge
  obtain ⟨e1,m1⟩ := vtx i hi
  obtain ⟨e2,m2⟩ := vtx _ (Nat.mod_lt _ (by omega))
  rw [e1,e2] at edge
  have b1 := vertex_x hn placed m1
  have b2 := vertex_x hn placed m2
  obtain ⟨t,t0,t1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp edge
  have x := HighStep.interpolated ((l.getD i (0,0)).1:ℝ) ((l.getD ((i+1)%l.length) (0,0)).1:ℝ) t0 t1
  simp only [Geometry.lerp_fst,ratPoint]
  constructor
  · exact (le_min (by exact_mod_cast b1.1) (by exact_mod_cast b2.1)).trans x.1
  · exact x.2.trans (max_le (by exact_mod_cast b1.2) (by exact_mod_cast b2.2))

/-- The hub lies between its western step and its eastern side. -/
theorem filled_x (hn : 65≤n) (placed : Placed ss) {q : Point} (hq : q∈(HP n k ss).filled) :
    ((door k-30-1/10:ℚ):ℝ)≤q.1 ∧ q.1≤((ss.getLastD 0+10:ℚ):ℝ) := by
  constructor
  · by_contra! c
    obtain ⟨t,t0,ht⟩ := ray_hits (d:=((-1,0):Point)) (by simp) hq
    have := (boundary_x hn placed ht).1
    simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,mul_neg,mul_one] at this
    linarith
  · by_contra! c
    obtain ⟨t,t0,ht⟩ := ray_hits (d:=((1,0):Point)) (by simp) hq
    have := (boundary_x hn placed ht).2
    simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,mul_one] at this
    linarith

/-- Above the low roof and west of the slots only the caps are filled. -/
theorem above_roof (hn : 65≤n) (placed : Placed ss) {q : Point} (hq : q∈(HP n k ss).filled)
    (hy : -6<q.2) (hx : q.1<1970) :
    ∃ j<k+1, (door j:ℝ)-30≤q.1 ∧ q.1≤(door j:ℝ)+110+1/10 ∧ q.2≤1 := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  obtain ⟨t,t0,ht⟩ := ray_hits (d:=((0,1):Point)) (by simp) hq
  set h : Point := q+t • ((0,1):Point) with hh
  have h1 : h.1=q.1 := by simp [h]
  have h2 : h.2=q.2+t := by simp [h]
  rcases pieces hn placed ht hF with c|c|⟨j,hj,c⟩|⟨x,hx',c⟩|⟨j,hj,c⟩|⟨x,hx',c|c⟩|⟨x,hx',c|c|c|c|c⟩|
      ⟨j,hj,c|c|c|c|c|c⟩|c|c|c|c
  all_goals first
    | (exfalso; linarith)
    | (exfalso; have := slot_far placed hx'; linarith)
    | (exfalso; have := slot_far placed (List.mem_of_mem_tail hx'); linarith)
    | exact ⟨j,hj,by linarith,by linarith,by linarith⟩
    | exact ⟨k,Nat.lt_succ_self k,by linarith,by linarith,by linarith⟩

/-- Inside a floor divider only its slit is filled. -/
theorem wall_out (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : p∈ss.tail) {q : Point} (hq : q∈(HP n k ss).filled)
    (x0 : (p:ℝ)-3<q.1) (x1 : q.1<(p:ℝ)-2) (y0 : ((1-D n:ℚ):ℝ)≤q.2) (y1 : q.2<((1-D n:ℚ):ℝ)+1/4) :
    (p:ℝ)-2-1/10≤q.1 ∧ q.2≤((1-D n:ℚ):ℝ)+1/100000000 := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have hpm := List.mem_of_mem_tail hp
  have pf := slot_far placed hpm
  have pl := slot_last placed hpm
  have dk := door_le k
  let W1 := Ioo ((p:ℝ)-3) ((p:ℝ)-2-1/10) ×ˢ Ioo F (F+1/4)
  let W2 := Ioo ((p:ℝ)-3) ((p:ℝ)-2) ×ˢ Ioo (F+1/100000000) (F+1/4)
  have pre : IsPreconnected (W1∪W2) :=
    (box_preconnected _ _ _ _).union ((p:ℝ)-5/2,F+1/8) ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
      ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩ (box_preconnected _ _ _ _)
  have avoid : ∀ w∈W1∪W2, w∉(HP n k ss).boundary := by
    rintro w (⟨⟨a1,a2⟩,b1,b2⟩|⟨⟨a1,a2⟩,b1,b2⟩) hb
    all_goals
      rcases pieces hn placed hb hF with h|h|⟨j,hj,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|
        ⟨j,hj,h|h|h|h|h|h⟩|h|h|h|h
      all_goals first
        | linarith
        | (have := door_le j; linarith)
        | (have := slot_far placed hx; linarith)
        | (rcases slot_gap placed (List.mem_of_mem_tail hx) hpm with rfl|g|g <;> linarith)
  have topB : ∀ x : ℝ, (p:ℝ)-3≤x → x≤(p:ℝ)-2 → ((x,F+1/4):Point)∈(HP n k ss).boundary := by
    intro x a b
    have := divider_top (n:=n) (k:=k) hp (x:=x) ⟨by push_cast; linarith,by push_cast; linarith⟩
    rwa [show ((1-D n+1/4:ℚ):ℝ)=F+1/4 by rw [hF]; push_cast; ring] at this
  have ext := seed_out (simple hn placed) pre avoid (topB ((p:ℝ)-5/2) (by linarith) (by linarith))
    (r:=1/8) (by norm_num) (by
      intro w d1 d2 wn
      rw [abs_lt] at d1 d2
      rcases lt_trichotomy w.2 (F+1/4) with lo|eq|hi
      · exact Or.inr ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,by linarith [d2.1],lo⟩
      · exact absurd (Jordan.boundary_subset_filled _ (by
          have := topB w.1 (by linarith [d1.1]) (by linarith [d1.2]); rwa [← eq] at this)) wn
      · exact absurd (band_upper hn placed ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,hi,by linarith [d2.2]⟩) wn)
  by_contra c
  rw [not_and_or,not_le,not_le] at c
  rcases lt_or_eq_of_le y0 with ylo|yeq
  · rcases c with c|c
    · exact ext q (Or.inl ⟨⟨x0,c⟩,ylo,y1⟩) hq
    · exact ext q (Or.inr ⟨⟨x0,x1⟩,c,y1⟩) hq
  · -- on the floor line under the divider: the points above and below are outside
    rcases c with c|c
    · refine out_of_rows (simple hn placed) (r:=min (q.1-((p:ℝ)-3)) ((p:ℝ)-2-1/10-q.1)/2)
        (by have := lt_min (sub_pos.mpr x0) (sub_pos.mpr c); positivity) ?_ hq
      intro w d1 d2 ne
      have m1 := min_le_left (q.1-((p:ℝ)-3)) ((p:ℝ)-2-1/10-q.1)
      have m2 := min_le_right (q.1-((p:ℝ)-3)) ((p:ℝ)-2-1/10-q.1)
      rw [abs_lt] at d1 d2
      rcases lt_or_gt_of_ne ne with lo|hi
      · intro wf
        obtain ⟨j,_,a,b,_⟩ := HubColumns.foot_column (Nat.succ_pos k) hn wf (by linarith [hF])
        have := door_le j; push_cast at b; linarith [d1.1]
      · exact ext w (Or.inl ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,by rw [yeq]; exact hi,
          by linarith [d2.2]⟩)
    · rw [← yeq] at c; linarith

/-- Beside a terrace, below its step, nothing is filled. -/
theorem terrace_out (hn : 65≤n) (placed : Placed ss) {j : Nat} (hj : j<k+1) {q : Point}
    (hq : q∈(HP n k ss).filled) (x0 : (door j:ℝ)+110<q.1) (x1 : q.1≤(door j:ℝ)+110+1/10)
    (y0 : -6<q.2) (y1 : q.2<1-1/10000) : False := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have dj := door_le j
  have dk := door_mono (Nat.lt_succ_iff.mp hj)
  let V := Ioo ((door j:ℝ)+110) ((door j:ℝ)+110+1/10) ×ˢ Ioo (-6:ℝ) (1-1/10000)
  have avoid : ∀ w∈V, w∉(HP n k ss).boundary := by
    rintro w ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨i,hi,h⟩|⟨x,hx,h⟩|⟨i,hi,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|
      ⟨i,hi,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := slot_far placed hx; linarith)
      | (have := slot_far placed (List.mem_of_mem_tail hx); linarith)
      | (rcases eq_or_ne i j with rfl|ne
         · linarith
         · rcases door_apart ne with g|g <;> linarith)
  have sideB : ∀ y : ℝ, -6≤y → y≤1-1/10000 → (((door j:ℝ)+110,y):Point)∈(HP n k ss).boundary := by
    intro y a b
    have := cap_right (n:=n) (ss:=ss) hj (y:=y) ⟨a,by push_cast; linarith⟩
    rwa [show ((door j+110:ℚ):ℝ)=(door j:ℝ)+110 by push_cast; ring] at this
  have ext := seed_out (simple hn placed) (box_preconnected _ _ _ _) avoid (sideB (-11/2) (by norm_num) (by norm_num))
    (r:=1/20) (by norm_num) (by
      intro w d1 d2 wn
      rw [abs_lt] at d1 d2
      rcases lt_trichotomy w.1 ((door j:ℝ)+110) with lo|eq|hi
      · exact absurd (cap_inside hn placed hj ⟨⟨by dsimp only at d1; linarith [d1.1],lo⟩,
          by dsimp only at d2; linarith [d2.1],by dsimp only at d2; linarith [d2.2]⟩) wn
      · exact absurd (Jordan.boundary_subset_filled _ (by
          have := sideB w.2 (by dsimp only at d2; linarith [d2.1]) (by dsimp only at d2; linarith [d2.2])
          rwa [← eq] at this)) wn
      · exact ⟨⟨hi,by dsimp only at d1; linarith [d1.2]⟩,by dsimp only at d2; linarith [d2.1],
          by dsimp only at d2; linarith [d2.2]⟩)
  rcases lt_or_eq_of_le x1 with xlo|xeq
  · exact ext q ⟨⟨x0,xlo⟩,y0,y1⟩ hq
  · -- on the terrace line: to the west the strip, to the east no cap
    refine out_of_cols (simple hn placed) (r:=min (q.2+6) (1-1/10000-q.2)/2 |> min (1/20))
      (by have := lt_min (show (0:ℝ)<q.2+6 by linarith) (show (0:ℝ)<1-1/10000-q.2 by linarith); positivity) ?_ hq
    intro w d1 d2 ne wf
    have m0 := min_le_left (1/20:ℝ) (min (q.2+6) (1-1/10000-q.2)/2)
    have m1 := min_le_right (1/20:ℝ) (min (q.2+6) (1-1/10000-q.2)/2)
    have m2 := min_le_left (q.2+6) (1-1/10000-q.2)
    have m3 := min_le_right (q.2+6) (1-1/10000-q.2)
    rw [abs_lt] at d1 d2
    rcases lt_or_gt_of_ne ne with lo|hi
    · exact ext w ⟨⟨by linarith [d1.1],by rw [← xeq]; exact lo⟩,by linarith [d2.1],by linarith [d2.2]⟩ wf
    · obtain ⟨i,hi',a,b,_⟩ := above_roof hn placed wf (by linarith [d2.1]) (by linarith [d1.2])
      rcases eq_or_ne i j with rfl|ne'
      · linarith
      · rcases door_apart ne' with g|g <;> linarith [d1.1,d1.2]

/-- West of the western wall only the thin floor strip is filled. -/
theorem west_out (hn : 65≤n) (placed : Placed ss) {q : Point} (hq : q∈(HP n k ss).filled)
    (hx : q.1<(door k:ℝ)-30) : ((1-D n:ℚ):ℝ)≤q.2 ∧ q.2≤((1-D n:ℚ):ℝ)+1/100000000 := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have F7' : F< -100 := by rw [hF]; exact F7
  have dk := door_le k
  have bx := filled_x hn placed hq
  push_cast at bx
  -- not above the low roof
  have notUp : ∀ w : Point, w∈(HP n k ss).filled → w.1<(door k:ℝ)-30 → -6<w.2 → False := by
    intro w wf wx wy
    obtain ⟨j,hj,a,_,_⟩ := above_roof hn placed wf wy (by linarith)
    have := door_mono (Nat.lt_succ_iff.mp hj); linarith
  -- not below the floor
  have notDown : ∀ w : Point, w∈(HP n k ss).filled → w.1<(door k:ℝ)-30 → w.2<F → False := by
    intro w wf wx wy
    obtain ⟨j,hj,a,_,_⟩ := HubColumns.foot_column (Nat.succ_pos k) hn wf (by linarith [hF])
    have := door_mono (Nat.lt_succ_iff.mp hj); push_cast at a; linarith
  -- the band west of the wall
  let Wst := Ioo ((door k:ℝ)-30-1/10) ((door k:ℝ)-30) ×ˢ Ioo (F+1/100000000) (-6:ℝ)
  have avoid : ∀ w∈Wst, w∉(HP n k ss).boundary := by
    rintro w ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨i,hi,h⟩|⟨x,hx',h⟩|⟨i,hi,h⟩|⟨x,hx',h|h⟩|⟨x,hx',h|h|h|h|h⟩|
      ⟨i,hi,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := slot_far placed hx'; linarith)
      | (have := slot_far placed (List.mem_of_mem_tail hx'); linarith)
      | (have := door_mono (Nat.lt_succ_iff.mp hi); linarith)
      | (obtain ⟨p,hp⟩ : ∃ p, p∈ss := by
          cases ss with
          | nil => exact absurd rfl placed.exists_slot
          | cons a l => exact ⟨a,List.mem_cons_self⟩
         have := slot_far placed hp; have := slot_last placed hp; linarith)
  have wallB : ∀ y : ℝ, F+1/100000000≤y → y≤1 → (((door k:ℝ)-30,y):Point)∈(HP n k ss).boundary := by
    intro y a b
    have := west_wall (n:=n) (k:=k) (ss:=ss) hn (y:=y) ⟨by rw [hF] at a; push_cast at a ⊢; linarith,b⟩
    rwa [show ((door k-30:ℚ):ℝ)=(door k:ℝ)-30 by push_cast; ring] at this
  obtain ⟨p,hp⟩ : ∃ p, p∈ss := by
    cases ss with
    | nil => exact absurd rfl placed.exists_slot
    | cons a l => exact ⟨a,List.mem_cons_self⟩
  have pf := slot_far placed hp
  have pl := slot_last placed hp
  have ext := seed_out (simple hn placed) (box_preconnected _ _ _ _) avoid (wallB (-7) (by linarith) (by norm_num))
    (r:=1/20) (by norm_num) (by
      intro w d1 d2 wn
      rw [abs_lt] at d1 d2
      rcases lt_trichotomy w.1 ((door k:ℝ)-30) with lo|eq|hi
      · exact ⟨⟨by dsimp only at d1; linarith [d1.1],lo⟩,by dsimp only at d2; linarith [d2.1],
          by dsimp only at d2; linarith [d2.2]⟩
      · exact absurd (Jordan.boundary_subset_filled _ (by
          have := wallB w.2 (by dsimp only at d2; linarith [d2.1]) (by dsimp only at d2; linarith [d2.2])
          rwa [← eq] at this)) wn
      · exact absurd (band_upper hn placed ⟨⟨hi,by dsimp only at d1; linarith [d1.2]⟩,
          by dsimp only at d2; linarith [d2.1],by dsimp only at d2; linarith [d2.2]⟩) wn)
  -- points of the band west of the wall (including its western edge) are outside
  have band : ∀ w : Point, w∈(HP n k ss).filled → w.1<(door k:ℝ)-30 → F+1/100000000<w.2 → w.2< -6 → False := by
    intro w wf wx wy0 wy1
    have bw := filled_x hn placed wf
    push_cast at bw
    rcases lt_or_eq_of_le bw.1 with xlo|xeq
    · exact ext w ⟨⟨xlo,wx⟩,wy0,wy1⟩ wf
    · refine out_of_cols (simple hn placed) (r:=min (w.2-(F+1/100000000)) (-6-w.2)/2 |> min (1/20))
        (by have := lt_min (sub_pos.mpr wy0) (show (0:ℝ)< -6-w.2 by linarith); positivity) ?_ wf
      intro u d1 d2 ne uf
      have m0 := min_le_left (1/20:ℝ) (min (w.2-(F+1/100000000)) (-6-w.2)/2)
      have m1 := min_le_right (1/20:ℝ) (min (w.2-(F+1/100000000)) (-6-w.2)/2)
      have m2 := min_le_left (w.2-(F+1/100000000)) (-6-w.2)
      have m3 := min_le_right (w.2-(F+1/100000000)) (-6-w.2)
      rw [abs_lt] at d1 d2
      rcases lt_or_gt_of_ne ne with lo|hi
      · have bu := filled_x hn placed uf; push_cast at bu; linarith [bu.1]
      · exact ext u ⟨⟨by linarith,by linarith [d1.2]⟩,by linarith [d2.1],by linarith [d2.2]⟩ uf
  refine ⟨?_,?_⟩
  · by_contra c; exact notDown q hq hx (by linarith)
  · by_contra c
    push_neg at c
    rcases lt_trichotomy q.2 (-6) with lo|eq|hi
    · exact band q hq hx c lo
    · refine out_of_rows (simple hn placed) (r:=min (1/2) ((door k:ℝ)-30-q.1))
        (lt_min (by norm_num) (by linarith)) ?_ hq
      intro u d1 d2 ne uf
      have m0 := min_le_left (1/2:ℝ) ((door k:ℝ)-30-q.1)
      have m1 := min_le_right (1/2:ℝ) ((door k:ℝ)-30-q.1)
      rw [abs_lt] at d1 d2
      rcases lt_or_gt_of_ne ne with lo'|hi'
      · exact band u uf (by linarith [d1.2]) (by linarith [d2.1]) (by linarith)
      · exact notUp u uf (by linarith [d1.2]) (by linarith)
    · exact notUp q hq hx hi

end

end ArtGallery.Orthogonal.BoundaryPoint.HubOutside
end
