module

public import ArtGallery.Orthogonal.BoundaryPoint.HubPoints
public import ArtGallery.Orthogonal.BoundaryPoint.HubRegion
public import ArtGallery.Orthogonal.BoundaryPoint.RealizedHub

/-! # Rectangles inside the hub

Open rectangles that meet no hub edge (by the explicit pieces of `HubEdges`) and contain one filled
point lie in the filled hub; seeds come from boundary points whose one side is known to be empty. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubCells
open Set RectContour BoundaryChart BankCoordinates HubComb HubFloor HubEdges HubPoints HubRegion

section
variable {n k : Nat} {ss : List ℚ}

/-- The hub boundary pieces as real inequalities. -/
theorem pieces (hn : 65≤n) (placed : Placed ss) {q : Point} (hq : q∈(HP n k ss).boundary)
    {F : ℝ} (hF : F=((1-D n:ℚ):ℝ)) :
    q.2=F ∨ q.2=-6 ∨ (∃ j<k+1, q.2=1 ∧ (door j:ℝ)-30≤q.1 ∧ q.1≤(door j:ℝ)+110+1/10) ∨
    (∃ x∈ss, q.2=-6-F ∧ (x:ℝ)≤q.1 ∧ q.1≤(x:ℝ)+3/2) ∨
    (∃ j<k+1, q.2=2*F ∧ (door j:ℝ)+100-1/1000≤q.1 ∧ q.1≤(door j:ℝ)+100+1/1000) ∨
    (∃ x∈ss, (q.1=x ∧ -6≤q.2 ∧ q.2≤-6-F) ∨ (q.1=(x:ℝ)+3/2 ∧ -6≤q.2 ∧ q.2≤-6-F)) ∨
    (∃ x∈ss.tail, (q.1=(x:ℝ)-3 ∧ F≤q.2 ∧ q.2≤F+1/4) ∨ (q.2=F+1/4 ∧ (x:ℝ)-3≤q.1 ∧ q.1≤(x:ℝ)-2) ∨
      (q.1=(x:ℝ)-2 ∧ F+1/100000000≤q.2 ∧ q.2≤F+1/4) ∨
      (q.2=F+1/100000000 ∧ (x:ℝ)-2-1/10≤q.1 ∧ q.1≤(x:ℝ)-2) ∨
      (q.1=(x:ℝ)-2-1/10 ∧ F≤q.2 ∧ q.2≤F+1/100000000)) ∨
    (∃ j<k+1, (q.1=(door j:ℝ)+100-1/1000 ∧ 2*F≤q.2 ∧ q.2≤F) ∨ (q.1=(door j:ℝ)+100+1/1000 ∧ 2*F≤q.2 ∧ q.2≤F) ∨
      (q.1=(door j:ℝ)-30 ∧ -6≤q.2 ∧ q.2≤1) ∨ (q.1=(door j:ℝ)+110 ∧ -6≤q.2 ∧ q.2≤1-1/10000) ∨
      (q.2=1-1/10000 ∧ (door j:ℝ)+110≤q.1 ∧ q.1≤(door j:ℝ)+110+1/10) ∨
      (q.1=(door j:ℝ)+110+1/10 ∧ 1-1/10000≤q.2 ∧ q.2≤1)) ∨
    (q.1=(door k:ℝ)-30 ∧ F+1/100000000≤q.2 ∧ q.2≤1) ∨
    (q.2=F+1/100000000 ∧ (door k:ℝ)-30-1/10≤q.1 ∧ q.1≤(door k:ℝ)-30) ∨
    (q.1=(door k:ℝ)-30-1/10 ∧ F≤q.2 ∧ q.2≤F+1/100000000) ∨
    (q.1=((ss.getLastD 0:ℚ):ℝ)+10 ∧ F≤q.2 ∧ q.2≤-6) := by
  have h := boundary_cases hn placed hq
  simp only [rSec3,rDivP,rDoorP,rEndP,rVS,rHS,eps] at h
  push_cast at h
  subst hF; push_cast
  exact h

theorem F_lt (hn : 65≤n) : ((1-D n:ℚ):ℝ)< -100 := by
  have big : (65:ℚ)≤n := by exact_mod_cast hn
  have : (1-D n:ℚ)< -100 := by
    dsimp [D,BankCoordinates.k]; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) big]
  exact_mod_cast this

theorem door_le (j : Nat) : (door j:ℝ)≤0 := by
  unfold door; push_cast; nlinarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]

theorem door_mono {i j : Nat} (h : i≤j) : (door j:ℝ)≤door i := by
  unfold door; push_cast; have : (i:ℝ)≤j := by exact_mod_cast h
  linarith

theorem slot_far (placed : Placed ss) {x : ℚ} (hx : x∈ss) : (1970:ℝ)<x := by exact_mod_cast placed.far x hx

theorem slot_gap (placed : Placed ss) {x y : ℚ} (hx : x∈ss) (hy : y∈ss) :
    x=y ∨ (x:ℝ)+10≤y ∨ (y:ℝ)+10≤x := by
  rcases pair_gap placed hx hy with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by exact_mod_cast h))
  · exact Or.inr (Or.inr (by exact_mod_cast h))

theorem slot_last (placed : Placed ss) {x : ℚ} (hx : x∈ss) : (x:ℝ)≤((ss.getLastD 0:ℚ):ℝ) := by
  exact_mod_cast last_bound placed x hx

/-- The polygon of the hub is simple. -/
theorem simple (hn : 65≤n) (placed : Placed ss) : (HP n k ss).Simple := RealizedHub.simple placed n k hn

/-- The band column under a base slot, between the floor and the low roof. -/
theorem column_band (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : p∈ss) :
    Ioo (p:ℝ) ((p:ℝ)+3/2) ×ˢ Ioo ((1-D n:ℚ):ℝ) (-6)⊆(HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have pf := slot_far placed hp
  have avoid : ∀ q∈Ioo (p:ℝ) ((p:ℝ)+3/2) ×ˢ Ioo F (-6), q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨j,hj,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨j,hj,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := door_le j; linarith)
      | (have := door_le k; linarith)
      | (have := slot_last placed hp; linarith)
      | (rcases slot_gap placed hx hp with rfl|g|g <;> linarith)
      | (rcases slot_gap placed (List.mem_of_mem_tail hx) hp with rfl|g|g <;> linarith)
  refine seed_in (simple hn placed) (box_preconnected _ _ _ _) avoid
    (floor_slot (k:=k) (n:=n) placed hp (x:=(p:ℝ)+3/4) ⟨by linarith,by push_cast; linarith⟩) (r:=1/8) (by norm_num) ?_
  intro q d1 d2 qf qb
  rw [abs_lt] at d1 d2
  refine ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,?_,by linarith [d2.2]⟩
  rcases lt_trichotomy q.2 F with lo|eq|hi
  · exfalso
    obtain ⟨j,_,a,b,_⟩ := HubColumns.foot_column (Nat.succ_pos k) hn qf lo
    have := door_le j; push_cast at b; linarith [d1.1]
  · exfalso; apply qb
    have := floor_slot (k:=k) (n:=n) placed hp (x:=q.1) ⟨by linarith [d1.1],by push_cast; linarith [d1.2]⟩
    rwa [show q=(q.1,q.2) from rfl,eq]
  · exact hi

/-- The band above the floor dividers, between the western step and the eastern side. -/
theorem band_upper (hn : 65≤n) (placed : Placed ss) :
    Ioo ((door k:ℝ)-30) (((ss.getLastD 0:ℚ):ℝ)+10) ×ˢ Ioo (((1-D n:ℚ):ℝ)+1/4) (-6)⊆(HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have avoid : ∀ q∈Ioo ((door k:ℝ)-30) (((ss.getLastD 0:ℚ):ℝ)+10) ×ˢ Ioo (F+1/4) (-6), q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨j,hj,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨j,hj,h|h|h|h|h|h⟩|h|h|h|h
    all_goals linarith
  obtain ⟨p,hp⟩ : ∃ p, p∈ss := by
    cases ss with
    | nil => exact absurd rfl placed.exists_slot
    | cons a l => exact ⟨a,List.mem_cons_self⟩
  have pf := slot_far placed hp
  have pl := slot_last placed hp
  have dk := door_le k
  exact region_sub (simple hn placed) (box_preconnected _ _ _ _) avoid
    (p:=((p:ℝ)+3/4,-7)) ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,by norm_num⟩
    (column_band hn placed hp ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,by norm_num⟩)

/-- The interior of a shaft, above the low roof. -/
theorem shaft_inside (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : p∈ss) :
    Ioo (p:ℝ) ((p:ℝ)+3/2) ×ˢ Ioo (-6) ((-6-(1-D n):ℚ):ℝ)⊆(HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have pf := slot_far placed hp
  have T : ((-6-(1-D n):ℚ):ℝ)=-6-F := by rw [hF]; push_cast; ring
  rw [T]
  have avoid : ∀ q∈Ioo (p:ℝ) ((p:ℝ)+3/2) ×ˢ Ioo (-6) (-6-F), q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨j,hj,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨j,hj,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := door_le j; linarith)
      | (have := door_le k; linarith)
      | (have := slot_last placed hp; linarith)
      | (rcases slot_gap placed hx hp with rfl|g|g <;> linarith)
      | (rcases slot_gap placed (List.mem_of_mem_tail hx) hp with rfl|g|g <;> linarith)
  refine seed_in (simple hn placed) (box_preconnected _ _ _ _) avoid
    (shaft_top (k:=k) (n:=n) (ss:=ss) hn hp (x:=(p:ℝ)+3/4) ⟨by linarith,by push_cast; linarith⟩) (r:=1/8) (by norm_num) ?_
  intro q d1 d2 qf qb
  rw [abs_lt,T] at d1 d2
  refine ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,by linarith [d2.1],?_⟩
  rcases lt_trichotomy q.2 (-6-F) with lo|eq|hi
  · exact lo
  · exfalso; apply qb
    have := shaft_top (k:=k) (n:=n) (ss:=ss) hn hp (x:=q.1) ⟨by linarith [d1.1],by push_cast; linarith [d1.2]⟩
    rw [T,← eq] at this; exact this
  · exfalso
    obtain ⟨x,_,_,_,c⟩ := HubColumns.shaft_column (Nat.succ_pos k) hn qf (by linarith [d2.1]) (by linarith [d1.1])
    rw [T] at c; dsimp only at d2; linarith [d2.1]

theorem door_apart {i j : Nat} (h : i≠j) : (door i:ℝ)+2000≤door j ∨ (door j:ℝ)+2000≤door i := by
  unfold door; push_cast
  rcases lt_or_gt_of_ne h with l|l
  · have : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast l
    right; linarith
  · have : (j:ℝ)+1≤(i:ℝ) := by exact_mod_cast l
    left; linarith

/-- Points above a cap top are outside. -/
theorem above_cap (hn : 65≤n) (placed : Placed ss) {q : Point} (qf : q∈(HP n k ss).filled)
    (hy : 1<q.2) (hx : q.1<1970) : False := by
  obtain ⟨j,_,_,_,c⟩ := HubSky.upper (Nat.succ_pos k) hn (fun x hx => (placed.far x hx).le) qf (by linarith) hx
  linarith

/-- The interior of a cap, above the low roof. -/
theorem cap_inside (hn : 65≤n) (placed : Placed ss) {j : Nat} (hj : j<k+1) :
    Ioo ((door j:ℝ)-30) ((door j:ℝ)+110) ×ˢ Ioo (-6) 1⊆(HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have dj := door_le j
  have dk := door_mono (Nat.lt_succ_iff.mp hj)
  have avoid : ∀ q∈Ioo ((door j:ℝ)-30) ((door j:ℝ)+110) ×ˢ Ioo (-6) 1, q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨i,hi,h⟩|⟨x,hx,h⟩|⟨i,hi,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨i,hi,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := slot_far placed hx; linarith)
      | (have := slot_far placed (List.mem_of_mem_tail hx); linarith)
      | (obtain ⟨p,hp⟩ : ∃ p, p∈ss := by
          cases ss with
          | nil => exact absurd rfl placed.exists_slot
          | cons a l => exact ⟨a,List.mem_cons_self⟩
         have := slot_far placed hp; have := slot_last placed hp; linarith)
      | (rcases eq_or_ne i j with rfl|ne
         · linarith
         · rcases door_apart ne with g|g <;> linarith)
  refine seed_in (simple hn placed) (box_preconnected _ _ _ _) avoid
    (cap_top (k:=k) (n:=n) (ss:=ss) hj (x:=(door j:ℝ)+100) ⟨by push_cast; linarith,by push_cast; linarith⟩) (r:=1/8)
    (by norm_num) ?_
  intro q d1 d2 qf qb
  rw [abs_lt] at d1 d2
  refine ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,by linarith [d2.1],?_⟩
  rcases lt_trichotomy q.2 1 with lo|eq|hi
  · exact lo
  · exfalso; apply qb
    have := cap_top (k:=k) (n:=n) (ss:=ss) hj (x:=q.1) ⟨by push_cast; linarith [d1.1],by push_cast; linarith [d1.2]⟩
    rwa [show q=(q.1,q.2) from rfl,eq]
  · exact (above_cap hn placed qf hi (by linarith [d1.2])).elim

/-- The strip under a cap top, including the terrace. -/
theorem cap_strip (hn : 65≤n) (placed : Placed ss) {j : Nat} (hj : j<k+1) :
    Ioo ((door j:ℝ)-30) ((door j:ℝ)+110+1/10) ×ˢ Ioo (1-1/10000) 1⊆(HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have dj := door_le j
  have dk := door_mono (Nat.lt_succ_iff.mp hj)
  have avoid : ∀ q∈Ioo ((door j:ℝ)-30) ((door j:ℝ)+110+1/10) ×ˢ Ioo (1-1/10000) 1, q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨i,hi,h⟩|⟨x,hx,h⟩|⟨i,hi,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨i,hi,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := slot_far placed hx; linarith)
      | (have := slot_far placed (List.mem_of_mem_tail hx); linarith)
      | (rcases eq_or_ne i j with rfl|ne
         · linarith
         · rcases door_apart ne with g|g <;> linarith)
  refine seed_in (simple hn placed) (box_preconnected _ _ _ _) avoid
    (cap_top (k:=k) (n:=n) (ss:=ss) hj (x:=(door j:ℝ)+100) ⟨by push_cast; linarith,by push_cast; linarith⟩) (r:=1/20000)
    (by norm_num) ?_
  intro q d1 d2 qf qb
  rw [abs_lt] at d1 d2
  refine ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,by linarith [d2.1],?_⟩
  rcases lt_trichotomy q.2 1 with lo|eq|hi
  · exact lo
  · exfalso; apply qb
    have := cap_top (k:=k) (n:=n) (ss:=ss) hj (x:=q.1) ⟨by push_cast; linarith [d1.1],by push_cast; linarith [d1.2]⟩
    rwa [show q=(q.1,q.2) from rfl,eq]
  · exact (above_cap hn placed qf hi (by linarith [d1.2])).elim

/-- The interior of a foot, below the floor. -/
theorem foot_inside (hn : 65≤n) (placed : Placed ss) {j : Nat} (hj : j<k+1) :
    Ioo ((door j:ℝ)+100-1/1000) ((door j:ℝ)+100+1/1000) ×ˢ Ioo (2*((1-D n:ℚ):ℝ)) ((1-D n:ℚ):ℝ)⊆
      (HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have dj := door_le j
  have avoid : ∀ q∈Ioo ((door j:ℝ)+100-1/1000) ((door j:ℝ)+100+1/1000) ×ˢ Ioo (2*F) F, q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb
    rcases pieces hn placed hb hF with h|h|⟨i,hi,h⟩|⟨x,hx,h⟩|⟨i,hi,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨i,hi,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (rcases eq_or_ne i j with rfl|ne
         · linarith
         · rcases door_apart ne with g|g <;> linarith)
  refine seed_in (simple hn placed) (box_preconnected _ _ _ _) avoid
    (foot_bottom (k:=k) (n:=n) (ss:=ss) hj (x:=(door j:ℝ)+100) ⟨by push_cast; linarith,by push_cast; linarith⟩) (r:=1/2000)
    (by norm_num) ?_
  intro q d1 d2 qf qb
  rw [abs_lt] at d1 d2
  have T : (((2*(1-D n)):ℚ):ℝ)=2*F := by rw [hF]; push_cast; ring
  rw [T] at d2
  refine ⟨⟨by linarith [d1.1],by linarith [d1.2]⟩,?_,by linarith [d2.2]⟩
  rcases lt_trichotomy q.2 (2*F) with lo|eq|hi
  · exfalso
    obtain ⟨i,_,_,_,c⟩ := HubColumns.foot_column (Nat.succ_pos k) hn qf (by linarith [d2.2])
    rw [T] at c; linarith
  · exfalso; apply qb
    have := foot_bottom (k:=k) (n:=n) (ss:=ss) hj (x:=q.1) ⟨by push_cast; linarith [d1.1],by push_cast; linarith [d1.2]⟩
    rw [T,← eq] at this; exact this
  · exact hi

/-- A strip of the band between two floor dividers (no divider strictly inside). -/
theorem gap_band (hn : 65≤n) (placed : Placed ss) {a b : ℝ} (hab : a<b) (ha : (door k:ℝ)-30≤a)
    (hb : b≤((ss.getLastD 0:ℚ):ℝ)+10) (free : ∀ x∈ss.tail, (x:ℝ)-2≤a ∨ b≤(x:ℝ)-3) :
    Ioo a b ×ˢ Ioo ((1-D n:ℚ):ℝ) (-6)⊆(HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have avoid : ∀ q∈Ioo a b ×ˢ Ioo F (-6), q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb'
    rcases pieces hn placed hb' hF with h|h|⟨j,hj,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨j,hj,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (rcases free x hx with g|g <;> linarith)
  exact region_sub (simple hn placed) (box_preconnected _ _ _ _) avoid
    (p:=((a+b)/2,-7)) ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,by norm_num⟩
    (band_upper hn placed ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,by norm_num⟩)

/-- The thin strip along the floor from the slit under a divider to the east of its slot. -/
theorem slit_band (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : p∈ss) :
    Ioo ((p:ℝ)-2-1/10) ((p:ℝ)+3/2) ×ˢ Ioo ((1-D n:ℚ):ℝ) (((1-D n:ℚ):ℝ)+1/100000000)⊆(HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have pf := slot_far placed hp
  have avoid : ∀ q∈Ioo ((p:ℝ)-2-1/10) ((p:ℝ)+3/2) ×ˢ Ioo F (F+1/100000000), q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb'
    rcases pieces hn placed hb' hF with h|h|⟨j,hj,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨j,hj,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := door_le j; linarith)
      | (have := door_le k; linarith)
      | (have := slot_last placed hp; linarith)
      | (rcases slot_gap placed (List.mem_of_mem_tail hx) hp with rfl|g|g <;> linarith)
  exact region_sub (simple hn placed) (box_preconnected _ _ _ _) avoid
    (p:=((p:ℝ)+3/4,F+1/200000000)) ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,
      by dsimp only; linarith⟩
    (column_band hn placed hp ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,
      by dsimp only; linarith⟩)

/-- The thin strip along the floor from the closed western step to the east of the first slot. -/
theorem west_band (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : ss.head?=some p) :
    Ioo ((door k:ℝ)-30-1/10) ((p:ℝ)+3/2) ×ˢ Ioo ((1-D n:ℚ):ℝ) (((1-D n:ℚ):ℝ)+1/100000000)⊆
      (HP n k ss).filled := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  obtain ⟨rest,hss⟩ : ∃ rest, ss=p::rest := by
    cases ss with
    | nil => simp at hp
    | cons a l => simp at hp; exact ⟨l,by rw [hp]⟩
  have hpm : p∈ss := by rw [hss]; exact List.mem_cons_self
  have pf := slot_far placed hpm
  have later : ∀ x∈ss.tail, (p:ℝ)+10≤x := by
    intro x hx
    have srt := placed.sorted
    rw [hss] at srt hx
    exact_mod_cast (List.pairwise_cons.mp srt).1 x hx
  have avoid : ∀ q∈Ioo ((door k:ℝ)-30-1/10) ((p:ℝ)+3/2) ×ˢ Ioo F (F+1/100000000), q∉(HP n k ss).boundary := by
    rintro q ⟨⟨a1,a2⟩,b1,b2⟩ hb'
    rcases pieces hn placed hb' hF with h|h|⟨j,hj,h⟩|⟨x,hx,h⟩|⟨j,hj,h⟩|⟨x,hx,h|h⟩|⟨x,hx,h|h|h|h|h⟩|⟨j,hj,h|h|h|h|h|h⟩|h|h|h|h
    all_goals first
      | linarith
      | (have := door_le j; linarith)
      | (have := later x hx; linarith)
      | (have := slot_last placed hpm; linarith)
      | (rcases slot_gap placed hx hpm with rfl|g|g <;> linarith)
  have dk := door_le k
  exact region_sub (simple hn placed) (box_preconnected _ _ _ _) avoid
    (p:=((p:ℝ)+3/4,F+1/200000000)) ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,
      by dsimp only; linarith⟩
    (column_band hn placed hpm ⟨⟨by dsimp only; linarith,by dsimp only; linarith⟩,by dsimp only; linarith,
      by dsimp only; linarith⟩)

end

end ArtGallery.Orthogonal.BoundaryPoint.HubCells
end
