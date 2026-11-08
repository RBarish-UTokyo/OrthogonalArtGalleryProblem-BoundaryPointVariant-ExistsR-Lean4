module

public import ArtGallery.Orthogonal.BoundaryPoint.HubOutside
public import ArtGallery.Orthogonal.BoundaryPoint.HubDivider

/-! # The hub is seen by its base and step guards

Base guards stand on the floor of their slots, step guards on the cap tops at `door j + 100`.
Every filled point of the hub lies in a closed rectangle inside the hub that contains one of them:
a shaft column, a cap column with its foot, a cap top strip, a band strip between floor dividers,
a slit strip, or the western floor strip seen by the first base guard; over a divider the step
guard or the next base guard sees it (`HubDivider.covered`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubCover
open Set RectContour BoundaryChart BankCoordinates HubComb HubFloor HubEdges HubPoints HubRegion HubCells HubOutside
open ChimneyRegion

section Cells
variable {P : Polygon}

theorem cell_eq (a b c d : ℝ) : cell a b c d=Icc a b ×ˢ Icc c d := by
  ext p; simp only [cell,Set.mem_prod,Set.mem_Icc,Set.mem_setOf_eq]; tauto

/-- The closure of an open box inside the filled region. -/
theorem cell_of {a b c d : ℝ} (hab : a<b) (hcd : c<d) (h : Ioo a b ×ˢ Ioo c d⊆P.filled) : cell a b c d⊆P.filled := by
  rw [cell_eq,← box_closure hab hcd]
  exact closure_minimal h (Jordan.isClosed_filled P)

/-- Two stacked cells with the same abscissae. -/
theorem stack {a b c m d : ℝ} (lo : cell a b c m⊆P.filled) (hi : cell a b m d⊆P.filled) : cell a b c d⊆P.filled := by
  rintro p ⟨p0,p1,p2,p3⟩
  rcases le_total p.2 m with h|h
  · exact lo ⟨p0,p1,p2,h⟩
  · exact hi ⟨p0,p1,h,p3⟩

theorem mono {a b c d a' b' c' d' : ℝ} (h : cell a b c d⊆P.filled) (ha : a≤a') (hb : b'≤b) (hc : c≤c') (hd : d'≤d) :
    cell a' b' c' d'⊆P.filled :=
  fun p ⟨p0,p1,p2,p3⟩ => h ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- A guard and a target in one cell inside the filled region. -/
theorem sees_in {a b c d : ℝ} (h : cell a b c d⊆P.filled) {g z : Point} (hg : g∈cell a b c d) (hz : z∈cell a b c d) :
    P.Sees g z := by
  intro w hw
  apply h
  obtain ⟨t,t0,t1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hw
  obtain ⟨g0,g1,g2,g3⟩ := hg
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have x := HighStep.interpolated g.1 z.1 t0 t1
  have y := HighStep.interpolated g.2 z.2 t0 t1
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [Geometry.lerp_fst,Geometry.lerp_snd]
  exacts [(le_min g0 z0).trans x.1,x.2.trans (max_le g1 z1),(le_min g2 z2).trans y.1,y.2.trans (max_le g3 z3)]

end Cells

section
variable {n k : Nat} {ss : List ℚ}

/-- The closed column of a slot: band and shaft. -/
theorem shaft_column (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : p∈ss) :
    cell (p:ℝ) ((p:ℝ)+3/2) ((1-D n:ℚ):ℝ) ((-6-(1-D n):ℚ):ℝ)⊆(HP n k ss).filled := by
  have F7 := F_lt hn
  have T : ((-6-(1-D n):ℚ):ℝ)=-6-((1-D n:ℚ):ℝ) := by push_cast; ring
  refine stack (m:=-6) (cell_of (by linarith) (by linarith) (column_band hn placed hp))
    (cell_of (by linarith) (by rw [T]; linarith) (shaft_inside hn placed hp))

/-- The closed column of a cap: band and cap. -/
theorem cap_column (hn : 65≤n) (placed : Placed ss) {j : Nat} (hj : j<k+1) :
    cell ((door j:ℝ)-30) ((door j:ℝ)+110) ((1-D n:ℚ):ℝ) 1⊆(HP n k ss).filled := by
  have F7 := F_lt hn
  have dj := door_le j
  have dk := door_mono (Nat.lt_succ_iff.mp hj)
  obtain ⟨p,hp⟩ : ∃ p, p∈ss := by
    cases ss with
    | nil => exact absurd rfl placed.exists_slot
    | cons a l => exact ⟨a,List.mem_cons_self⟩
  have pf := slot_far placed hp
  have pl := slot_last placed hp
  refine stack (m:=-6) (cell_of (by linarith) (by linarith) (gap_band hn placed (by linarith) (by linarith)
    (by linarith) (fun x hx => Or.inr (by have := slot_far placed (List.mem_of_mem_tail hx); linarith))))
    (cell_of (by linarith) (by norm_num) (cap_inside hn placed hj))

/-- The closed column of a foot, up to its cap top. -/
theorem foot_column (hn : 65≤n) (placed : Placed ss) {j : Nat} (hj : j<k+1) :
    cell ((door j:ℝ)+100-1/1000) ((door j:ℝ)+100+1/1000) (2*((1-D n:ℚ):ℝ)) 1⊆(HP n k ss).filled := by
  have F7 := F_lt hn
  exact stack (m:=((1-D n:ℚ):ℝ)) (cell_of (by linarith) (by linarith) (foot_inside hn placed hj))
    (mono (cap_column hn placed hj) (by linarith) (by linarith) le_rfl le_rfl)

/-- The closed strip under a cap top. -/
theorem top_strip (hn : 65≤n) (placed : Placed ss) {j : Nat} (hj : j<k+1) :
    cell ((door j:ℝ)-30) ((door j:ℝ)+110+1/10) (1-1/10000) 1⊆(HP n k ss).filled :=
  cell_of (by linarith) (by norm_num) (cap_strip hn placed hj)

/-- The closed band above the dividers. -/
theorem band_cell (hn : 65≤n) (placed : Placed ss) :
    cell ((door k:ℝ)-30) (((ss.getLastD 0:ℚ):ℝ)+10) (((1-D n:ℚ):ℝ)+1/4) (-6)⊆(HP n k ss).filled := by
  have F7 := F_lt hn
  have dk := door_le k
  obtain ⟨p,hp⟩ : ∃ p, p∈ss := by
    cases ss with
    | nil => exact absurd rfl placed.exists_slot
    | cons a l => exact ⟨a,List.mem_cons_self⟩
  have pf := slot_far placed hp
  have pl := slot_last placed hp
  exact cell_of (by linarith) (by linarith) (band_upper hn placed)

/-- A closed band strip between dividers. -/
theorem gap_cell (hn : 65≤n) (placed : Placed ss) {a b : ℝ} (hab : a<b) (ha : (door k:ℝ)-30≤a)
    (hb : b≤((ss.getLastD 0:ℚ):ℝ)+10) (free : ∀ x∈ss.tail, (x:ℝ)-2≤a ∨ b≤(x:ℝ)-3) :
    cell a b ((1-D n:ℚ):ℝ) (-6)⊆(HP n k ss).filled := by
  have F7 := F_lt hn
  exact cell_of hab (by linarith) (gap_band hn placed hab ha hb free)

/-- The closed slit strip of a divider, reaching east over its slot. -/
theorem slit_cell (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : p∈ss) :
    cell ((p:ℝ)-2-1/10) ((p:ℝ)+3/2) ((1-D n:ℚ):ℝ) (((1-D n:ℚ):ℝ)+1/100000000)⊆(HP n k ss).filled :=
  cell_of (by linarith) (by linarith) (slit_band hn placed hp)

/-- The closed western floor strip. -/
theorem west_cell (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : ss.head?=some p) :
    cell ((door k:ℝ)-30-1/10) ((p:ℝ)+3/2) ((1-D n:ℚ):ℝ) (((1-D n:ℚ):ℝ)+1/100000000)⊆(HP n k ss).filled := by
  have hpm : p∈ss := by
    cases ss with
    | nil => simp at hp
    | cons a l => simp at hp; rw [hp]; exact List.mem_cons_self
  have := slot_far placed hpm
  have := door_le k
  exact cell_of (by linarith) (by linarith) (west_band hn placed hp)

open Classical in
/-- Every filled point of the hub is seen by a base guard (on the floor of its slot, at offset
`t p ∈ [0,3/2]`) or by a step guard (on its cap top at `door j + 100`). -/
theorem hub_cover (hn : 65≤n) (placed : Placed ss) (hbig : ∀ x∈ss, (x:ℝ)+20≤11/10*(D n:ℝ))
    (t : ℚ → ℝ) (ht : ∀ p∈ss, 0≤t p ∧ t p≤3/2) {z : Point} (hz : z∈(HP n k ss).filled) :
    (∃ p∈ss, (HP n k ss).Sees ((p:ℝ)+t p,((1-D n:ℚ):ℝ)) z) ∨
      ∃ j<k+1, (HP n k ss).Sees ((door j:ℝ)+100,1) z := by
  set F : ℝ := ((1-D n:ℚ):ℝ) with hF
  have F7 := F_lt hn
  have FD : F=1-(D n:ℝ) := by rw [hF]; push_cast; ring
  have dk := door_le k
  have bx := filled_x hn placed hz
  push_cast at bx
  obtain ⟨p0,rest,hss⟩ : ∃ p0 rest, ss=p0::rest := by
    cases ss with
    | nil => exact absurd rfl placed.exists_slot
    | cons a l => exact ⟨a,l,rfl⟩
  have hp0 : p0∈ss := by rw [hss]; exact List.mem_cons_self
  have head : ss.head?=some p0 := by rw [hss]; rfl
  have tailEq : ss.tail=rest := by rw [hss]; rfl
  have later : ∀ x∈ss.tail, (p0:ℝ)+10≤x := by
    intro x hx
    have srt := placed.sorted
    rw [hss] at srt; rw [tailEq] at hx
    exact_mod_cast (List.pairwise_cons.mp srt).1 x hx
  have p0f := slot_far placed hp0
  have p0l := slot_last placed hp0
  have guardIn (p : ℚ) (hp : p∈ss) {a b c d : ℝ} (ha : a≤p) (hb : (p:ℝ)+3/2≤b) (hc : c≤F) (hd : F≤d) :
      ((p:ℝ)+t p,F)∈cell a b c d := by
    have := ht p hp
    exact ⟨by dsimp only; linarith,by dsimp only; linarith,hc,hd⟩
  -- below the floor: a foot, seen from its cap top
  rcases lt_or_ge z.2 F with below|above
  · obtain ⟨j,hj,a,b,c⟩ := HubColumns.foot_column (Nat.succ_pos k) hn hz (by rw [← hF]; exact below)
    have dj := door_le j
    push_cast at a b c
    refine Or.inr ⟨j,hj,sees_in (foot_column hn placed hj) ⟨by dsimp only; linarith,by dsimp only; linarith,
      by dsimp only; linarith,le_rfl⟩ ⟨by linarith,by linarith,by linarith [c],by linarith⟩⟩
  -- above the low roof: a shaft or a cap
  rcases lt_or_ge (-6) z.2 with high|low
  · by_cases east : (1101/10:ℝ)<z.1
    · obtain ⟨p,hp,a,b,c⟩ := HubColumns.shaft_column (Nat.succ_pos k) hn hz high east
      push_cast at b c
      refine Or.inl ⟨p,hp,sees_in (shaft_column hn placed hp) (guardIn p hp le_rfl (by push_cast; linarith) le_rfl
        (by push_cast; linarith)) ⟨a,by linarith,by linarith,by push_cast; linarith⟩⟩
    · obtain ⟨j,hj,a,b,c⟩ := above_roof hn placed hz high (by linarith)
      have dj := door_le j
      by_cases inCap : z.1≤(door j:ℝ)+110
      · exact Or.inr ⟨j,hj,sees_in (cap_column hn placed hj) ⟨by dsimp only; linarith,by dsimp only; linarith,
          by dsimp only; linarith,le_rfl⟩ ⟨a,inCap,by linarith,c⟩⟩
      · by_cases topY : 1-1/10000≤z.2
        · exact Or.inr ⟨j,hj,sees_in (top_strip hn placed hj) ⟨by dsimp only; linarith,by dsimp only; linarith,
            by dsimp only; norm_num,le_rfl⟩ ⟨a,b,topY,c⟩⟩
        · exact (terrace_out hn placed hj hz (by linarith) b high (by linarith)).elim
  -- the band between the floor and the low roof
  by_cases west : z.1<(door k:ℝ)-30
  · obtain ⟨_,wy⟩ := west_out hn placed hz west
    exact Or.inl ⟨p0,hp0,sees_in (west_cell hn placed head) (guardIn p0 hp0 (by linarith) le_rfl le_rfl
      (by linarith)) ⟨bx.1,by linarith,above,wy⟩⟩
  push_neg at west
  by_cases S : ∃ p∈ss, (p:ℝ)-2≤z.1
  · -- the last slot whose divider starts at or west of the target
    let Sf := ss.toFinset.filter (fun p : ℚ => (p:ℝ)-2≤z.1)
    have ne : Sf.Nonempty := by
      obtain ⟨p,hp,h⟩ := S; exact ⟨p,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp,h⟩⟩
    obtain ⟨ps,hps,hmax⟩ := Sf.exists_max_image id ne
    obtain ⟨psm,psx⟩ := Finset.mem_filter.mp hps
    have psm' := List.mem_toFinset.mp psm
    have below_ps : ∀ x∈ss, (x:ℝ)-2≤z.1 → (x:ℝ)≤ps := fun x hx h =>
      by exact_mod_cast hmax x (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hx,h⟩)
    have psf := slot_far placed psm'
    have psl := slot_last placed psm'
    by_cases T : ∃ q∈ss, z.1<(q:ℝ)-2
    · let Tf := ss.toFinset.filter (fun p : ℚ => z.1<(p:ℝ)-2)
      have neT : Tf.Nonempty := by
        obtain ⟨p,hp,h⟩ := T; exact ⟨p,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp,h⟩⟩
      obtain ⟨q,hq,hmin⟩ := Tf.exists_min_image id neT
      obtain ⟨qm,qx⟩ := Finset.mem_filter.mp hq
      have qm' := List.mem_toFinset.mp qm
      have above_q : ∀ x∈ss, z.1<(x:ℝ)-2 → (q:ℝ)≤x := fun x hx h =>
        by exact_mod_cast hmin x (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hx,h⟩)
      have split : ∀ x∈ss, (x:ℝ)≤ps ∨ (q:ℝ)≤x := by
        intro x hx
        rcases le_or_gt ((x:ℝ)-2) z.1 with h|h
        · exact Or.inl (below_ps x hx h)
        · exact Or.inr (above_q x hx h)
      have gapq : (ps:ℝ)+10≤q := by
        rcases slot_gap placed psm' qm' with e|g|g
        · rw [e] at psx; linarith
        · exact g
        · linarith
      have qf := slot_far placed qm'
      have ql := slot_last placed qm'
      have minimal : ∀ x∈ss, (p0:ℝ)≤x := by
        intro x hx
        rw [hss] at hx
        rcases List.mem_cons.mp hx with e|h
        · rw [e]
        · have := later x (by rw [tailEq]; exact h); linarith
      have qtail : q∈ss.tail := by
        rw [tailEq]
        have qm'' := qm'
        rw [hss] at qm''
        rcases List.mem_cons.mp qm'' with e|h
        · exfalso
          have := minimal ps psm'
          rw [e] at gapq; linarith
        · exact h
      by_cases xq : z.1<(q:ℝ)-3
      · refine Or.inl ⟨ps,psm',sees_in (gap_cell hn placed (a:=(ps:ℝ)-2) (b:=(q:ℝ)-3) (by linarith) (by linarith)
          (by linarith) (fun x hx => ?_)) (guardIn ps psm' (by linarith) (by linarith) le_rfl (by linarith))
          ⟨psx,xq.le,above,low⟩⟩
        rcases split x (List.mem_of_mem_tail hx) with h|h
        · left; linarith
        · right; linarith
      · push_neg at xq
        by_cases yh : F+1/4≤z.2
        · -- over the divider of `q`
          have hq3 := ht q qm'
          have cov := HubDivider.covered (P:=HP n k ss) (u:=(q:ℝ)-2) (d:=2+t q) (a:=(q:ℝ)-2-z.1) (D:=(D n:ℝ)) (y:=z.2)
            (by have := F7; push_cast at this; linarith) (by linarith) (by have := hbig q qm'; linarith) (by linarith)
            ⟨by linarith,by linarith⟩ ⟨by rw [FD] at yh; linarith,low⟩
            (mono (cap_column hn placed (j:=0) (Nat.succ_pos k)) (by norm_num [door]) (by norm_num [door])
              (by rw [← FD]; linarith) le_rfl)
            (mono (band_cell hn placed) (by linarith) (by linarith) (by rw [← FD]) le_rfl)
            (mono (gap_cell hn placed (a:=(q:ℝ)-2) (b:=(q:ℝ)+3/2) (by linarith) (by linarith) (by linarith)
              (fun x hx => by
                rcases slot_gap placed (List.mem_of_mem_tail hx) qm' with e|g|g
                · left; rw [e]
                · left; linarith
                · right; linarith)) le_rfl (by linarith) (by rw [← FD]) le_rfl)
            (mono (band_cell hn placed) (by linarith) (by linarith) (by rw [← FD]) le_rfl)
          rw [show (q:ℝ)-2-((q:ℝ)-2-z.1)=z.1 by ring,show (q:ℝ)-2+(2+t q)=(q:ℝ)+t q by ring,← FD] at cov
          have zeq : ((z.1,z.2):Point)=z := rfl
          rw [zeq] at cov
          rcases cov with h|h
          · exact Or.inr ⟨0,Nat.succ_pos k,by simpa [door] using h⟩
          · exact Or.inl ⟨q,qm',h⟩
        · push_neg at yh
          rcases lt_or_eq_of_le xq with xlt|xeq
          · obtain ⟨wx,wy⟩ := wall_out hn placed qtail hz xlt (by linarith) above yh
            exact Or.inl ⟨q,qm',sees_in (slit_cell hn placed qm') (guardIn q qm' (by linarith) le_rfl le_rfl
              (by linarith)) ⟨wx,by linarith,above,wy⟩⟩
          · refine Or.inl ⟨ps,psm',sees_in (gap_cell hn placed (a:=(ps:ℝ)-2) (b:=(q:ℝ)-3) (by linarith)
              (by linarith) (by linarith) (fun x hx => ?_)) (guardIn ps psm' (by linarith) (by linarith) le_rfl
              (by linarith)) ⟨psx,xeq.symm.le,above,low⟩⟩
            rcases split x (List.mem_of_mem_tail hx) with h|h
            · left; linarith
            · right; linarith
    · push_neg at T
      refine Or.inl ⟨ps,psm',sees_in (gap_cell hn placed (a:=(ps:ℝ)-2) (b:=((ss.getLastD 0:ℚ):ℝ)+10) (by linarith)
        (by linarith) le_rfl (fun x hx => Or.inl (by
          have := below_ps x (List.mem_of_mem_tail hx) (T x (List.mem_of_mem_tail hx)); linarith)))
        (guardIn ps psm' (by linarith) (by linarith) le_rfl (by linarith)) ⟨psx,bx.2,above,low⟩⟩
  · push_neg at S
    have zs := S p0 hp0
    refine Or.inl ⟨p0,hp0,sees_in (gap_cell hn placed (a:=(door k:ℝ)-30) (b:=(p0:ℝ)+3/2) (by linarith) le_rfl
      (by linarith) (fun x hx => Or.inr (by have := later x hx; linarith)))
      (guardIn p0 hp0 (by linarith) le_rfl le_rfl (by linarith)) ⟨west,by linarith,above,low⟩⟩

end

end ArtGallery.Orthogonal.BoundaryPoint.HubCover
end
