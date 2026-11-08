module

public import ArtGallery.Orthogonal.BoundaryPoint.CoverAssume
public import ArtGallery.Orthogonal.BoundaryPoint.CopyLower

/-! # Assembling the cover of a wing chart

Every point of a wing chart lies in a certified rectangle of cells, seen from the whole guard
segment of one role, or in a special cell handled separately. With one guard per role standing on
its role's segment (stationary roles at their record point, which lies on their spot), every point
of the chart is seen by one of the guards, in any polygon containing the chart. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingAssemble
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CoverChain CoverAssume ArtGallery.Orthogonal.Hard

/-- Sight is monotone in the filled region. -/
theorem sees_mono {Q P : Polygon} (sub : Q.filled⊆P.filled) {g z : Point} (h : Q.Sees g z) : P.Sees g z :=
  h.trans sub

/-- The record point lies on the spot segment: same grid row (or column), between the ends. -/
def onSpot (r : List Index) : Bool :=
  let a := r.getD 0 (0,0); let b := r.getD 1 (0,0); let c := r.getD 2 (0,0)
  (a.2==b.2 && a.2==c.2 && (decide (b.1≤a.1 ∧ a.1≤c.1) || decide (c.1≤a.1 ∧ a.1≤b.1))) ||
  (a.1==b.1 && a.1==c.1 && (decide (b.2≤a.2 ∧ a.2≤c.2) || decide (c.2≤a.2 ∧ a.2≤b.2)))

section
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

theorem between_seg {u v w : ℝ} (h : (u≤w ∧ w≤v) ∨ (v≤w ∧ w≤u)) {y : ℝ} :
    ((w,y):Point)∈ArtGallery.segment (u,y) (v,y) := by
  rcases eq_or_ne u v with rfl|ne
  · have : w=u := by rcases h with ⟨a,b⟩|⟨a,b⟩ <;> linarith
    exact Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,by ext <;> simp [Geometry.lerp,this]⟩
  · have d : v-u≠0 := sub_ne_zero.mpr ne.symm
    refine Geometry.mem_segment_iff_lerp.mpr ⟨(w-u)/(v-u),?_,?_,?_⟩
    · rcases h with ⟨a,b⟩|⟨a,b⟩
      · rcases eq_or_lt_of_le (a.trans b) with e|l
        · exact absurd e ne
        · exact div_nonneg (by linarith) (by linarith)
      · rcases eq_or_lt_of_le (a.trans b) with e|l
        · exact absurd e.symm ne
        · exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases h with ⟨a,b⟩|⟨a,b⟩
      · rcases eq_or_lt_of_le (a.trans b) with e|l
        · exact absurd e ne
        · exact (div_le_one (by linarith)).mpr (by linarith)
      · rcases eq_or_lt_of_le (a.trans b) with e|l
        · exact absurd e.symm ne
        · rw [div_le_one_of_neg (by linarith)]; linarith
    · ext
      · simp [Geometry.lerp]; field_simp; ring
      · simp [Geometry.lerp]

theorem record_on_spot (G : Good C X Y s A) {r : List Index} (h : onSpot r=true)
    (hn : ∀ p∈[r.getD 0 (0,0),r.getD 1 (0,0),r.getD 2 (0,0)], p.1<C.nx ∧ p.2<C.ny) :
    gridPt X Y (r.getD 0 (0,0))∈ArtGallery.segment (gridPt X Y (CellRoles.spotA r)) (gridPt X Y (CellRoles.spotB r)) := by
  have lx := G.lx; have ly := G.ly
  have lvx {i j : Nat} (hj : j<C.nx) (h : i≤j) := lev_le G.hx (by omega : j<X.length) h
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at hn
  obtain ⟨⟨a1,a2⟩,⟨b1,b2⟩,⟨c1,c2⟩⟩ := hn
  simp only [onSpot,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  simp only [CellRoles.spotA,CellRoles.spotB,gridPt]
  rcases h with ⟨⟨e1,e2⟩,o⟩|⟨⟨e1,e2⟩,o⟩
  · rw [← e1,← e2]
    apply between_seg
    rcases o with ⟨p,q⟩|⟨p,q⟩
    · exact Or.inl ⟨lvx a1 p,lvx c1 q⟩
    · exact Or.inr ⟨lvx a1 p,lvx b1 q⟩
  · rw [← e1,← e2]
    have sw : ((X.getD (r.getD 0 (0,0)).1 0,Y.getD (r.getD 0 (0,0)).2 0):Point)∈
        ArtGallery.segment (X.getD (r.getD 0 (0,0)).1 0,Y.getD (r.getD 1 (0,0)).2 0)
          (X.getD (r.getD 0 (0,0)).1 0,Y.getD (r.getD 2 (0,0)).2 0) := by
      have := between_seg (u:=Y.getD (r.getD 1 (0,0)).2 0) (v:=Y.getD (r.getD 2 (0,0)).2 0)
        (w:=Y.getD (r.getD 0 (0,0)).2 0) (y:=X.getD (r.getD 0 (0,0)).1 0) (by
          rcases o with ⟨p,q⟩|⟨p,q⟩
          · exact Or.inl ⟨lvy a2 p,lvy c2 q⟩
          · exact Or.inr ⟨lvy a2 p,lvy b2 q⟩)
      obtain ⟨t,t0,t1,e⟩ := Geometry.mem_segment_iff_lerp.mp this
      refine Geometry.mem_segment_iff_lerp.mpr ⟨t,t0,t1,?_⟩
      simp only [Geometry.lerp,Prod.mk.injEq] at e ⊢
      exact ⟨by ring,e.1⟩
    exact sw

/-- The completeness check of a cover data module in the form used by `coverA`. -/
theorem comp_of {tiles : List (Nat × Nat × Nat × Nat)} {covered : Nat → Nat → Bool}
    (h : tiles.all (fun t => (List.range' t.1 (t.2.1-t.1)).all fun i =>
      (List.range' t.2.2.1 (t.2.2.2-t.2.2.1)).all fun j => covered i j)=true) :
    ∀ t∈tiles, ∀ i j, t.1 ≤ i → i<t.2.1 → t.2.2.1≤j → j<t.2.2.2 → covered i j=true := by
  intro t ht i j a b c d
  have h1 := List.all_eq_true.mp h t ht
  have h2 := List.all_eq_true.mp h1 i (List.mem_range'_1.mpr ⟨a,by omega⟩)
  exact List.all_eq_true.mp h2 j (List.mem_range'_1.mpr ⟨c,by omega⟩)

theorem nondeg_of {tiles : List (Nat × Nat × Nat × Nat)}
    (h : tiles.all (fun t => decide (t.1<t.2.1 ∧ t.2.2.1<t.2.2.2))=true) :
    ∀ t∈tiles, t.1<t.2.1 ∧ t.2.2.1<t.2.2.2 := by
  intro t ht; simpa using List.all_eq_true.mp h t ht

/-- Each certified rectangle names a role whose guard stands on its segment: a stationary role
(not in `M`) at its record point, which is on its spot when the rectangle uses the spot. -/
def entriesOK (C : Chart) (roles : List (List Index)) (M : List Nat) (rects : List EntryA) : Bool :=
  rects.all fun e => decide (e.role<roles.length) &&
    (if M.contains e.role then !e.point else
      (e.point || onSpot (roles.getD e.role [])) &&
        [(roles.getD e.role []).getD 0 (0,0),(roles.getD e.role []).getD 1 (0,0),
          (roles.getD e.role []).getD 2 (0,0)].all fun p => decide (p.1<C.nx ∧ p.2<C.ny))

theorem guards_on (G : Good C X Y s A) {roles : List (List Index)} {M : List Nat} {rects : List EntryA}
    (h : entriesOK C roles M rects=true) (gd : Nat → Point)
    (hst : ∀ r, r∉M → gd r=gridPt X Y ((roles.getD r []).getD 0 (0,0)))
    (hmv : ∀ r∈M, gd r∈ArtGallery.segment (gridPt X Y (CellRoles.spotA (roles.getD r [])))
      (gridPt X Y (CellRoles.spotB (roles.getD r [])))) :
    ∀ e∈rects, gd e.role∈ArtGallery.segment (gridPt X Y (e.ends roles).1) (gridPt X Y (e.ends roles).2) := by
  intro e he
  have h1 := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h1
  obtain ⟨hl,h2⟩ := h1
  by_cases hm : M.contains e.role=true
  · simp only [hm,ite_true,Bool.not_eq_true'] at h2
    have hm' : e.role∈M := List.contains_iff_mem.mp hm
    simp only [EntryA.ends,h2,Bool.false_eq_true,ite_false]
    exact hmv _ hm'
  · simp only [hm,Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true,
      decide_eq_true_eq] at h2
    have hm' : e.role∉M := fun c => hm (List.contains_iff_mem.mpr c)
    rw [hst _ hm']
    obtain ⟨pt|on,ix⟩ := h2
    · simp only [EntryA.ends,pt,ite_true]
      exact Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,by simp [Geometry.lerp]⟩
    · by_cases pt : e.point=true
      · simp only [EntryA.ends,pt,ite_true]
        exact Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,by simp [Geometry.lerp]⟩
      · simp only [EntryA.ends,pt,Bool.false_eq_true,ite_false]
        exact record_on_spot G on ix

/-- A copy receiver at a parameter in `[0,3/2]` stands on its spot. -/
theorem receiver_mem {X Y : List ℝ} {ra rb : Index} (hy : ra.2=rb.2) {t : ℝ} (ht : 0≤t ∧ t≤3/2) :
    CopyLower.receiver X Y ra rb t∈ArtGallery.segment (gridPt X Y ra) (gridPt X Y rb) := by
  refine Geometry.mem_segment_iff_lerp.mpr ⟨2/3*t,by linarith,by linarith,?_⟩
  simp only [CopyLower.receiver,Geometry.lerp,gridPt,hy]
  ext <;> simp <;> ring

/-- A point is on the degenerate segment at itself. -/
theorem self_mem (p : Point) : p∈ArtGallery.segment p p :=
  Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,by simp [Geometry.lerp]⟩

theorem entries_roles {C : Chart} {roles : List (List Index)} {M : List Nat} {rects : List EntryA}
    (h : entriesOK C roles M rects=true) : ∀ e∈rects, e.role<roles.length := by
  intro e he
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true,decide_eq_true_eq] at this
  exact this.1

theorem cell_prop {special : List (Nat × Nat)} {rects : List EntryA} {i j : Nat}
    (h : (special.contains (i,j) || rects.any (fun e => decide (e.x ≤ i ∧ i+1 ≤ e.x' ∧ e.y ≤ j ∧ j+1 ≤ e.y')))=true) :
    (i,j)∈special ∨ ∃ e∈rects, e.x ≤ i ∧ i+1≤e.x' ∧ e.y≤j ∧ j+1≤e.y' := by
  simp only [Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true,decide_eq_true_eq] at h
  exact h

/-- The cover of a wing chart, transported to any polygon containing it. -/
theorem cover (G : Good C X Y s A) (hnd : ∀ t∈C.tiles, t.1<t.2.1 ∧ t.2.2.1<t.2.2.2)
    {roles : List (List Index)} {rects : List EntryA} {special : List (Nat × Nat)}
    (hok : rects.all (EntryA.good C roles)=true)
    (hcomp : ∀ t∈C.tiles, ∀ i j, t.1 ≤ i → i<t.2.1 → t.2.2.1≤j → j<t.2.2.2 →
      (i,j)∈special ∨ ∃ e∈rects, e.x ≤ i ∧ i+1≤e.x' ∧ e.y≤j ∧ j+1≤e.y')
    {P : Polygon} (sub : (C.poly X Y).filled⊆P.filled) {GS : Set Point} (gd : Nat → Point)
    (hgd : ∀ e∈rects, gd e.role∈GS ∧
      gd e.role∈ArtGallery.segment (gridPt X Y (e.ends roles).1) (gridPt X Y (e.ends roles).2))
    (spec : ∀ c∈special, ∀ z∈Rect (X.getD c.1 0) (X.getD (c.1+1) 0) (Y.getD c.2 0) (Y.getD (c.2+1) 0),
      z∈(C.poly X Y).filled → ∃ g∈GS, P.Sees g z)
    {z : Point} (hz : z∈(C.poly X Y).filled) : ∃ g∈GS, P.Sees g z := by
  rcases coverA G hnd hok hcomp hz with ⟨e,he,_,sees⟩|⟨c,hc,hzc⟩
  · obtain ⟨m,on⟩ := hgd e he
    exact ⟨gd e.role,m,sees_mono sub (sees _ on)⟩
  · exact spec c hc z hzc hz

end

end ArtGallery.Orthogonal.BoundaryPoint.WingAssemble
end
