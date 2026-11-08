module

public import ArtGallery.Orthogonal.BoundaryPoint.SepCert

/-! # Certified exclusions of a guard segment from a whole grid cell

A target cell is an atom-code pair: odd codes are grid lines and even codes are
the open intervals between consecutive lines. A guard segment joins two grid
nodes. A `cross` certificate names a cycle edge that separates the guard
segment from the cell, and certifies the determinant signs of both edge ends
at every corner of the closed cell from both guard ends. Zero signs are
allowed as long as one corner has strict signs from both guard ends; the
determinant is affine in the target, so it keeps a strict sign on the
relatively open cell. Every segment from the guard segment to the cell then
properly crosses the edge. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CellCert
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert RegisterForm MarginCert ArtGallery.Orthogonal.Hard

/-- The grid nodes at the corners of the closure of an atom cell. -/
def corners (c : Nat × Nat) : List Index :=
  (if c.1%2=1 then [lo c.1] else [lo c.1,hi c.1]).flatMap fun x =>
    (if c.2%2=1 then [lo c.2] else [lo c.2,hi c.2]).map fun y => (x,y)

/-- Four signs at one corner: `(g₀,a)`, `(g₀,b)`, `(g₁,a)`, `(g₁,b)`. -/
abbrev Quad := Sign × Sign × Sign × Sign

def Quad.strictA (q : Quad) : Bool := !q.1.isZero && !q.2.2.1.isZero
def Quad.strictB (q : Quad) : Bool := !q.2.1.isZero && !q.2.2.2.isZero

/-- Corner checks, zipped with the signs. -/
def zipOK (C : Chart) (pos : Bool) (g₀ g₁ a b : Index) : List Index → List Quad → Bool
  | [],[] => true
  | w::ws,q::qs => C.detSign pos w g₀ a q.1 && C.detSign (!pos) w g₀ b q.2.1 &&
      C.detSign pos w g₁ a q.2.2.1 && C.detSign (!pos) w g₁ b q.2.2.2 && zipOK C pos g₀ g₁ a b ws qs
  | _,_ => false

def cross (C : Chart) (g₀ g₁ : Index) (cell : Nat × Nat) (k : Nat) (pos : Bool) (qs : List Quad) : Bool :=
  let a := C.node k
  let b := C.next k
  decide (k<C.n) && decide (side a b cell≠0) && decide (sideNode a b g₀= -side a b cell) &&
    decide (sideNode a b g₁= -side a b cell) &&
    zipOK C pos g₀ g₁ a b (corners cell) qs && qs.any Quad.strictA && qs.any Quad.strictB &&
    decide (g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny) &&
    decide (Inner C.nx cell.1 ∧ Inner C.ny cell.2)

/-- Corner checks for one edge end only, zipped with the signs `(g₀,v)`, `(g₁,v)`. -/
def zipOne (C : Chart) (pos : Bool) (g₀ g₁ v : Index) : List Index → List (Sign × Sign) → Bool
  | [],[] => true
  | w::ws,q::qs => C.detSign pos w g₀ v q.1 && C.detSign pos w g₁ v q.2 && zipOne C pos g₀ g₁ v ws qs
  | _,_ => false

/-- A certificate for the far end `v` of edge `k` (`v` is the edge's first node if `first`); the
sign at the other end is supplied separately for the particular guard and target. -/
def crossOne (C : Chart) (g₀ g₁ : Index) (cell : Nat × Nat) (k : Nat) (pos first : Bool)
    (qs : List (Sign × Sign)) : Bool :=
  let a := C.node k
  let b := C.next k
  let v := if first then a else b
  decide (k<C.n) && decide (side a b cell≠0) && decide (sideNode a b g₀= -side a b cell) &&
    decide (sideNode a b g₁= -side a b cell) &&
    zipOne C pos g₀ g₁ v (corners cell) qs && qs.any (fun q => !q.1.isZero && !q.2.isZero) &&
    decide (g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny) &&
    decide (Inner C.nx cell.1 ∧ Inner C.ny cell.2)

/-- Strictly inside an axis-parallel edge from `a` to `b`. -/
def strictIn (a b z : Index) : Bool :=
  (decide (a.1=z.1 ∧ b.1=z.1) && strictly a.2 b.2 z.2) || (decide (a.2=z.2 ∧ b.2=z.2) && strictly a.1 b.1 z.1)

/-- Both guard ends lie strictly inside edge `k`, and the cell lies strictly outside its half-plane. -/
def half (C : Chart) (g₀ g₁ : Index) (cell : Nat × Nat) (k : Nat) : Bool :=
  decide (k<C.n) && strictIn (C.node k) (C.next k) g₀ && strictIn (C.node k) (C.next k) g₁ &&
    decide (side (C.node k) (C.next k) cell<0)

section Sound
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

/-- An affine function of the target, written as a determinant. -/
private theorem det_interp (g v : Point) (x₀ x₁ y₀ y₁ μ ν : ℝ) :
    ArtGallery.det (x₀+μ*(x₁-x₀),y₀+ν*(y₁-y₀)) g v=
      (1-μ)*(1-ν)*ArtGallery.det (x₀,y₀) g v+μ*(1-ν)*ArtGallery.det (x₁,y₀) g v+
      (1-μ)*ν*ArtGallery.det (x₀,y₁) g v+μ*ν*ArtGallery.det (x₁,y₁) g v := by
  simp only [ArtGallery.det]; ring

/-- A coordinate in an atom cell, as a parameter between its two bounding lines. -/
private theorem param {xs : List ℝ} (hx : xs.IsChain (·<·)) {c : Nat} (hc : Inner xs.length c) {z : ℝ}
    (hz : atom z xs=c) :
    ∃ μ : ℝ, z=xs.getD (lo c) 0+μ*(xs.getD (hi c) 0-xs.getD (lo c) 0) ∧
      (c%2=1 → μ=0 ∧ xs.getD (hi c) 0=xs.getD (lo c) 0) ∧ (c%2=0 → 0<μ ∧ μ<1) := by
  rcases Nat.mod_two_eq_zero_or_one c with ev|od
  · have hlo : lo c<xs.length := by unfold lo; unfold Inner hi at hc; omega
    have step : lo c<hi c := by unfold lo hi; unfold Inner at hc; omega
    have lt := level_lt hx hc.2 step
    have l1 : xs.getD (lo c) 0<z := by
      have le := (line_le hx hlo z).mpr (by rw [hz]; unfold line lo; unfold Inner at hc; omega)
      rcases le.lt_or_eq with p|p
      · exact p
      · exfalso
        have := (compare_line hx hlo z).2.mp p.symm
        rw [hz] at this; unfold line lo at this; omega
    have l2 : z<xs.getD (hi c) 0 := by
      have h := le_line hx hc.2 z
      have nle : ¬(atom z xs≤line (hi c)) → False := by intro n; apply n; rw [hz]; unfold line hi; omega
      have hle := h.mpr (by by_contra n; exact nle n)
      rcases hle.lt_or_eq with p|p
      · exact p
      · exfalso
        have := (compare_line hx hc.2 z).2.mp p
        rw [hz] at this; unfold line hi at this; omega
    refine ⟨(z-xs.getD (lo c) 0)/(xs.getD (hi c) 0-xs.getD (lo c) 0),?_,fun h => by omega,fun _ => ⟨?_,?_⟩⟩
    · have hne : xs.getD (hi c) 0-xs.getD (lo c) 0≠0 := (sub_pos.mpr lt).ne'
      field_simp; ring
    · exact div_pos (by linarith) (by linarith)
    · exact (div_lt_one (by linarith)).mpr (by linarith)
  · have e := on_line hx hc od hz
    have same : hi c=lo c := by unfold hi lo; omega
    refine ⟨0,by rw [e]; ring,fun _ => ⟨rfl,by rw [same]⟩,fun h => by omega⟩

/-- The determinant at a cell point is a positive combination of its values at the corners. -/
private theorem cell_pos (G : Good C X Y s A) {cell : Nat × Nat}
    (hc : Inner C.nx cell.1 ∧ Inner C.ny cell.2) {w : Point} (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2)
    {g v : Point}
    (nonneg : ∀ c∈corners cell, 0≤ArtGallery.det (gridPt X Y c) g v)
    (strict : ∃ c∈corners cell, 0<ArtGallery.det (gridPt X Y c) g v) :
    0<ArtGallery.det w g v := by
  have hx : Inner X.length cell.1 := by rw [G.lx]; exact hc.1
  have hy : Inner Y.length cell.2 := by rw [G.ly]; exact hc.2
  obtain ⟨μ,eμ,oμ,iμ⟩ := param G.hx hx wx
  obtain ⟨ν,eν,oν,iν⟩ := param G.hy hy wy
  have wpt : w=(X.getD (lo cell.1) 0+μ*(X.getD (hi cell.1) 0-X.getD (lo cell.1) 0),
      Y.getD (lo cell.2) 0+ν*(Y.getD (hi cell.2) 0-Y.getD (lo cell.2) 0)) := Prod.ext eμ eν
  rw [wpt,det_interp]
  -- the four corner values
  let d00 := ArtGallery.det (X.getD (lo cell.1) 0,Y.getD (lo cell.2) 0) g v
  let d10 := ArtGallery.det (X.getD (hi cell.1) 0,Y.getD (lo cell.2) 0) g v
  let d01 := ArtGallery.det (X.getD (lo cell.1) 0,Y.getD (hi cell.2) 0) g v
  let d11 := ArtGallery.det (X.getD (hi cell.1) 0,Y.getD (hi cell.2) 0) g v
  have mem (x y : Nat) (hx' : x∈(if cell.1%2=1 then [lo cell.1] else [lo cell.1,hi cell.1]))
      (hy' : y∈(if cell.2%2=1 then [lo cell.2] else [lo cell.2,hi cell.2])) : (x,y)∈corners cell :=
    List.mem_flatMap.mpr ⟨x,hx',List.mem_map.mpr ⟨y,hy',rfl⟩⟩
  obtain ⟨c,hc',sc⟩ := strict
  simp only [corners,List.mem_flatMap,List.mem_map] at hc'
  obtain ⟨x,hx',y,hy',rfl⟩ := hc'
  rcases Nat.mod_two_eq_zero_or_one cell.1 with e1|o1 <;> rcases Nat.mod_two_eq_zero_or_one cell.2 with e2|o2
  · -- open rectangle
    have n00 := nonneg _ (mem (lo cell.1) (lo cell.2) (by simp [e1]) (by simp [e2]))
    have n10 := nonneg _ (mem (hi cell.1) (lo cell.2) (by simp [e1]) (by simp [e2]))
    have n01 := nonneg _ (mem (lo cell.1) (hi cell.2) (by simp [e1]) (by simp [e2]))
    have n11 := nonneg _ (mem (hi cell.1) (hi cell.2) (by simp [e1]) (by simp [e2]))
    simp only [gridPt] at n00 n10 n01 n11 sc
    obtain ⟨m0,m1⟩ := iμ e1
    obtain ⟨v0,v1⟩ := iν e2
    have w00 : 0<(1-μ)*(1-ν) := mul_pos (by linarith) (by linarith)
    have w10 : 0<μ*(1-ν) := mul_pos m0 (by linarith)
    have w01 : 0<(1-μ)*ν := mul_pos (by linarith) v0
    have w11 : 0<μ*ν := mul_pos m0 v0
    have t00 := mul_nonneg w00.le n00
    have t10 := mul_nonneg w10.le n10
    have t01 := mul_nonneg w01.le n01
    have t11 := mul_nonneg w11.le n11
    simp only [e1,e2,Nat.zero_ne_one,ite_false,List.mem_cons,List.not_mem_nil,or_false] at hx' hy'
    rcases hx' with rfl|rfl <;> rcases hy' with rfl|rfl
    · nlinarith [mul_pos w00 sc]
    · nlinarith [mul_pos w01 sc]
    · nlinarith [mul_pos w10 sc]
    · nlinarith [mul_pos w11 sc]
  · -- open horizontal segment on a line
    obtain ⟨n0,same⟩ := oν o2
    have n00 := nonneg _ (mem (lo cell.1) (lo cell.2) (by simp [e1]) (by simp [o2]))
    have n10 := nonneg _ (mem (hi cell.1) (lo cell.2) (by simp [e1]) (by simp [o2]))
    simp only [gridPt] at n00 n10 sc
    obtain ⟨m0,m1⟩ := iμ e1
    subst n0
    simp only [e1,o2,Nat.zero_ne_one,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hx' hy'
    subst hy'
    rw [same]
    rcases hx' with rfl|rfl
    · nlinarith [mul_pos (show 0<1-μ by linarith) sc,mul_nonneg m0.le n10]
    · nlinarith [mul_pos m0 sc,mul_nonneg (show 0≤1-μ by linarith) n00]
  · -- open vertical segment on a line
    obtain ⟨n0,same⟩ := oμ o1
    have n00 := nonneg _ (mem (lo cell.1) (lo cell.2) (by simp [o1]) (by simp [e2]))
    have n01 := nonneg _ (mem (lo cell.1) (hi cell.2) (by simp [o1]) (by simp [e2]))
    simp only [gridPt] at n00 n01 sc
    obtain ⟨v0,v1⟩ := iν e2
    subst n0
    simp only [e2,o1,Nat.zero_ne_one,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hx' hy'
    subst hx'
    rw [same]
    rcases hy' with rfl|rfl
    · nlinarith [mul_pos (show 0<1-ν by linarith) sc,mul_nonneg v0.le n01]
    · nlinarith [mul_pos v0 sc,mul_nonneg (show 0≤1-ν by linarith) n00]
  · -- a grid node
    obtain ⟨n0,s1⟩ := oμ o1
    obtain ⟨m0,s2⟩ := oν o2
    subst n0; subst m0
    simp only [o1,o2,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hx' hy'
    subst hx'; subst hy'
    simp only [gridPt] at sc
    simpa using sc


theorem zipOK_mem {pos : Bool} {g₀ g₁ a b : Index} :
    ∀ {ws : List Index} {qs : List Quad}, zipOK C pos g₀ g₁ a b ws qs=true →
    ∀ i, i<qs.length → ∃ w q, ws[i]?=some w ∧ qs[i]?=some q ∧
      C.detSign pos w g₀ a q.1=true ∧ C.detSign (!pos) w g₀ b q.2.1=true ∧
      C.detSign pos w g₁ a q.2.2.1=true ∧ C.detSign (!pos) w g₁ b q.2.2.2=true
  | [],[],_ => by intro i hi; simp at hi
  | [],_::_,h => by simp [zipOK] at h
  | _::_,[],h => by simp [zipOK] at h
  | w::ws,q::qs,h => by
    simp only [zipOK,Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,rest⟩ := h
    intro i hi
    cases i with
    | zero => exact ⟨w,q,rfl,rfl,h1,h2,h3,h4⟩
    | succ i => simpa using zipOK_mem rest i (by simpa using hi)

theorem zipOK_cover {pos : Bool} {g₀ g₁ a b : Index} :
    ∀ {ws : List Index} {qs : List Quad}, zipOK C pos g₀ g₁ a b ws qs=true → ∀ w∈ws, ∃ i, i<qs.length ∧ ws[i]?=some w
  | [],[],_ => by simp
  | [],_::_,h => by simp [zipOK] at h
  | _::_,[],h => by simp [zipOK] at h
  | w::ws,q::qs,h => by
    simp only [zipOK,Bool.and_eq_true] at h
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · exact ⟨0,by simp,rfl⟩
    · obtain ⟨i,hi,e⟩ := zipOK_cover h.2 v hv
      exact ⟨i+1,by simpa using hi,by simpa using e⟩

theorem corner_range {cell : Nat × Nat} (hc : Inner C.nx cell.1 ∧ Inner C.ny cell.2) :
    ∀ c∈corners cell, c.1<C.nx ∧ c.2<C.ny := by
  intro c hc'
  simp only [corners,List.mem_flatMap,List.mem_map] at hc'
  obtain ⟨x,hx,y,hy,rfl⟩ := hc'
  have l1 : lo cell.1<C.nx := by unfold lo; unfold Inner hi at hc; omega
  have l2 : lo cell.2<C.ny := by unfold lo; unfold Inner hi at hc; omega
  constructor
  · split at hx <;> simp at hx <;> rcases hx with rfl|rfl <;> first | exact l1 | exact hc.1.2
  · split at hy <;> simp at hy <;> rcases hy with rfl|rfl <;> first | exact l2 | exact hc.2.2

/-- One sign family along a guard segment and over a whole cell. -/
private theorem along_cell (G : Good C X Y s A) {cell : Nat × Nat} (hc : Inner C.nx cell.1 ∧ Inner C.ny cell.2)
    {w : Point} (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2) {g₀ g₁ v : Point} {t : ℝ}
    (t0 : 0≤t) (t1 : t≤1)
    (nonneg : ∀ c∈corners cell, 0≤ArtGallery.det (gridPt X Y c) g₀ v ∧ 0≤ArtGallery.det (gridPt X Y c) g₁ v)
    (strict : ∃ c∈corners cell, 0<ArtGallery.det (gridPt X Y c) g₀ v ∧ 0<ArtGallery.det (gridPt X Y c) g₁ v) :
    0<ArtGallery.det w (Geometry.lerp g₀ g₁ t) v := by
  apply cell_pos G hc wx wy
  · intro c hc'
    rw [Geometry.det_lerp_mid]
    have h := nonneg c hc'
    nlinarith [mul_nonneg (show 0≤1-t by linarith) h.1,mul_nonneg t0 h.2]
  · obtain ⟨c,hc',h⟩ := strict
    refine ⟨c,hc',?_⟩
    rw [Geometry.det_lerp_mid]
    rcases eq_or_lt_of_le t0 with e|e
    · subst e; simpa using h.1
    · nlinarith [mul_pos e h.2,mul_nonneg (show 0≤1-t by linarith) h.1.le]

private theorem swap_det (p g v : Point) : ArtGallery.det p g v= -ArtGallery.det p v g := by
  simp only [ArtGallery.det]; ring

private theorem along_cell_neg (G : Good C X Y s A) {cell : Nat × Nat} (hc : Inner C.nx cell.1 ∧ Inner C.ny cell.2)
    {w : Point} (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2) {g₀ g₁ v : Point} {t : ℝ}
    (t0 : 0≤t) (t1 : t≤1)
    (nonpos : ∀ c∈corners cell, ArtGallery.det (gridPt X Y c) g₀ v≤0 ∧ ArtGallery.det (gridPt X Y c) g₁ v≤0)
    (strict : ∃ c∈corners cell, ArtGallery.det (gridPt X Y c) g₀ v<0 ∧ ArtGallery.det (gridPt X Y c) g₁ v<0) :
    ArtGallery.det w (Geometry.lerp g₀ g₁ t) v<0 := by
  have key := cell_pos G hc wx wy (g:=v) (v:=Geometry.lerp g₀ g₁ t) ?_ ?_
  · rw [swap_det]; linarith
  · intro c hc'
    rw [swap_det _ v,Geometry.det_lerp_mid]
    have h := nonpos c hc'
    nlinarith [mul_nonpos_iff.mpr (Or.inl ⟨show 0≤1-t by linarith,h.1⟩),mul_nonpos_iff.mpr (Or.inl ⟨t0,h.2⟩)]
  · obtain ⟨c,hc',h⟩ := strict
    refine ⟨c,hc',?_⟩
    rw [swap_det _ v,Geometry.det_lerp_mid]
    rcases eq_or_lt_of_le t0 with e|e
    · subst e; simp; linarith [h.1]
    · nlinarith [mul_pos e (neg_pos.mpr h.2),mul_nonneg (show 0≤1-t by linarith) (neg_nonneg.mpr h.1.le)]

theorem cross_sound (G : Good C X Y s A) {g₀ g₁ : Index} {cell : Nat × Nat} {k : Nat} {pos : Bool}
    {qs : List Quad} (h : cross C g₀ g₁ cell k pos qs=true) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁)) {w : Point}
    (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2) : ¬(C.poly X Y).Sees z w := by
  simp only [cross,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk,ne⟩,o₀⟩,o₁⟩,zipped⟩,⟨qa,qam,sa⟩⟩,⟨qb,qbm,sb⟩⟩,⟨r₀x,r₀y,r₁x,r₁y⟩⟩,hc⟩ := h
  intro sees
  have nr := node_range G k hk
  have xr := next_range G k hk
  have ax := axis_next G.axis hk
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  have rg₀ : g₀.1<C.nx ∧ g₀.2<C.ny := ⟨r₀x,r₀y⟩
  have rg₁ : g₁.1<C.nx ∧ g₁.2<C.ny := ⟨r₁x,r₁y⟩
  have rn : (C.node k).1<C.nx ∧ (C.node k).2<C.ny := by rw [←G.lx,←G.ly]; exact nr
  have rx : (C.next k).1<C.nx ∧ (C.next k).2<C.ny := by rw [←G.lx,←G.ly]; exact xr
  obtain ⟨t,t0,t1,zt⟩ := Geometry.mem_segment_iff_lerp.mp hz
  have corner (c : Index) (hc' : c∈corners cell) : ∃ q∈qs,
      C.detSign pos c g₀ (C.node k) q.1=true ∧ C.detSign (!pos) c g₀ (C.next k) q.2.1=true ∧
      C.detSign pos c g₁ (C.node k) q.2.2.1=true ∧ C.detSign (!pos) c g₁ (C.next k) q.2.2.2=true := by
    obtain ⟨i,hi,e⟩ := zipOK_cover zipped c hc'
    obtain ⟨w',q,ew,eq,f1,f2,f3,f4⟩ := zipOK_mem zipped i hi
    rw [e] at ew; cases ew
    exact ⟨q,List.mem_of_getElem? eq,f1,f2,f3,f4⟩
  have strictCorner (q : Quad) (hq : q∈qs) : ∃ c∈corners cell,
      C.detSign pos c g₀ (C.node k) q.1=true ∧ C.detSign (!pos) c g₀ (C.next k) q.2.1=true ∧
      C.detSign pos c g₁ (C.node k) q.2.2.1=true ∧ C.detSign (!pos) c g₁ (C.next k) q.2.2.2=true := by
    obtain ⟨i,hi,e⟩ := List.getElem_of_mem hq
    obtain ⟨w',q',ew,eq,f1,f2,f3,f4⟩ := zipOK_mem zipped i hi
    rw [List.getElem?_eq_getElem hi,e] at eq; cases eq
    exact ⟨w',List.mem_of_getElem? ew,f1,f2,f3,f4⟩
  have cr := corner_range (C:=C) hc
  have real (c : Index) (hc' : c∈corners cell) (g : Index) (hg : g.1<C.nx ∧ g.2<C.ny) (v : Index)
      (hv : v.1<C.nx ∧ v.2<C.ny) (p : Bool) (sg : Sign) (d : C.detSign p c g v sg=true) :
      (p=true → 0≤ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)) ∧
      (p=false → ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)≤0) ∧
      (sg.isZero=false → (p=true → 0<ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)) ∧
        (p=false → ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)<0)) := by
    have f := detSign_sound G (cr c hc') hg hv d
    cases hz' : sg.isZero
    · have := f.2 hz'
      exact ⟨fun e => (this.1 e).le,fun e => (this.2 e).le,fun _ => this⟩
    · have := f.1 hz'
      exact ⟨fun _ => this.ge,fun _ => this.le,fun e => by simp at e⟩
  -- the family at the first edge end has the sign `pos`, the second the sign `!pos`
  have fam (v : Index) (hv : v.1<C.nx ∧ v.2<C.ny) (p : Bool)
      (cs : ∀ c∈corners cell, ∃ s₀ s₁ : Sign, C.detSign p c g₀ v s₀=true ∧ C.detSign p c g₁ v s₁=true)
      (st : ∃ c∈corners cell, ∃ s₀ s₁ : Sign, C.detSign p c g₀ v s₀=true ∧ C.detSign p c g₁ v s₁=true ∧
        s₀.isZero=false ∧ s₁.isZero=false) :
      (p=true → 0<ArtGallery.det w z (gridPt X Y v)) ∧ (p=false → ArtGallery.det w z (gridPt X Y v)<0) := by
    rw [zt]
    obtain ⟨c',hc'',s₀,s₁,d₀,d₁,z₀,z₁⟩ := st
    cases p with
    | true =>
      refine ⟨fun _ => along_cell G hc wx wy t0 t1 ?_ ⟨c',hc'',((real c' hc'' g₀ rg₀ v hv true s₀ d₀).2.2 z₀).1 rfl,
        ((real c' hc'' g₁ rg₁ v hv true s₁ d₁).2.2 z₁).1 rfl⟩,fun e => by simp at e⟩
      intro c hc'
      obtain ⟨u₀,u₁,e₀,e₁⟩ := cs c hc'
      exact ⟨(real c hc' g₀ rg₀ v hv true u₀ e₀).1 rfl,(real c hc' g₁ rg₁ v hv true u₁ e₁).1 rfl⟩
    | false =>
      refine ⟨fun e => by simp at e,fun _ => along_cell_neg G hc wx wy t0 t1 ?_
        ⟨c',hc'',((real c' hc'' g₀ rg₀ v hv false s₀ d₀).2.2 z₀).2 rfl,((real c' hc'' g₁ rg₁ v hv false s₁ d₁).2.2 z₁).2 rfl⟩⟩
      intro c hc'
      obtain ⟨u₀,u₁,e₀,e₁⟩ := cs c hc'
      exact ⟨(real c hc' g₀ rg₀ v hv false u₀ e₀).2.1 rfl,(real c hc' g₁ rg₁ v hv false u₁ e₁).2.1 rfl⟩
  have fa := fam (C.node k) rn pos
    (fun c hc' => by obtain ⟨q,_,d1,_,d3,_⟩ := corner c hc'; exact ⟨_,_,d1,d3⟩)
    (by
      obtain ⟨c,hc',d1,_,d3,_⟩ := strictCorner qa qam
      simp only [Quad.strictA,Bool.and_eq_true,Bool.not_eq_true'] at sa
      exact ⟨c,hc',_,_,d1,d3,sa.1,sa.2⟩)
  have fb := fam (C.next k) rx (!pos)
    (fun c hc' => by obtain ⟨q,_,_,d2,_,d4⟩ := corner c hc'; exact ⟨_,_,d2,d4⟩)
    (by
      obtain ⟨c,hc',_,d2,_,d4⟩ := strictCorner qb qbm
      simp only [Quad.strictB,Bool.and_eq_true,Bool.not_eq_true'] at sb
      exact ⟨c,hc',_,_,d2,d4,sb.1,sb.2⟩)
  have crossW : ArtGallery.det w z (gridPt X Y (C.node k))*ArtGallery.det w z (gridPt X Y (C.next k))<0 := by
    cases pos with
    | true => exact mul_neg_of_pos_of_neg (fa.1 rfl) (fb.2 rfl)
    | false => exact mul_neg_of_neg_of_pos (fa.2 rfl) (fb.1 rfl)
  -- the edge line separates the guard segment from the cell
  have hg₀ : g₀.1<X.length ∧ g₀.2<Y.length := by rw [G.lx,G.ly]; exact rg₀
  have hg₁ : g₁.1<X.length ∧ g₁.2<Y.length := by rw [G.lx,G.ly]; exact rg₁
  have s₀ := side_node G.hx G.hy nr xr hg₀ ax
  have s₁ := side_node G.hx G.hy nr xr hg₁ ax
  have sw := side_sound G.hx G.hy nr xr ax wx wy
  have dz : ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z=
      (1-t)*ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) (gridPt X Y g₀)+
        t*ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) (gridPt X Y g₁) := by
    rw [zt]; simp only [ArtGallery.det,Geometry.lerp]; ring
  have crossE : ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) w*
      ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z<0 := by
    rcases lt_or_gt_of_ne ne with n|n
    · have a0 := s₀.2 (by rw [o₀]; omega)
      have a1 := s₁.2 (by rw [o₁]; omega)
      have zp : 0<ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z := by
        rw [dz]
        rcases eq_or_lt_of_le t0 with e|e
        · subst e; simpa using a0
        · nlinarith [mul_pos e a1,mul_nonneg (show 0≤1-t by linarith) a0.le]
      exact mul_neg_of_neg_of_pos (sw.1 n) zp
    · have a0 := s₀.1 (by rw [o₀]; omega)
      have a1 := s₁.1 (by rw [o₁]; omega)
      have zn : ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z<0 := by
        rw [dz]
        rcases eq_or_lt_of_le t0 with e|e
        · subst e; simpa using a0
        · nlinarith [mul_pos e (neg_pos.mpr a1),mul_nonneg (show 0≤1-t by linarith) (neg_nonneg.mpr a0.le)]
      exact mul_neg_of_pos_of_neg (sw.2 n) zn
  rw [←node_vtx C X Y hk,←next_vtx C X Y hk] at crossE crossW
  exact Polygon.not_sees_of_proper_cross G.simple hk' crossE crossW (Polygon.sees_comm.mp sees)

theorem zipOne_mem {pos : Bool} {g₀ g₁ v : Index} :
    ∀ {ws : List Index} {qs : List (Sign × Sign)}, zipOne C pos g₀ g₁ v ws qs=true →
    ∀ i, i<qs.length → ∃ w q, ws[i]?=some w ∧ qs[i]?=some q ∧
      C.detSign pos w g₀ v q.1=true ∧ C.detSign pos w g₁ v q.2=true
  | [],[],_ => by intro i hi; simp at hi
  | [],_::_,h => by simp [zipOne] at h
  | _::_,[],h => by simp [zipOne] at h
  | w::ws,q::qs,h => by
    simp only [zipOne,Bool.and_eq_true] at h
    obtain ⟨⟨h1,h2⟩,rest⟩ := h
    intro i hi
    cases i with
    | zero => exact ⟨w,q,rfl,rfl,h1,h2⟩
    | succ i => simpa using zipOne_mem rest i (by simpa using hi)

theorem zipOne_cover {pos : Bool} {g₀ g₁ v : Index} :
    ∀ {ws : List Index} {qs : List (Sign × Sign)}, zipOne C pos g₀ g₁ v ws qs=true →
    ∀ w∈ws, ∃ i, i<qs.length ∧ ws[i]?=some w
  | [],[],_ => by simp
  | [],_::_,h => by simp [zipOne] at h
  | _::_,[],h => by simp [zipOne] at h
  | w::ws,q::qs,h => by
    simp only [zipOne,Bool.and_eq_true] at h
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact ⟨0,by simp,rfl⟩
    · obtain ⟨i,hi,e⟩ := zipOne_cover h.2 u hu
      exact ⟨i+1,by simpa using hi,by simpa using e⟩

/-- A proper crossing of edge `k` from one certified far end and a supplied near-end sign. -/
theorem crossOne_sound (G : Good C X Y s A) {g₀ g₁ : Index} {cell : Nat × Nat} {k : Nat} {pos first : Bool}
    {qs : List (Sign × Sign)} (h : crossOne C g₀ g₁ cell k pos first qs=true) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁)) {w : Point}
    (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2)
    (near : let u := gridPt X Y (if first then C.next k else C.node k)
      (pos=true → ArtGallery.det w z u<0) ∧ (pos=false → 0<ArtGallery.det w z u)) :
    ¬(C.poly X Y).Sees z w := by
  simp only [crossOne,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk,ne⟩,o₀⟩,o₁⟩,zipped⟩,⟨qa,qam,sa⟩⟩,⟨r₀x,r₀y,r₁x,r₁y⟩⟩,hc⟩ := h
  intro sees
  have nr := node_range G k hk
  have xr := next_range G k hk
  have ax := axis_next G.axis hk
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  have rg₀ : g₀.1<C.nx ∧ g₀.2<C.ny := ⟨r₀x,r₀y⟩
  have rg₁ : g₁.1<C.nx ∧ g₁.2<C.ny := ⟨r₁x,r₁y⟩
  have rn : (C.node k).1<C.nx ∧ (C.node k).2<C.ny := by rw [←G.lx,←G.ly]; exact nr
  have rx : (C.next k).1<C.nx ∧ (C.next k).2<C.ny := by rw [←G.lx,←G.ly]; exact xr
  have rv : (if first then C.node k else C.next k).1<C.nx ∧ (if first then C.node k else C.next k).2<C.ny := by
    cases first <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> assumption
  obtain ⟨t,t0,t1,zt⟩ := Geometry.mem_segment_iff_lerp.mp hz
  have cr := corner_range (C:=C) hc
  have real (c : Index) (hc' : c∈corners cell) (g : Index) (hg : g.1<C.nx ∧ g.2<C.ny) (v : Index)
      (hv : v.1<C.nx ∧ v.2<C.ny) (p : Bool) (sg : Sign) (d : C.detSign p c g v sg=true) :
      (p=true → 0≤ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)) ∧
      (p=false → ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)≤0) ∧
      (sg.isZero=false → (p=true → 0<ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)) ∧
        (p=false → ArtGallery.det (gridPt X Y c) (gridPt X Y g) (gridPt X Y v)<0)) := by
    have f := detSign_sound G (cr c hc') hg hv d
    cases hz' : sg.isZero
    · have := f.2 hz'
      exact ⟨fun e => (this.1 e).le,fun e => (this.2 e).le,fun _ => this⟩
    · have := f.1 hz'
      exact ⟨fun _ => this.ge,fun _ => this.le,fun e => by simp at e⟩
  let v := if first then C.node k else C.next k
  have corner (c : Index) (hc' : c∈corners cell) : ∃ q∈qs,
      C.detSign pos c g₀ v q.1=true ∧ C.detSign pos c g₁ v q.2=true := by
    obtain ⟨i,hi,e⟩ := zipOne_cover zipped c hc'
    obtain ⟨w',q,ew,eq,f1,f2⟩ := zipOne_mem zipped i hi
    rw [e] at ew; cases ew
    exact ⟨q,List.mem_of_getElem? eq,f1,f2⟩
  obtain ⟨c',hc'',d₀,d₁⟩ : ∃ c∈corners cell, C.detSign pos c g₀ v qa.1=true ∧ C.detSign pos c g₁ v qa.2=true := by
    obtain ⟨i,hi,e⟩ := List.getElem_of_mem qam
    obtain ⟨w',q',ew,eq,f1,f2⟩ := zipOne_mem zipped i hi
    rw [List.getElem?_eq_getElem hi,e] at eq; cases eq
    exact ⟨w',List.mem_of_getElem? ew,f1,f2⟩
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at sa
  have far : (pos=true → 0<ArtGallery.det w z (gridPt X Y v)) ∧ (pos=false → ArtGallery.det w z (gridPt X Y v)<0) := by
    rw [zt]
    cases pos with
    | true =>
      refine ⟨fun _ => along_cell G hc wx wy t0 t1 ?_ ⟨c',hc'',((real c' hc'' g₀ rg₀ v rv true _ d₀).2.2 sa.1).1 rfl,
        ((real c' hc'' g₁ rg₁ v rv true _ d₁).2.2 sa.2).1 rfl⟩,fun e => by simp at e⟩
      intro c hc'
      obtain ⟨q,_,e₀,e₁⟩ := corner c hc'
      exact ⟨(real c hc' g₀ rg₀ v rv true _ e₀).1 rfl,(real c hc' g₁ rg₁ v rv true _ e₁).1 rfl⟩
    | false =>
      refine ⟨fun e => by simp at e,fun _ => along_cell_neg G hc wx wy t0 t1 ?_
        ⟨c',hc'',((real c' hc'' g₀ rg₀ v rv false _ d₀).2.2 sa.1).2 rfl,((real c' hc'' g₁ rg₁ v rv false _ d₁).2.2 sa.2).2 rfl⟩⟩
      intro c hc'
      obtain ⟨q,_,e₀,e₁⟩ := corner c hc'
      exact ⟨(real c hc' g₀ rg₀ v rv false _ e₀).2.1 rfl,(real c hc' g₁ rg₁ v rv false _ e₁).2.1 rfl⟩
  have crossW : ArtGallery.det w z (gridPt X Y (C.node k))*ArtGallery.det w z (gridPt X Y (C.next k))<0 := by
    cases first <;> cases pos <;> simp only [v,Bool.false_eq_true,ite_true,ite_false] at far near
    · exact mul_neg_of_pos_of_neg (near.2 trivial) (far.2 trivial)
    · exact mul_neg_of_neg_of_pos (near.1 trivial) (far.1 trivial)
    · exact mul_neg_of_neg_of_pos (far.2 trivial) (near.2 trivial)
    · exact mul_neg_of_pos_of_neg (far.1 trivial) (near.1 trivial)
  have hg₀ : g₀.1<X.length ∧ g₀.2<Y.length := by rw [G.lx,G.ly]; exact rg₀
  have hg₁ : g₁.1<X.length ∧ g₁.2<Y.length := by rw [G.lx,G.ly]; exact rg₁
  have s₀ := side_node G.hx G.hy nr xr hg₀ ax
  have s₁ := side_node G.hx G.hy nr xr hg₁ ax
  have sw := side_sound G.hx G.hy nr xr ax wx wy
  have dz : ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z=
      (1-t)*ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) (gridPt X Y g₀)+
        t*ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) (gridPt X Y g₁) := by
    rw [zt]; simp only [ArtGallery.det,Geometry.lerp]; ring
  have crossE : ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) w*
      ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z<0 := by
    rcases lt_or_gt_of_ne ne with n|n
    · have a0 := s₀.2 (by rw [o₀]; omega)
      have a1 := s₁.2 (by rw [o₁]; omega)
      have zp : 0<ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z := by
        rw [dz]
        rcases eq_or_lt_of_le t0 with e|e
        · subst e; simpa using a0
        · nlinarith [mul_pos e a1,mul_nonneg (show 0≤1-t by linarith) a0.le]
      exact mul_neg_of_neg_of_pos (sw.1 n) zp
    · have a0 := s₀.1 (by rw [o₀]; omega)
      have a1 := s₁.1 (by rw [o₁]; omega)
      have zn : ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z<0 := by
        rw [dz]
        rcases eq_or_lt_of_le t0 with e|e
        · subst e; simpa using a0
        · nlinarith [mul_pos e (neg_pos.mpr a1),mul_nonneg (show 0≤1-t by linarith) (neg_nonneg.mpr a0.le)]
      exact mul_neg_of_pos_of_neg (sw.2 n) zn
  rw [←node_vtx C X Y hk,←next_vtx C X Y hk] at crossE crossW
  exact Polygon.not_sees_of_proper_cross G.simple hk' crossE crossW (Polygon.sees_comm.mp sees)

private theorem strict_param (G : Good C X Y s A) {a b g : Index} (ha : a.1<C.nx ∧ a.2<C.ny)
    (hb : b.1<C.nx ∧ b.2<C.ny) (h : strictIn a b g=true) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ gridPt X Y g=Geometry.lerp (gridPt X Y a) (gridPt X Y b) t := by
  have ha' : a.1<X.length ∧ a.2<Y.length := by rw [G.lx,G.ly]; exact ha
  have hb' : b.1<X.length ∧ b.2<Y.length := by rw [G.lx,G.ly]; exact hb
  simp only [strictIn,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  have between (xs : List ℝ) (hx : xs.IsChain (·<·)) {u v w : Nat} (hu : u<xs.length) (hv : v<xs.length)
      (st : strictly u v w=true) : ∃ t : ℝ, 0<t ∧ t<1 ∧ xs.getD u 0+t*(xs.getD v 0-xs.getD u 0)=xs.getD w 0 := by
    simp only [strictly,decide_eq_true_eq] at st
    have r : (xs.getD u 0<xs.getD w 0 ∧ xs.getD w 0<xs.getD v 0) ∨ (xs.getD v 0<xs.getD w 0 ∧ xs.getD w 0<xs.getD u 0) := by
      rcases st with ⟨p,q⟩|⟨p,q⟩
      · exact Or.inl ⟨level_lt hx (by omega) p,level_lt hx hv q⟩
      · exact Or.inr ⟨level_lt hx (by omega) p,level_lt hx hu q⟩
    have ne : xs.getD v 0-xs.getD u 0≠0 := by rcases r with ⟨p,q⟩|⟨p,q⟩ <;> intro e <;> linarith
    refine ⟨(xs.getD w 0-xs.getD u 0)/(xs.getD v 0-xs.getD u 0),?_,?_,by field_simp; ring⟩
    · rcases r with ⟨p,q⟩|⟨p,q⟩
      · exact div_pos (by linarith) (by linarith)
      · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · rcases r with ⟨p,q⟩|⟨p,q⟩
      · exact (div_lt_one (by linarith)).mpr (by linarith)
      · exact (div_lt_one_of_neg (by linarith)).mpr (by linarith)
  rcases h with ⟨⟨e1,e2⟩,st⟩|⟨⟨e1,e2⟩,st⟩
  · obtain ⟨t,t0,t1,ht⟩ := between Y G.hy ha'.2 hb'.2 st
    refine ⟨t,t0,t1,?_⟩
    simp only [Geometry.lerp,gridPt,e1,e2,sub_self,mul_zero,add_zero,ht]
  · obtain ⟨t,t0,t1,ht⟩ := between X G.hx ha'.1 hb'.1 st
    refine ⟨t,t0,t1,?_⟩
    simp only [Geometry.lerp,gridPt,e1,e2,sub_self,mul_zero,add_zero,ht]

theorem half_sound (G : Good C X Y s A) {g₀ g₁ : Index} {cell : Nat × Nat} {k : Nat}
    (h : half C g₀ g₁ cell k=true) (hc : Inner C.nx cell.1 ∧ Inner C.ny cell.2) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁)) {w : Point}
    (wx : atom w.1 X=cell.1) (wy : atom w.2 Y=cell.2) : ¬(C.poly X Y).Sees z w := by
  simp only [half,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk,s₀⟩,s₁⟩,out⟩ := h
  intro sees
  have nr := node_range G k hk
  have xr := next_range G k hk
  have rn : (C.node k).1<C.nx ∧ (C.node k).2<C.ny := by rw [←G.lx,←G.ly]; exact nr
  have rx : (C.next k).1<C.nx ∧ (C.next k).2<C.ny := by rw [←G.lx,←G.ly]; exact xr
  obtain ⟨t₀,a0,a1,e0⟩ := strict_param G rn rx s₀
  obtain ⟨t₁,b0,b1,e1⟩ := strict_param G rn rx s₁
  obtain ⟨μ,μ0,μ1,zt⟩ := Geometry.mem_segment_iff_lerp.mp hz
  -- the guard lies strictly inside the edge
  have param : z=Geometry.lerp (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) ((1-μ)*t₀+μ*t₁) := by
    rw [zt,e0,e1]; simp only [Geometry.lerp]; ext <;> simp <;> ring
  have p0 : 0<(1-μ)*t₀+μ*t₁ := by
    rcases eq_or_lt_of_le μ0 with h|h
    · subst h; simpa using a0
    · nlinarith [mul_pos h b0,mul_nonneg (show 0≤1-μ by linarith) a0.le]
  have p1 : (1-μ)*t₀+μ*t₁<1 := by
    rcases eq_or_lt_of_le μ0 with h|h
    · subst h; simpa using a1
    · nlinarith [mul_lt_mul_of_pos_left b1 h,mul_le_mul_of_nonneg_left a1.le (show 0≤1-μ by linarith)]
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  rw [param] at sees
  have d := Polygon.sees_edge_point G.simple G.left hk' (node_vtx C X Y hk) (next_vtx C X Y hk) p0 p1 sees
  have := (side_sound G.hx G.hy nr xr (axis_next G.axis hk) wx wy).1 out
  linarith

end Sound

end ArtGallery.Orthogonal.BoundaryPoint.CellCert
end
