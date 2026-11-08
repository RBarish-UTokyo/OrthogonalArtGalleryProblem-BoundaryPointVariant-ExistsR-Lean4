module

public import ArtGallery.Orthogonal.BoundaryPoint.SepGeom
public import ArtGallery.Orthogonal.BoundaryPoint.RegisterPoly
public import ArtGallery.Orthogonal.BoundaryPoint.ZSign
public import ArtGallery.Geometry.Det

/-! # Certified exclusions of a witness from a boundary cell

A chart is a cycle of grid nodes over two strictly increasing real axes whose
levels are register forms. An exclusion certifies that no point of one boundary
cell (atom-code pair) sees a given grid-node witness:

* `cone k out`: the witness is the convex cycle vertex `k` and the cell lies
  strictly outside the half-plane of its incoming or outgoing edge;
* `half k`: the witness lies inside the open cycle edge `k` and the cell lies
  strictly outside that edge's half-plane;
* `atom c`: witness and cell lie on one grid line and the open grid atom `c`
  strictly between them belongs to no tile, hence is exterior;
* `cross k pos ss`: every segment from the witness to a point of the cell
  properly crosses cycle edge `k`. The edge-side tests are index tests; the four
  witness-side determinant signs at the two end nodes of the cell are certified
  by `RegisterPoly` or `RegisterProduct` for every admissible parameter.

All tests are boolean. Soundness needs only the strictly increasing axes, the
form values of the levels with their register bounds, simplicity, interior on
the left, and the region as a union of tiles. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SepCert
open Set GridAtom GridParity RoomGrid SpanCells SepGeom RegisterForm MarginCert ArtGallery.Orthogonal.Hard

/-- A certified strict sign of a determinant. -/
inductive Sign
  | poly (k : Nat)
  | prod (h : RegisterProduct.Hint)
  | zero
  /-- Product comparison on the integer copy, from base `0`, `1` or `2` (`ZSign.prodOK`). -/
  | zprod (base : Nat) (h : RegisterProduct.Hint)
  /-- Expanded determinant on the integer copy (`ZSign.polyOK`). -/
  | zpoly (k : Nat)
  /-- Identically vanishing determinant on the integer copy (`ZSign.zeroOK`). -/
  | zzero
  /-- Product checks from all bases, then the expanded determinant, without hints (`ZSign.autoOK`). -/
  | zauto
  /-- `zprod base h` with the rotated points given as literal line indices (`ZSign.prodL`). -/
  | zlit (base : Nat) (h : RegisterProduct.Hint) (i0 j0 i1 j1 i2 j2 : Nat)

def Sign.isZero : Sign → Bool
  | .zero => true
  | .zzero => true
  | _ => false

inductive Excl
  | cone (k : Nat) (out : Bool)
  | half (k : Nat)
  | atom (c : Nat)
  | cross (k : Nat) (pos : Bool) (s₀ s₁ s₂ s₃ : Sign)

/-- The boolean data of a chart. -/
structure Chart where
  nx : Nat
  ny : Nat
  cyc : List Index
  tiles : List (CorridorProgram.Rect Nat)
  fx : List Form
  fy : List Form
  B : Nat → Box
  /-- The integer copy of the forms and boxes (`ZSign.ZData.ofChart`). -/
  z : ZSign.ZData

def Chart.n (C : Chart) := C.cyc.length
def Chart.node (C : Chart) (k : Nat) : Index := C.cyc.getD (k%C.n) (0,0)
def Chart.prev (C : Chart) (k : Nat) : Index := C.cyc.getD ((k+C.n-1)%C.n) (0,0)
def Chart.next (C : Chart) (k : Nat) : Index := C.cyc.getD ((k+1)%C.n) (0,0)

/-- Strictly between two natural numbers. -/
def strictly (u v z : Nat) : Bool := decide ((u<z ∧ z<v) ∨ (v<z ∧ z<u))

/-- Is `det w g c > 0`, with grid nodes `w c` and a node `g`, certified? -/
def Chart.detPos (C : Chart) (w g c : Index) : Sign → Bool
  | .poly k => RegisterForm.positive (RegisterPoly.B2 C.B)
      (RegisterPoly.det (C.fx.getD w.1 []) (C.fy.getD w.2 []) (C.fx.getD g.1 []) (C.fy.getD g.2 [])
        (C.fx.getD c.1 []) (C.fy.getD c.2 [])) k
  | .prod h => RegisterProduct.check C.B (diff (C.fx.getD g.1 []) (C.fx.getD w.1 []))
      (diff (C.fy.getD c.2 []) (C.fy.getD w.2 [])) (diff (C.fy.getD g.2 []) (C.fy.getD w.2 []))
      (diff (C.fx.getD c.1 []) (C.fx.getD w.1 [])) h
  | .zero => false
  | .zprod b h => C.z.ok && ZSign.prodOK C.z w g c b h
  | .zpoly k => C.z.ok && ZSign.polyOK C.z w g c k
  | .zzero => false
  | .zauto => C.z.ok && ZSign.autoOK C.z w g c
  | .zlit b h i0 j0 i1 j1 i2 j2 => C.z.ok && decide (ZSign.rot w g c b=((i0,j0),(i1,j1),(i2,j2))) &&
      ZSign.prodL C.z i0 j0 i1 j1 i2 j2 h

/-- The expanded determinant form of three grid nodes. -/
def Chart.detForm (C : Chart) (w g c : Index) : Form :=
  RegisterPoly.det (C.fx.getD w.1 []) (C.fy.getD w.2 []) (C.fx.getD g.1 []) (C.fy.getD g.2 [])
    (C.fx.getD c.1 []) (C.fy.getD c.2 [])

/-- Certified sign `det w g c > 0` (`pos`) or `< 0`, or an identically vanishing determinant. -/
def Chart.detSign (C : Chart) (pos : Bool) (w g c : Index) : Sign → Bool
  | .zero => (C.detForm w g c).isEmpty
  | .zzero => C.z.ok && ZSign.zeroOK C.z w g c
  | s => if pos then C.detPos w g c s else C.detPos w c g s

def Chart.ok (C : Chart) (w : Index) (cell : Nat × Nat) : Excl → Bool
  | .cone k out => decide (k<C.n) && decide (C.node k=w) &&
      decide (0<sideNode (C.prev k) (C.node k) (C.next k)) &&
      (if out then decide (side (C.node k) (C.next k) cell<0) else decide (side (C.prev k) (C.node k) cell<0))
  | .half k =>
      let a := C.node k
      let b := C.next k
      decide (k<C.n) &&
      ((decide (a.1=w.1 ∧ b.1=w.1) && strictly a.2 b.2 w.2) || (decide (a.2=w.2 ∧ b.2=w.2) && strictly a.1 b.1 w.1)) &&
      decide (side a b cell<0)
  | .atom c => decide (c%2=0) && C.tiles.all (fun r => !(if cell.2=line w.2 then inBox c (line w.2) r else inBox (line w.1) c r)) &&
      ((decide (cell.2=line w.2) && strictly (line w.1) cell.1 c) || (decide (cell.1=line w.1) && strictly (line w.2) cell.2 c))
  | .cross k pos s₀ s₁ s₂ s₃ =>
      let a := C.node k
      let b := C.next k
      let g₀ : Index := (lo cell.1,lo cell.2)
      let g₁ : Index := (hi cell.1,hi cell.2)
      decide (k<C.n) && decide (sideNode a b w≠0) && decide (side a b cell= -sideNode a b w) &&
      C.detSign pos w g₀ a s₀ && C.detSign (!pos) w g₀ b s₁ &&
      C.detSign pos w g₁ a s₂ && C.detSign (!pos) w g₁ b s₃ &&
      !(s₀.isZero && s₂.isZero) && !(s₁.isZero && s₃.isZero) &&
      (!(s₀.isZero || s₁.isZero || s₂.isZero || s₃.isZero) || decide (cell.1%2=0 ∨ cell.2%2=0))

/-! ## Soundness -/

/-- The real chart polygon. -/
def Chart.poly (C : Chart) (X Y : List ℝ) : Polygon := ⟨C.cyc.map (gridPt X Y)⟩

structure Good (C : Chart) (X Y : List ℝ) (s : ℚ) (A : Nat → ℚ) : Prop where
  hx : X.IsChain (·<·)
  hy : Y.IsChain (·<·)
  lx : X.length=C.nx
  ly : Y.length=C.ny
  vx : ∀ i<C.nx, X.getD i 0=((value s A (C.fx.getD i []):ℚ):ℝ)
  vy : ∀ i<C.ny, Y.getD i 0=((value s A (C.fy.getD i []):ℚ):ℝ)
  bounds : Bounds C.B A
  pos : 0<s
  small : s≤cap
  verts : ∀ p∈C.cyc, p.1<C.nx ∧ p.2<C.ny
  axis : cyclicAxis C.cyc
  simple : (C.poly X Y).Simple
  left : (C.poly X Y).InteriorLeft
  fill : (C.poly X Y).filled=cellsR X Y C.tiles
  tileIdx : ∀ r∈C.tiles, r.1<C.nx ∧ r.2.1<C.nx ∧ r.2.2.1<C.ny ∧ r.2.2.2<C.ny
  cells : ∀ e∈cellsOf C.cyc, Inner C.nx e.1 ∧ Inner C.ny e.2 ∧ (e.1%2=1 ∨ e.2%2=1)
  zval : C.z.ok=true → (∀ i, ZSign.valueZ s A (C.z.X i)=C.z.dx*value s A (C.fx.getD i [])) ∧
    (∀ i, ZSign.valueZ s A (C.z.Y i)=C.z.dy*value s A (C.fy.getD i []))
  zb : ZSign.ZBounds C.z A
  zpos : 0<C.z.dx ∧ 0<C.z.dy ∧ 0<C.z.db

section Sound
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

theorem poly_n (C : Chart) (X Y : List ℝ) : (C.poly X Y).n=C.n := by
  simp [Chart.poly,Polygon.n,Chart.n]

theorem vtx_eq (C : Chart) (X Y : List ℝ) {i : Nat} (hi : i<C.n) :
    (C.poly X Y).vtx i=gridPt X Y (C.cyc.getD i (0,0)) := by
  have hi' : i<C.cyc.length := hi
  simp only [Chart.poly,Polygon.vtx]
  rw [List.getD_eq_getElem _ _ (by simpa using hi'),List.getD_eq_getElem _ _ hi',List.getElem_map]

theorem node_mem (C : Chart) {i : Nat} (hi : i<C.n) : C.cyc.getD i (0,0)∈C.cyc := by
  have hi' : i<C.cyc.length := hi
  rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'

theorem n_pos {C : Chart} {k : Nat} (hk : k<C.n) : 0<C.n := by omega

theorem node_vtx (C : Chart) (X Y : List ℝ) {k : Nat} (hk : k<C.n) :
    (C.poly X Y).vtx k=gridPt X Y (C.node k) := by
  rw [vtx_eq C X Y hk,Chart.node,Nat.mod_eq_of_lt hk]

theorem next_vtx (C : Chart) (X Y : List ℝ) {k : Nat} (hk : k<C.n) :
    (C.poly X Y).vtx ((k+1)%(C.poly X Y).n)=gridPt X Y (C.next k) := by
  rw [poly_n,vtx_eq C X Y (Nat.mod_lt _ (n_pos hk)),Chart.next]

theorem prev_vtx (C : Chart) (X Y : List ℝ) {k : Nat} (hk : k<C.n) :
    (C.poly X Y).vtx ((k+(C.poly X Y).n-1)%(C.poly X Y).n)=gridPt X Y (C.prev k) := by
  rw [poly_n,vtx_eq C X Y (Nat.mod_lt _ (n_pos hk)),Chart.prev]

/-- Consecutive cycle nodes share a grid line. -/
theorem axis_next (h : cyclicAxis C.cyc) {k : Nat} (hk : k<C.n) :
    (C.node k).1=(C.next k).1 ∨ (C.node k).2=(C.next k).2 := by
  have hk' : k<C.cyc.length := hk
  have m : (k+1)%C.cyc.length<C.cyc.length := Nat.mod_lt _ (by omega)
  have := h ⟨k,hk'⟩
  simp only [Chart.node,Chart.next,Nat.mod_eq_of_lt hk',Chart.n] at this ⊢
  rw [List.getD_eq_getElem _ _ hk',List.getD_eq_getElem _ _ m]
  exact this

theorem axis_prev (h : cyclicAxis C.cyc) {k : Nat} (hk : k<C.n) :
    (C.prev k).1=(C.node k).1 ∨ (C.prev k).2=(C.node k).2 := by
  have pos := n_pos hk
  let j := (k+C.n-1)%C.n
  have hj : j<C.n := Nat.mod_lt _ pos
  have e := axis_next h hj
  have nx : C.next j=C.node k := by
    simp only [Chart.next,Chart.node,j]
    congr 1
    rw [Nat.mod_add_mod,Nat.mod_eq_of_lt hk]
    have : k+C.n-1+1=k+C.n := by omega
    rw [this,Nat.add_mod_right,Nat.mod_eq_of_lt hk]
  have pv : C.node j=C.prev k := by simp only [Chart.node,Chart.prev,j,Nat.mod_mod]
  rw [←nx,←pv]; exact e

theorem node_range (G : Good C X Y s A) (k : Nat) (hk : k<C.n) :
    (C.node k).1<X.length ∧ (C.node k).2<Y.length := by
  have := G.verts _ (node_mem C (Nat.mod_lt k (n_pos hk)))
  rw [G.lx,G.ly]; exact this

theorem next_range (G : Good C X Y s A) (k : Nat) (hk : k<C.n) :
    (C.next k).1<X.length ∧ (C.next k).2<Y.length := by
  have := G.verts _ (node_mem C (Nat.mod_lt (k+1) (n_pos hk)))
  rw [G.lx,G.ly]; exact this

theorem prev_range (G : Good C X Y s A) (k : Nat) (hk : k<C.n) :
    (C.prev k).1<X.length ∧ (C.prev k).2<Y.length := by
  have := G.verts _ (node_mem C (Nat.mod_lt (k+C.n-1) (n_pos hk)))
  rw [G.lx,G.ly]; exact this

theorem cone_sound (G : Good C X Y s A) {w : Index} {cell : Nat × Nat} {k : Nat} {out : Bool}
    (h : C.ok w cell (.cone k out)=true) {z : Point} (zx : atom z.1 X=cell.1) (zy : atom z.2 Y=cell.2) :
    ¬(C.poly X Y).Sees z (gridPt X Y w) := by
  simp only [Chart.ok,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk,hn⟩,hc⟩,hs⟩ := h
  intro sees
  rw [←hn] at sees
  have pr := prev_range G k hk
  have nr := node_range G k hk
  have xr := next_range G k hk
  have conv := (side_node G.hx G.hy pr nr xr (axis_prev G.axis hk)).2 hc
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  have cone := Polygon.sees_subset_cone' G.simple G.left hk' (prev_vtx C X Y hk) (node_vtx C X Y hk)
    (next_vtx C X Y hk) conv sees
  cases out with
  | false =>
    have hs' : side (C.prev k) (C.node k) cell<0 := by simpa using hs
    have := (side_sound G.hx G.hy pr nr (axis_prev G.axis hk) zx zy).1 hs'
    linarith [cone.1]
  | true =>
    have hs' : side (C.node k) (C.next k) cell<0 := by simpa using hs
    have := (side_sound G.hx G.hy nr xr (axis_next G.axis hk) zx zy).1 hs'
    linarith [cone.2]

private theorem between_param {u v w : ℝ} (h : (u<w ∧ w<v) ∨ (v<w ∧ w<u)) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ u+t*(v-u)=w := by
  have ne : v-u≠0 := by rcases h with ⟨a,b⟩|⟨a,b⟩ <;> intro e <;> linarith
  refine ⟨(w-u)/(v-u),?_,?_,by field_simp; ring⟩
  · rcases h with ⟨a,b⟩|⟨a,b⟩
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · rcases h with ⟨a,b⟩|⟨a,b⟩
    · exact (div_lt_one (by linarith)).mpr (by linarith)
    · exact (div_lt_one_of_neg (by linarith)).mpr (by linarith)

private theorem strictly_real {xs : List ℝ} (hx : xs.IsChain (·<·)) {a b w : Nat}
    (ha : a<xs.length) (hb : b<xs.length) (h : strictly a b w=true) :
    (xs.getD a 0<xs.getD w 0 ∧ xs.getD w 0<xs.getD b 0) ∨ (xs.getD b 0<xs.getD w 0 ∧ xs.getD w 0<xs.getD a 0) := by
  simp only [strictly,decide_eq_true_eq] at h
  rcases h with ⟨p,q⟩|⟨p,q⟩
  · exact Or.inl ⟨level_lt hx (by omega) p,level_lt hx hb q⟩
  · exact Or.inr ⟨level_lt hx (by omega) p,level_lt hx ha q⟩

theorem half_sound (G : Good C X Y s A) {w : Index} {cell : Nat × Nat} {k : Nat}
    (h : C.ok w cell (.half k)=true) {z : Point} (zx : atom z.1 X=cell.1) (zy : atom z.2 Y=cell.2) :
    ¬(C.poly X Y).Sees z (gridPt X Y w) := by
  simp only [Chart.ok,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hk,hl⟩,hs⟩ := h
  intro sees
  have nr := node_range G k hk
  have xr := next_range G k hk
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  have param : ∃ t : ℝ, 0<t ∧ t<1 ∧ gridPt X Y w=Geometry.lerp (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) t := by
    rcases hl with ⟨⟨e1,e2⟩,st⟩|⟨⟨e1,e2⟩,st⟩
    · obtain ⟨t,t0,t1,ht⟩ := between_param (strictly_real G.hy nr.2 xr.2 st)
      refine ⟨t,t0,t1,?_⟩
      simp only [Geometry.lerp,gridPt,e1,e2,sub_self,mul_zero,add_zero,ht]
    · obtain ⟨t,t0,t1,ht⟩ := between_param (strictly_real G.hx nr.1 xr.1 st)
      refine ⟨t,t0,t1,?_⟩
      simp only [Geometry.lerp,gridPt,e1,e2,sub_self,mul_zero,add_zero,ht]
  obtain ⟨t,t0,t1,ht⟩ := param
  rw [ht] at sees
  have d := Polygon.sees_edge_point G.simple G.left hk' (node_vtx C X Y hk) (next_vtx C X Y hk) t0 t1
    (Polygon.sees_comm.mp sees)
  have := (side_sound G.hx G.hy nr xr (axis_next G.axis hk) zx zy).1 hs
  linarith

/-- The midpoint of an open grid interval has that interval's atom code. -/
private theorem mid_atom {xs : List ℝ} (hx : xs.IsChain (·<·)) {m : Nat} (hm : m+1<xs.length) :
    let q := (xs.getD m 0+xs.getD (m+1) 0)/2
    xs.getD m 0<q ∧ q<xs.getD (m+1) 0 ∧ atom q xs=2*m+2 := by
  have lt := level_lt hx hm (Nat.lt_succ_self m)
  dsimp only
  refine ⟨by linarith,by linarith,?_⟩
  have up := (compare_line hx hm ((xs.getD m 0+xs.getD (m+1) 0)/2)).1.mp (by linarith)
  have low : ¬((xs.getD m 0+xs.getD (m+1) 0)/2≤xs.getD m 0) := by intro h; linarith
  rw [le_line hx (by omega)] at low
  unfold line at up low; omega

/-- A coordinate on the far side of a grid line, read from its atom code. -/
private theorem past {xs : List ℝ} (hx : xs.IsChain (·<·)) {i c : Nat} (hi : i<xs.length) {z : ℝ}
    (hz : atom z xs=c) : (line i≤c → xs.getD i 0≤z) ∧ (c≤line i → z≤xs.getD i 0) :=
  ⟨fun h => (line_le hx hi z).mpr (hz ▸ h),fun h => (le_line hx hi z).mpr (hz ▸ h)⟩

private theorem mono_le {xs : List ℝ} (hx : xs.IsChain (·<·)) {i j : Nat} (hj : j<xs.length) (h : i≤j) :
    xs.getD i 0≤xs.getD j 0 := by
  rcases Nat.lt_or_ge i j with lt|ge
  · exact (level_lt hx hj lt).le
  · rw [show i=j by omega]

/-- A collinear exterior atom between the witness and the cell (one axis, generic). -/
private theorem exterior_between {xs : List ℝ} (hx : xs.IsChain (·<·)) {w c d : Nat} {zc : ℝ}
    (hw : w<xs.length) (hd : hi d<xs.length) (hz : atom zc xs=d) (ev : c%2=0)
    (st : strictly (line w) d c=true) :
    ∃ m, m+1<xs.length ∧ c=2*m+2 ∧
      let q := (xs.getD m 0+xs.getD (m+1) 0)/2
      Between zc (xs.getD w 0) q := by
  simp only [strictly,decide_eq_true_eq] at st
  refine ⟨c/2-1,?_,by unfold line at st; omega,?_⟩
  · unfold line hi at *; omega
  · have hm : c/2-1+1<xs.length := by unfold line hi at *; omega
    obtain ⟨a,b,_⟩ := mid_atom hx hm
    dsimp only at a b ⊢
    rcases st with ⟨p,q⟩|⟨p,q⟩
    · right
      constructor
      · exact (mono_le hx (by omega) (by unfold line at p; omega)).trans a.le
      · exact b.le.trans ((past hx hm hz).1 (by unfold line; omega))
    · left
      constructor
      · exact ((past hx (by omega) hz).2 (by unfold line; omega)).trans a.le
      · exact b.le.trans (mono_le hx hw (by unfold line at q; omega))

theorem atom_sound (G : Good C X Y s A) {w : Index} {cell : Nat × Nat} {c : Nat}
    (hw : w.1<C.nx ∧ w.2<C.ny) (hcell : Inner C.nx cell.1 ∧ Inner C.ny cell.2)
    (h : C.ok w cell (.atom c)=true) {z : Point} (zx : atom z.1 X=cell.1) (zy : atom z.2 Y=cell.2) :
    ¬(C.poly X Y).Sees z (gridPt X Y w) := by
  simp only [Chart.ok,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,List.all_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨ev,tiles⟩,ax⟩ := h
  have wx : w.1<X.length := G.lx ▸ hw.1
  have wy : w.2<Y.length := G.ly ▸ hw.2
  have cx : hi cell.1<X.length := G.lx ▸ hcell.1.2
  have cy : hi cell.2<Y.length := G.ly ▸ hcell.2.2
  have hR : ∀ r∈C.tiles, r.1<X.length ∧ r.2.1<X.length ∧ r.2.2.1<Y.length ∧ r.2.2.2<Y.length := by
    intro r hr; rw [G.lx,G.ly]; exact G.tileIdx r hr
  intro sees
  rcases ax with ⟨e,st⟩|⟨e,st⟩
  · -- horizontal common line
    obtain ⟨m,hm,rfl,btw⟩ := exterior_between G.hx wx cx zx ev st
    obtain ⟨_,_,am⟩ := mid_atom G.hx hm
    let q : Point := ((X.getD m 0+X.getD (m+1) 0)/2,Y.getD w.2 0)
    have zl : z.2=Y.getD w.2 0 := by
      have hc2 : Inner Y.length cell.2 := by rw [G.ly]; exact hcell.2
      have := on_line G.hy hc2 (by rw [e]; unfold line; omega) zy
      rwa [e,show lo (line w.2)=w.2 by unfold lo line; omega] at this
    have inSeg : q∈ArtGallery.segment z (gridPt X Y w) := by
      apply (segment_box (Or.inr zl)).mpr
      exact ⟨btw,Or.inl ⟨le_of_eq zl,le_refl _⟩⟩
    have inside := G.fill ▸ sees inSeg
    have any := (cells_iff G.hx G.hy hR q).mp inside
    obtain ⟨r,hr,hb⟩ := List.any_eq_true.mp any
    have no := tiles r hr
    simp only [e,ite_true] at no
    rw [am,atom_level G.hy wy] at hb
    rw [hb] at no; exact absurd no (by decide)
  · -- vertical common line
    obtain ⟨m,hm,rfl,btw⟩ := exterior_between G.hy wy cy zy ev st
    obtain ⟨_,_,am⟩ := mid_atom G.hy hm
    let q : Point := (X.getD w.1 0,(Y.getD m 0+Y.getD (m+1) 0)/2)
    have zl : z.1=X.getD w.1 0 := by
      have hc1 : Inner X.length cell.1 := by rw [G.lx]; exact hcell.1
      have := on_line G.hx hc1 (by rw [e]; unfold line; omega) zx
      rwa [e,show lo (line w.1)=w.1 by unfold lo line; omega] at this
    have inSeg : q∈ArtGallery.segment z (gridPt X Y w) := by
      apply (segment_box (Or.inl zl)).mpr
      exact ⟨Or.inl ⟨le_of_eq zl,le_refl _⟩,btw⟩
    have inside := G.fill ▸ sees inSeg
    have any := (cells_iff G.hx G.hy hR q).mp inside
    obtain ⟨r,hr,hb⟩ := List.any_eq_true.mp any
    have no := tiles r hr
    by_cases e2 : cell.2=line w.2
    · -- the cell is the witness node itself on both lines: no atom strictly between
      simp only [strictly,decide_eq_true_eq] at st
      rw [e2] at st; omega
    · simp only [e2,ite_false] at no
      rw [atom_level G.hx wx,am] at hb
      rw [hb] at no; exact absurd no (by decide)

theorem det_real (G : Good C X Y s A) {w g c : Index}
    (hw : w.1<C.nx ∧ w.2<C.ny) (hg : g.1<C.nx ∧ g.2<C.ny) (hc : c.1<C.nx ∧ c.2<C.ny) :
    ArtGallery.det (gridPt X Y w) (gridPt X Y g) (gridPt X Y c)=
      (((value s A (C.fx.getD g.1 [])-value s A (C.fx.getD w.1 []))*(value s A (C.fy.getD c.2 [])-value s A (C.fy.getD w.2 []))-
        (value s A (C.fy.getD g.2 [])-value s A (C.fy.getD w.2 []))*(value s A (C.fx.getD c.1 [])-value s A (C.fx.getD w.1 [])):ℚ):ℝ) := by
  simp only [ArtGallery.det,gridPt,G.vx _ hw.1,G.vx _ hg.1,G.vx _ hc.1,G.vy _ hw.2,G.vy _ hg.2,G.vy _ hc.2]
  push_cast; ring

/-- The integer determinant is the rational one scaled by `dx * dy`. -/
theorem dz_eq (G : Good C X Y s A) (hok : C.z.ok=true) (w g c : Index) :
    ZSign.DZ C.z s A w g c=C.z.dx*C.z.dy*
      ((value s A (C.fx.getD g.1 [])-value s A (C.fx.getD w.1 []))*(value s A (C.fy.getD c.2 [])-value s A (C.fy.getD w.2 []))-
        (value s A (C.fy.getD g.2 [])-value s A (C.fy.getD w.2 []))*(value s A (C.fx.getD c.1 [])-value s A (C.fx.getD w.1 []))) := by
  obtain ⟨vx,vy⟩ := G.zval hok
  simp only [ZSign.DZ,vx,vy]; ring

private theorem small' (G : Good C X Y s A) : s≤1/65 := by simpa [cap] using G.small

theorem detPos_sound (G : Good C X Y s A) {w g c : Index} {sg : Sign}
    (hw : w.1<C.nx ∧ w.2<C.ny) (hg : g.1<C.nx ∧ g.2<C.ny) (hc : c.1<C.nx ∧ c.2<C.ny)
    (h : C.detPos w g c sg=true) :
    0<ArtGallery.det (gridPt X Y w) (gridPt X Y g) (gridPt X Y c) := by
  rw [det_real G hw hg hc]
  apply Rat.cast_pos.mpr
  cases sg with
  | poly k =>
    have := RegisterPoly.positive G.bounds G.pos G.small h
    rwa [RegisterPoly.det_value] at this
  | prod hh =>
    have := RegisterProduct.compare G.bounds G.pos G.small hh h
    simp only [diff_value] at this
    linarith
  | zero => simp [Chart.detPos] at h
  | zprod b hh =>
    simp only [Chart.detPos,Bool.and_eq_true] at h
    have := ZSign.prodOK_sound G.zb G.zpos.2.2 G.pos (small' G) h.2
    rw [dz_eq G h.1] at this
    have dxy : (0:ℚ)<C.z.dx*C.z.dy := by
      have := G.zpos; exact mul_pos (by exact_mod_cast this.1) (by exact_mod_cast this.2.1)
    exact (mul_pos_iff_of_pos_left dxy).mp this
  | zpoly k =>
    simp only [Chart.detPos,Bool.and_eq_true] at h
    have := ZSign.polyOK_sound G.zb G.zpos.2.2 G.pos (small' G) h.2
    rw [dz_eq G h.1] at this
    have dxy : (0:ℚ)<C.z.dx*C.z.dy := by
      have := G.zpos; exact mul_pos (by exact_mod_cast this.1) (by exact_mod_cast this.2.1)
    exact (mul_pos_iff_of_pos_left dxy).mp this
  | zzero => simp [Chart.detPos] at h
  | zauto =>
    simp only [Chart.detPos,Bool.and_eq_true] at h
    have := ZSign.autoOK_sound G.zb G.zpos.2.2 G.pos (small' G) h.2
    rw [dz_eq G h.1] at this
    have dxy : (0:ℚ)<C.z.dx*C.z.dy := by
      have := G.zpos; exact mul_pos (by exact_mod_cast this.1) (by exact_mod_cast this.2.1)
    exact (mul_pos_iff_of_pos_left dxy).mp this

  | zlit b hh i0 j0 i1 j1 i2 j2 =>
    simp only [Chart.detPos,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨hok,hr⟩,hp⟩ := h
    have := ZSign.prodL_sound G.zb G.zpos.2.2 G.pos (small' G) hp
    have e := ZSign.DZ_rot C.z s A w g c b
    simp only [hr] at e
    rw [e,dz_eq G hok] at this
    have dxy : (0:ℚ)<C.z.dx*C.z.dy := by
      have := G.zpos; exact mul_pos (by exact_mod_cast this.1) (by exact_mod_cast this.2.1)
    exact (mul_pos_iff_of_pos_left dxy).mp this

theorem detSign_sound (G : Good C X Y s A) {pos : Bool} {w g c : Index} {sg : Sign}
    (hw : w.1<C.nx ∧ w.2<C.ny) (hg : g.1<C.nx ∧ g.2<C.ny) (hc : c.1<C.nx ∧ c.2<C.ny)
    (h : C.detSign pos w g c sg=true) :
    (sg.isZero=true → ArtGallery.det (gridPt X Y w) (gridPt X Y g) (gridPt X Y c)=0) ∧
    (sg.isZero=false → (pos=true → 0<ArtGallery.det (gridPt X Y w) (gridPt X Y g) (gridPt X Y c)) ∧
      (pos=false → ArtGallery.det (gridPt X Y w) (gridPt X Y g) (gridPt X Y c)<0)) := by
  cases sg with
  | zero =>
    refine ⟨fun _ => ?_,fun e => by simp [Sign.isZero] at e⟩
    have nil : C.detForm w g c=[] := List.isEmpty_iff.mp h
    have v := RegisterPoly.det_value s A (C.fx.getD w.1 []) (C.fy.getD w.2 []) (C.fx.getD g.1 [])
      (C.fy.getD g.2 []) (C.fx.getD c.1 []) (C.fy.getD c.2 [])
    rw [show RegisterPoly.det (C.fx.getD w.1 []) (C.fy.getD w.2 []) (C.fx.getD g.1 []) (C.fy.getD g.2 [])
      (C.fx.getD c.1 []) (C.fy.getD c.2 [])=C.detForm w g c from rfl,nil,value] at v
    rw [det_real G hw hg hc,←v]; simp
  | zzero =>
    refine ⟨fun _ => ?_,fun e => by simp [Sign.isZero] at e⟩
    simp only [Chart.detSign,Bool.and_eq_true] at h
    have z0 := ZSign.zeroOK_sound (s:=s) (A:=A) h.2
    rw [dz_eq G h.1] at z0
    have dxy : (C.z.dx:ℚ)*C.z.dy≠0 := by
      have := G.zpos; exact mul_ne_zero (by exact_mod_cast this.1.ne') (by exact_mod_cast this.2.1.ne')
    rw [det_real G hw hg hc]
    have := (mul_eq_zero.mp z0).resolve_left dxy
    rw [this]; simp
  | poly k | prod hh | zprod _ hh | zpoly k | zauto | zlit _ _ _ _ _ _ _ _ =>
    refine ⟨fun e => by simp [Sign.isZero] at e,fun _ => ?_⟩
    cases pos with
    | true => exact ⟨fun _ => detPos_sound G hw hg hc (by simpa [Chart.detSign] using h),fun e => by simp at e⟩
    | false =>
      refine ⟨fun e => by simp at e,fun _ => ?_⟩
      have := detPos_sound G hw hc hg (by simpa [Chart.detSign] using h)
      have sw : ArtGallery.det (gridPt X Y w) (gridPt X Y c) (gridPt X Y g)=
          -ArtGallery.det (gridPt X Y w) (gridPt X Y g) (gridPt X Y c) := by
        simp only [ArtGallery.det]; ring
      linarith

private theorem sign_of_side {u : ℝ} {p : Int} (h : (p<0 → u<0) ∧ (0<p → 0<u)) (ne : p≠0) :
    (p<0 ∧ u<0) ∨ (0<p ∧ 0<u) := by
  rcases lt_or_gt_of_ne ne with l|g
  · exact Or.inl ⟨l,h.1 l⟩
  · exact Or.inr ⟨g,h.2 g⟩

/-- An affine combination that is positive at one end and positive or zero at the other. -/
private theorem affine_pos {d₀ d₁ t : ℝ} (t0 : 0≤t) (t1 : t≤1)
    (h₀ : 0<d₀ ∨ (d₀=0 ∧ 0<t)) (h₁ : 0<d₁ ∨ (d₁=0 ∧ t<1)) (both : 0<d₀ ∨ 0<d₁) :
    0<(1-t)*d₀+t*d₁ := by
  rcases h₀ with p₀|⟨z₀,tp⟩ <;> rcases h₁ with p₁|⟨z₁,tq⟩
  · rcases eq_or_lt_of_le t0 with e|p
    · rw [←e]; simpa using p₀
    · nlinarith [mul_nonneg (sub_nonneg.mpr t1) p₀.le]
  · rw [z₁]; nlinarith
  · rw [z₀]; nlinarith
  · rcases both with b|b <;> linarith

/-- Strict parameter range on an open span cell. -/
private theorem open_param {xs : List ℝ} (hx : xs.IsChain (·<·)) {c : Nat} (hc : Inner xs.length c)
    (ev : c%2=0) {z t : ℝ} (hz : atom z xs=c) (ht : z=xs.getD (lo c) 0+t*(xs.getD (hi c) 0-xs.getD (lo c) 0)) :
    0<t ∧ t<1 := by
  have hl : lo c<xs.length := by unfold lo; unfold Inner hi at hc; omega
  have up : z<xs.getD (hi c) 0 := (compare_line hx hc.2 z).1.mpr (by rw [hz]; unfold line hi; unfold Inner at hc; omega)
  have low : xs.getD (lo c) 0<z := by
    by_contra n
    have := (le_line hx hl z).mp (not_lt.mp n)
    rw [hz] at this; unfold line lo at this; unfold Inner at hc; omega
  have gap : 0<xs.getD (hi c) 0-xs.getD (lo c) 0 := by linarith
  constructor
  · by_contra n; push Not at n; nlinarith
  · by_contra n; push Not at n; nlinarith

theorem cross_sound (G : Good C X Y s A) {w : Index} {cell : Nat × Nat} {k : Nat} {pos : Bool}
    {s₀ s₁ s₂ s₃ : Sign} (hw : w.1<C.nx ∧ w.2<C.ny)
    (hcell : Inner C.nx cell.1 ∧ Inner C.ny cell.2 ∧ (cell.1%2=1 ∨ cell.2%2=1))
    (h : C.ok w cell (.cross k pos s₀ s₁ s₂ s₃)=true) {z : Point} (zx : atom z.1 X=cell.1) (zy : atom z.2 Y=cell.2) :
    ¬(C.poly X Y).Sees z (gridPt X Y w) := by
  simp only [Chart.ok,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hk,ne⟩,opp⟩,c₀⟩,c₁⟩,c₂⟩,c₃⟩,za⟩,zb⟩,zo⟩ := h
  intro sees
  have nr := node_range G k hk
  have xr := next_range G k hk
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  have ax := axis_next G.axis hk
  let a := C.node k
  let b := C.next k
  let g₀ : Index := (lo cell.1,lo cell.2)
  let g₁ : Index := (hi cell.1,hi cell.2)
  have rn (p : Index) (hp : p.1<X.length ∧ p.2<Y.length) : p.1<C.nx ∧ p.2<C.ny := by
    rw [←G.lx,←G.ly]; exact hp
  have r₀ : g₀.1<C.nx ∧ g₀.2<C.ny := ⟨by have := hcell.1.2; show lo cell.1<C.nx; unfold lo; unfold hi at this; omega,
    by have := hcell.2.1.2; show lo cell.2<C.ny; unfold lo; unfold hi at this; omega⟩
  have r₁ : g₁.1<C.nx ∧ g₁.2<C.ny := ⟨hcell.1.2,hcell.2.1.2⟩
  have d₀a := detSign_sound G hw r₀ (rn a nr) c₀
  have d₀b := detSign_sound G hw r₀ (rn b xr) c₁
  have d₁a := detSign_sound G hw r₁ (rn a nr) c₂
  have d₁b := detSign_sound G hw r₁ (rn b xr) c₃
  have hcx : Inner X.length cell.1 := by rw [G.lx]; exact hcell.1
  have hcy : Inner Y.length cell.2 := by rw [G.ly]; exact hcell.2.1
  obtain ⟨t,t0,t1,zt⟩ := Geometry.mem_segment_iff_lerp.mp (segment_of_cell G.hx G.hy hcx hcy hcell.2.2 zx zy)
  -- strict parameter on an open cell
  have strictT : (s₀.isZero || s₁.isZero || s₂.isZero || s₃.isZero)=true → 0<t ∧ t<1 := by
    intro any
    have oc : cell.1%2=0 ∨ cell.2%2=0 := by
      rcases zo with n|o
      · simp only [n] at any; exact absurd any (by decide)
      · exact o
    rcases oc with e|e
    · exact open_param G.hx hcx e zx (by rw [zt]; rfl)
    · exact open_param G.hy hcy e zy (by rw [zt]; rfl)
  have along (c : Point) : ArtGallery.det (gridPt X Y w) z c=
      (1-t)*ArtGallery.det (gridPt X Y w) (gridPt X Y g₀) c+t*ArtGallery.det (gridPt X Y w) (gridPt X Y g₁) c := by
    rw [zt]; exact Geometry.det_lerp_mid _ _ _ _ _
  -- one-sided sign facts for a vertex `v` with signs at both ends
  have side (v : Point) (sA sB : Sign) (p : Bool)
      (dA : (sA.isZero=true → ArtGallery.det (gridPt X Y w) (gridPt X Y g₀) v=0) ∧
        (sA.isZero=false → (p=true → 0<ArtGallery.det (gridPt X Y w) (gridPt X Y g₀) v) ∧
          (p=false → ArtGallery.det (gridPt X Y w) (gridPt X Y g₀) v<0)))
      (dB : (sB.isZero=true → ArtGallery.det (gridPt X Y w) (gridPt X Y g₁) v=0) ∧
        (sB.isZero=false → (p=true → 0<ArtGallery.det (gridPt X Y w) (gridPt X Y g₁) v) ∧
          (p=false → ArtGallery.det (gridPt X Y w) (gridPt X Y g₁) v<0)))
      (nb : (sA.isZero && sB.isZero)=false)
      (tA : sA.isZero=true → 0<t) (tB : sB.isZero=true → t<1) :
      (p=true → 0<ArtGallery.det (gridPt X Y w) z v) ∧ (p=false → ArtGallery.det (gridPt X Y w) z v<0) := by
    rw [along]
    cases p with
    | true =>
      refine ⟨fun _ => ?_,fun e => by simp at e⟩
      cases ha : sA.isZero <;> cases hb : sB.isZero
      · exact affine_pos t0 t1 (Or.inl ((dA.2 ha).1 rfl)) (Or.inl ((dB.2 hb).1 rfl)) (Or.inl ((dA.2 ha).1 rfl))
      · exact affine_pos t0 t1 (Or.inl ((dA.2 ha).1 rfl)) (Or.inr ⟨dB.1 hb,tB hb⟩) (Or.inl ((dA.2 ha).1 rfl))
      · exact affine_pos t0 t1 (Or.inr ⟨dA.1 ha,tA ha⟩) (Or.inl ((dB.2 hb).1 rfl)) (Or.inr ((dB.2 hb).1 rfl))
      · simp [ha,hb] at nb
    | false =>
      refine ⟨fun e => by simp at e,fun _ => ?_⟩
      have neg : 0<(1-t)*(-ArtGallery.det (gridPt X Y w) (gridPt X Y g₀) v)+t*(-ArtGallery.det (gridPt X Y w) (gridPt X Y g₁) v) := by
        cases ha : sA.isZero <;> cases hb : sB.isZero
        · exact affine_pos t0 t1 (Or.inl (neg_pos.mpr ((dA.2 ha).2 rfl))) (Or.inl (neg_pos.mpr ((dB.2 hb).2 rfl)))
            (Or.inl (neg_pos.mpr ((dA.2 ha).2 rfl)))
        · exact affine_pos t0 t1 (Or.inl (neg_pos.mpr ((dA.2 ha).2 rfl))) (Or.inr ⟨by rw [dB.1 hb]; simp,tB hb⟩)
            (Or.inl (neg_pos.mpr ((dA.2 ha).2 rfl)))
        · exact affine_pos t0 t1 (Or.inr ⟨by rw [dA.1 ha]; simp,tA ha⟩) (Or.inl (neg_pos.mpr ((dB.2 hb).2 rfl)))
            (Or.inr (neg_pos.mpr ((dB.2 hb).2 rfl)))
        · simp [ha,hb] at nb
      linarith
  have sa := side (gridPt X Y a) s₀ s₂ pos d₀a d₁a (by simpa using za)
    (fun e => (strictT (by simp [e])).1) (fun e => (strictT (by simp [e])).2)
  have sb := side (gridPt X Y b) s₁ s₃ (!pos) d₀b d₁b (by simpa using zb)
    (fun e => (strictT (by simp [e])).1) (fun e => (strictT (by simp [e])).2)
  have crossW : ArtGallery.det (gridPt X Y w) z (gridPt X Y a)*ArtGallery.det (gridPt X Y w) z (gridPt X Y b)<0 := by
    cases pos with
    | true => exact mul_neg_of_pos_of_neg (sa.1 rfl) (sb.2 rfl)
    | false => exact mul_neg_of_neg_of_pos (sa.2 rfl) (sb.1 rfl)
  have hwr : w.1<X.length ∧ w.2<Y.length := by rw [G.lx,G.ly]; exact hw
  have sw := sign_of_side (side_node G.hx G.hy nr xr hwr ax) ne
  have sz := side_sound G.hx G.hy nr xr ax zx zy
  have crossE : ArtGallery.det (gridPt X Y a) (gridPt X Y b) (gridPt X Y w)*ArtGallery.det (gridPt X Y a) (gridPt X Y b) z<0 := by
    rcases sw with ⟨l,u⟩|⟨l,u⟩
    · exact mul_neg_of_neg_of_pos u (sz.2 (by rw [opp]; omega))
    · exact mul_neg_of_pos_of_neg u (sz.1 (by rw [opp]; omega))
  rw [←node_vtx C X Y hk,←next_vtx C X Y hk] at crossE crossW
  exact Polygon.not_sees_of_proper_cross G.simple hk' crossE crossW (Polygon.sees_comm.mp sees)


/-! ## Pieces of an open span cell -/

/-- A point given by two register forms. -/
abbrev PForm := Form × Form

def Chart.nodeF (C : Chart) (p : Index) : PForm := (C.fx.getD p.1 [],C.fy.getD p.2 [])

def lerpF (a b : PForm) (t : ℚ) : PForm :=
  (plus (scaled 0 (1-t) a.1) (scaled 0 t b.1),plus (scaled 0 (1-t) a.2) (scaled 0 t b.2))

/-- Certified `det w g c > 0` for points given by forms. -/
def detPosF (B : Nat → Box) (w g c : PForm) : Sign → Bool
  | .poly k => RegisterForm.positive (RegisterPoly.B2 B) (RegisterPoly.det w.1 w.2 g.1 g.2 c.1 c.2) k
  | .prod h => RegisterProduct.check B (diff g.1 w.1) (diff c.2 w.2) (diff g.2 w.2) (diff c.1 w.1) h
  | .zero => false
  | .zprod _ _ => false
  | .zpoly _ => false
  | .zzero => false
  | .zauto => false
  | .zlit _ _ _ _ _ _ _ _ => false

def detSignF (B : Nat → Box) (pos : Bool) (w g c : PForm) (s : Sign) : Bool :=
  if pos then detPosF B w g c s else detPosF B w c g s

/-- A crossing exclusion on the closed piece `[t₀,t₁]` of a cell's segment. -/
def Chart.pieceOK (C : Chart) (w : Index) (cell : Nat × Nat) (t₀ t₁ : ℚ) (k : Nat) (pos : Bool)
    (s₀ s₁ s₂ s₃ : Sign) : Bool :=
  let a := C.node k
  let b := C.next k
  let g₀ := C.nodeF (lo cell.1,lo cell.2)
  let g₁ := C.nodeF (hi cell.1,hi cell.2)
  let p₀ := lerpF g₀ g₁ t₀
  let p₁ := lerpF g₀ g₁ t₁
  decide (0≤t₀ ∧ t₀≤t₁ ∧ t₁≤1) && decide (k<C.n) && decide (sideNode a b w≠0) &&
    decide (side a b cell= -sideNode a b w) &&
    detSignF C.B pos (C.nodeF w) p₀ (C.nodeF a) s₀ && detSignF C.B (!pos) (C.nodeF w) p₀ (C.nodeF b) s₁ &&
    detSignF C.B pos (C.nodeF w) p₁ (C.nodeF a) s₂ && detSignF C.B (!pos) (C.nodeF w) p₁ (C.nodeF b) s₃

/-- A piece: whether it excludes the anchor (`true`) or the foreign witness, its parameter
range and its crossing data. -/
abbrev Piece := Bool × ℚ × ℚ × Nat × Bool × Sign × Sign × Sign × Sign

/-- Pieces cover `[start,1]` consecutively. -/
def chainCover : ℚ → List Piece → Bool
  | _,[] => false
  | s,[p] => decide (p.2.1=s) && decide (1≤p.2.2.1)
  | s,p::q::ps => decide (p.2.1=s) && chainCover p.2.2.1 (q::ps)

theorem chainCover_mem : ∀ {s : ℚ} {ps : List Piece}, chainCover s ps=true → ∀ t : ℚ, s≤t → t≤1 →
    ∃ p∈ps, p.2.1≤t ∧ t≤p.2.2.1
  | _,[],h,_,_,_ => by simp [chainCover] at h
  | s,[p],h,t,st,t1 => by
    simp only [chainCover,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨p,List.mem_singleton_self _,h.1 ▸ st,t1.trans h.2⟩
  | s,p::q::ps,h,t,st,t1 => by
    simp only [chainCover,Bool.and_eq_true,decide_eq_true_eq] at h
    by_cases le : t≤p.2.2.1
    · exact ⟨p,List.mem_cons_self,h.1 ▸ st,le⟩
    · obtain ⟨r,hr,a,b⟩ := chainCover_mem h.2 t (not_le.mp le).le t1
      exact ⟨r,List.mem_cons_of_mem _ hr,a,b⟩

theorem chainCover_real : ∀ {s : ℚ} {ps : List Piece}, chainCover s ps=true → ∀ t : ℝ, (s:ℝ)≤t → t≤1 →
    ∃ p∈ps, (p.2.1:ℝ)≤t ∧ t≤(p.2.2.1:ℝ)
  | _,[],h,_,_,_ => by simp [chainCover] at h
  | s,[p],h,t,st,t1 => by
    simp only [chainCover,Bool.and_eq_true,decide_eq_true_eq] at h
    refine ⟨p,List.mem_singleton_self _,by rw [h.1]; exact st,t1.trans ?_⟩
    exact_mod_cast h.2
  | s,p::q::ps,h,t,st,t1 => by
    simp only [chainCover,Bool.and_eq_true,decide_eq_true_eq] at h
    by_cases le : t≤(p.2.2.1:ℝ)
    · exact ⟨p,List.mem_cons_self,by rw [h.1]; exact st,le⟩
    · obtain ⟨r,hr,a,b⟩ := chainCover_real h.2 t (not_le.mp le).le t1
      exact ⟨r,List.mem_cons_of_mem _ hr,a,b⟩

inductive Foreign
  | plain (e : Excl)
  | split (ps : List Piece)


/-- A pair of forms realizes a point. -/
def Realizes (s : ℚ) (A : Nat → ℚ) (pf : PForm) (q : Point) : Prop :=
  q=(((value s A pf.1:ℚ):ℝ),((value s A pf.2:ℚ):ℝ))

theorem node_realizes (G : Good C X Y s A) {p : Index} (hp : p.1<C.nx ∧ p.2<C.ny) :
    Realizes s A (C.nodeF p) (gridPt X Y p) := by
  simp only [Realizes,Chart.nodeF,gridPt,G.vx _ hp.1,G.vy _ hp.2]

theorem lerp_realizes {a b : PForm} {qa qb : Point} (ha : Realizes s A a qa) (hb : Realizes s A b qb) (t : ℚ) :
    Realizes s A (lerpF a b t) (Geometry.lerp qa qb (t:ℝ)) := by
  simp only [Realizes] at ha hb ⊢
  subst ha hb
  simp only [lerpF,Geometry.lerp,plus_value,scaled_value,pow_zero,mul_one]
  push_cast; ext <;> simp <;> ring

theorem detPosF_sound (G : Good C X Y s A) {w g c : PForm} {qw qg qc : Point} {sg : Sign}
    (hw : Realizes s A w qw) (hg : Realizes s A g qg) (hc : Realizes s A c qc)
    (h : detPosF C.B w g c sg=true) : 0<ArtGallery.det qw qg qc := by
  have e : ArtGallery.det qw qg qc=
      (((value s A g.1-value s A w.1)*(value s A c.2-value s A w.2)-(value s A g.2-value s A w.2)*(value s A c.1-value s A w.1):ℚ):ℝ) := by
    simp only [Realizes] at hw hg hc; subst hw hg hc
    simp only [ArtGallery.det]; push_cast; ring
  rw [e]
  apply Rat.cast_pos.mpr
  cases sg with
  | poly k =>
    have := RegisterPoly.positive G.bounds G.pos G.small h
    rwa [RegisterPoly.det_value] at this
  | prod hh =>
    have := RegisterProduct.compare G.bounds G.pos G.small hh h
    simp only [diff_value] at this
    linarith
  | zero => simp [detPosF] at h
  | zprod _ _ => simp [detPosF] at h
  | zpoly _ => simp [detPosF] at h
  | zzero => simp [detPosF] at h
  | zauto => simp [detPosF] at h
  | zlit _ _ _ _ _ _ _ _ => simp [detPosF] at h

theorem detSignF_sound (G : Good C X Y s A) {pos : Bool} {w g c : PForm} {qw qg qc : Point} {sg : Sign}
    (hw : Realizes s A w qw) (hg : Realizes s A g qg) (hc : Realizes s A c qc)
    (h : detSignF C.B pos w g c sg=true) :
    (pos=true → 0<ArtGallery.det qw qg qc) ∧ (pos=false → ArtGallery.det qw qg qc<0) := by
  cases pos with
  | true => exact ⟨fun _ => detPosF_sound G hw hg hc (by simpa [detSignF] using h),fun e => by simp at e⟩
  | false =>
    refine ⟨fun e => by simp at e,fun _ => ?_⟩
    have := detPosF_sound G hw hc hg (by simpa [detSignF] using h)
    have sw : ArtGallery.det qw qc qg=-ArtGallery.det qw qg qc := by simp only [ArtGallery.det]; ring
    linarith

private theorem lerp_lerp (a b : Point) (t₀ t₁ u : ℝ) :
    Geometry.lerp (Geometry.lerp a b t₀) (Geometry.lerp a b t₁) u=Geometry.lerp a b (t₀+u*(t₁-t₀)) := by
  simp only [Geometry.lerp]; ext <;> simp <;> ring

theorem piece_sound (G : Good C X Y s A) {w : Index} {cell : Nat × Nat} {t₀ t₁ : ℚ} {k : Nat} {pos : Bool}
    {s₀ s₁ s₂ s₃ : Sign} (hw : w.1<C.nx ∧ w.2<C.ny)
    (hcell : Inner C.nx cell.1 ∧ Inner C.ny cell.2 ∧ (cell.1%2=1 ∨ cell.2%2=1))
    (h : C.pieceOK w cell t₀ t₁ k pos s₀ s₁ s₂ s₃=true) {z : Point} (zx : atom z.1 X=cell.1) (zy : atom z.2 Y=cell.2)
    {t : ℝ} (zt : z=Geometry.lerp (gridPt X Y (lo cell.1,lo cell.2)) (gridPt X Y (hi cell.1,hi cell.2)) t)
    (ht₀ : (t₀:ℝ)≤t) (ht₁ : t≤(t₁:ℝ)) :
    ¬(C.poly X Y).Sees z (gridPt X Y w) := by
  simp only [Chart.pieceOK,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨range,hk⟩,ne⟩,opp⟩,c₀⟩,c₁⟩,c₂⟩,c₃⟩ := h
  intro sees
  have nr := node_range G k hk
  have xr := next_range G k hk
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  have ax := axis_next G.axis hk
  have rn (p : Index) (hp : p.1<X.length ∧ p.2<Y.length) : p.1<C.nx ∧ p.2<C.ny := by
    rw [←G.lx,←G.ly]; exact hp
  have r₀ : (lo cell.1,lo cell.2).1<C.nx ∧ (lo cell.1,lo cell.2).2<C.ny :=
    ⟨by have := hcell.1.2; show lo cell.1<C.nx; unfold lo; unfold hi at this; omega,
     by have := hcell.2.1.2; show lo cell.2<C.ny; unfold lo; unfold hi at this; omega⟩
  have r₁ : (hi cell.1,hi cell.2).1<C.nx ∧ (hi cell.1,hi cell.2).2<C.ny := ⟨hcell.1.2,hcell.2.1.2⟩
  let G₀ := gridPt X Y (lo cell.1,lo cell.2)
  let G₁ := gridPt X Y (hi cell.1,hi cell.2)
  have R₀ := lerp_realizes (node_realizes G r₀) (node_realizes G r₁) t₀
  have R₁ := lerp_realizes (node_realizes G r₀) (node_realizes G r₁) t₁
  have Rw := node_realizes G hw
  have Ra := node_realizes G (rn _ nr)
  have Rb := node_realizes G (rn _ xr)
  have d₀a := detSignF_sound G Rw R₀ Ra c₀
  have d₀b := detSignF_sound G Rw R₀ Rb c₁
  have d₁a := detSignF_sound G Rw R₁ Ra c₂
  have d₁b := detSignF_sound G Rw R₁ Rb c₃
  -- the point as a lerp of the two piece ends
  obtain ⟨u,u0,u1,zu⟩ : ∃ u : ℝ, 0≤u ∧ u≤1 ∧ z=Geometry.lerp (Geometry.lerp G₀ G₁ (t₀:ℝ)) (Geometry.lerp G₀ G₁ (t₁:ℝ)) u := by
    rcases eq_or_lt_of_le ((ht₀.trans ht₁)) with e|lt
    · refine ⟨0,le_refl _,zero_le_one,?_⟩
      rw [lerp_lerp,zt]; congr 1; linarith [ht₀,ht₁,e]
    · refine ⟨(t-t₀)/(t₁-t₀),div_nonneg (by linarith) (by linarith),(div_le_one (by linarith)).mpr (by linarith),?_⟩
      rw [lerp_lerp,zt]; congr 1; field_simp; ring
  have along (c : Point) : ArtGallery.det (gridPt X Y w) z c=
      (1-u)*ArtGallery.det (gridPt X Y w) (Geometry.lerp G₀ G₁ (t₀:ℝ)) c+u*ArtGallery.det (gridPt X Y w) (Geometry.lerp G₀ G₁ (t₁:ℝ)) c := by
    rw [zu]; exact Geometry.det_lerp_mid _ _ _ _ _
  have pos_comb {d₀ d₁ : ℝ} (h₀ : 0<d₀) (h₁ : 0<d₁) : 0<(1-u)*d₀+u*d₁ := by
    rcases eq_or_lt_of_le u0 with e|p
    · rw [←e]; simpa using h₀
    · nlinarith [mul_nonneg (sub_nonneg.mpr u1) h₀.le]
  have crossW : ArtGallery.det (gridPt X Y w) z (gridPt X Y (C.node k))*ArtGallery.det (gridPt X Y w) z (gridPt X Y (C.next k))<0 := by
    rw [along,along]
    cases pos with
    | true =>
      have n₁ := pos_comb (neg_pos.mpr (d₀b.2 rfl)) (neg_pos.mpr (d₁b.2 rfl))
      exact mul_neg_of_pos_of_neg (pos_comb (d₀a.1 rfl) (d₁a.1 rfl)) (by linarith)
    | false =>
      have n₁ := pos_comb (neg_pos.mpr (d₀a.2 rfl)) (neg_pos.mpr (d₁a.2 rfl))
      exact mul_neg_of_neg_of_pos (by linarith) (pos_comb (d₀b.1 rfl) (d₁b.1 rfl))
  have hwr : w.1<X.length ∧ w.2<Y.length := by rw [G.lx,G.ly]; exact hw
  have sw := sign_of_side (side_node G.hx G.hy nr xr hwr ax) ne
  have sz := side_sound G.hx G.hy nr xr ax zx zy
  have crossE : ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) (gridPt X Y w)*
      ArtGallery.det (gridPt X Y (C.node k)) (gridPt X Y (C.next k)) z<0 := by
    rcases sw with ⟨l,u'⟩|⟨l,u'⟩
    · exact mul_neg_of_neg_of_pos u' (sz.2 (by rw [opp]; omega))
    · exact mul_neg_of_pos_of_neg u' (sz.1 (by rw [opp]; omega))
  rw [←node_vtx C X Y hk,←next_vtx C X Y hk] at crossE crossW
  exact Polygon.not_sees_of_proper_cross G.simple hk' crossE crossW (Polygon.sees_comm.mp sees)

theorem ok_sound (G : Good C X Y s A) {w : Index} {cell : Nat × Nat} {e : Excl}
    (hw : w.1<C.nx ∧ w.2<C.ny) (mem : cell∈cellsOf C.cyc)
    (h : C.ok w cell e=true) {z : Point} (zx : atom z.1 X=cell.1) (zy : atom z.2 Y=cell.2) :
    ¬(C.poly X Y).Sees z (gridPt X Y w) := by
  have hc := G.cells cell mem
  cases e with
  | cone k out => exact cone_sound G h zx zy
  | half k => exact half_sound G h zx zy
  | atom c => exact atom_sound G hw ⟨hc.1,hc.2.1⟩ h zx zy
  | cross k pos s₀ s₁ s₂ s₃ => exact cross_sound G hw hc h zx zy

/-! ## Role certificates -/

inductive Entry
  | anchor (e : Excl)
  | foreign (es : List (Nat × Nat × Foreign))

/-- Witness `s` of role `k`, in grid indices. -/
def wit (roles : List (List Index)) (k s : Nat) : Index := ((roles.getD k []).drop 3).getD s (0,0)

/-- A foreign exclusion: a plain exclusion of the foreign witness, or a split of the cell into
pieces, each excluding the anchor or the foreign witness. -/
def Chart.fexOK (C : Chart) (wa wh : Index) (cell : Nat × Nat) : Foreign → Bool
  | .plain e => C.ok wh cell e
  | .split ps => decide (cell.1%2=0 ∨ cell.2%2=0) && chainCover 0 ps &&
      ps.all fun p => C.pieceOK (if p.1 then wa else wh) cell p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2

def Chart.foreignOK (C : Chart) (roles : List (List Index)) (i a : Nat) (cell : Nat × Nat)
    (es : List (Nat × Nat × Foreign)) : Bool :=
  (List.range roles.length).all fun k => k==i || (List.range 3).all fun t =>
    es.any fun x => x.1==k && x.2.1==t && C.fexOK (wit roles i a) (wit roles k t) cell x.2.2

/-- Boolean check of a relation along two lists of equal length. -/
def allZip {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [],[] => true
  | a::as,b::bs => f a b && allZip f as bs
  | _,_ => false

theorem allZip_mem {α β : Type} {f : α → β → Bool} {l : List α} {m : List β} (h : allZip f l m=true)
    {a : α} (ha : a∈l) : ∃ b, f a b=true := by
  induction l generalizing m with
  | nil => simp at ha
  | cons x l ih =>
    cases m with
    | nil => simp [allZip] at h
    | cons y m =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp ha with rfl|t
      · exact ⟨y,h.1⟩
      · exact ih h.2 t

theorem allZip_append {α β : Type} {f : α → β → Bool} {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h₁ : allZip f l₁ m₁=true) (h₂ : allZip f l₂ m₂=true) : allZip f (l₁++l₂) (m₁++m₂)=true := by
  induction l₁ generalizing m₁ with
  | nil => cases m₁ with
    | nil => simpa using h₂
    | cons _ _ => simp [allZip] at h₁
  | cons a l ih => cases m₁ with
    | nil => simp [allZip] at h₁
    | cons b m =>
      simp only [allZip,Bool.and_eq_true] at h₁
      show (f a b && allZip f (l++l₂) (m++m₂))=true
      rw [h₁.1,ih h₁.2]; rfl

/-- Checking along a partition of both lists into corresponding blocks. -/
theorem allZip_flatten {α β : Type} {f : α → β → Bool} :
    ∀ (ls : List (List α)) (ms : List (List β)), ls.length=ms.length →
      (∀ i, i < ls.length → allZip f (ls.getD i []) (ms.getD i [])=true) → allZip f ls.flatten ms.flatten=true
  | [],[],_,_ => rfl
  | l::ls,m::ms,hl,h => by
    rw [List.flatten_cons,List.flatten_cons]
    exact allZip_append (h 0 (by simp))
      (allZip_flatten ls ms (by simpa using hl) (fun i hi => by simpa using h (i+1) (by simp; omega)))
  | [],_::_,hl,_ => by simp at hl
  | _::_,[],hl,_ => by simp at hl

/-- Chunked checking: consecutive blocks of `c` items, each with its own entry list. -/
theorem allZip_chunks {α β : Type} {f : α → β → Bool} (c : Nat) (l : List α) (ms : List (List β))
    (h : ∀ i, i < ms.length → allZip f ((l.drop (c*i)).take c) (ms.getD i [])=true)
    (len : l.length≤c*ms.length) : allZip f l ms.flatten=true := by
  induction ms generalizing l with
  | nil =>
    have : l=[] := List.eq_nil_of_length_eq_zero (by simpa using len)
    subst this; rfl
  | cons m ms ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero,List.drop_zero,List.getD_cons_zero] at h0
    rw [List.flatten_cons,←List.take_append_drop c l]
    apply allZip_append h0
    apply ih
    · intro i hi
      have := h (i+1) (by simp; omega)
      simpa [Nat.mul_succ,List.drop_drop,Nat.add_comm] using this
    · simp only [List.length_drop]; simp only [List.length_cons] at len; rw [Nat.mul_succ] at len; omega

def Chart.entryOK (C : Chart) (roles : List (List Index)) (i a : Nat) (cell : Nat × Nat) : Entry → Bool
  | .anchor e => C.ok (wit roles i a) cell e
  | .foreign es => C.foreignOK roles i a cell es

/-- Entries are aligned with `cellsOf`. -/
def Chart.roleOK (C : Chart) (roles : List (List Index)) (i a : Nat) (entries : List Entry) : Bool :=
  allZip (C.entryOK roles i a) (cellsOf C.cyc) entries

def Chart.rolesIn (C : Chart) (roles : List (List Index)) : Bool :=
  roles.all fun r => r.all fun p => decide (p.1<C.nx ∧ p.2<C.ny)

theorem wit_range {C : Chart} {roles : List (List Index)} (h : C.rolesIn roles=true) {k t : Nat}
    (hk : k<roles.length) (ht : t<((roles.getD k []).drop 3).length) :
    (wit roles k t).1<C.nx ∧ (wit roles k t).2<C.ny := by
  simp only [Chart.rolesIn,List.all_eq_true,decide_eq_true_eq] at h
  have mk : roles.getD k []∈roles := by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  apply h _ mk
  unfold wit
  rw [List.getD_eq_getElem _ _ ht]
  exact List.mem_of_mem_drop (List.getElem_mem ht)

/-- A role certificate: no boundary point sees the anchor of role `i` and any witness of any
other role. -/
theorem role_sound (G : Good C X Y s A) {roles : List (List Index)} (inR : C.rolesIn roles=true)
    {i a : Nat} (hi : i<roles.length) (ha : a<((roles.getD i []).drop 3).length)
    {entries : List Entry} (cert : C.roleOK roles i a entries=true)
    {y : Point} (hy : y∈(C.poly X Y).boundary) (sa : (C.poly X Y).Sees y (gridPt X Y (wit roles i a)))
    {k t : Nat} (hk : k<roles.length) (ne : k≠i) (ht : t<3)
    (htk : t<((roles.getD k []).drop 3).length) :
    ¬(C.poly X Y).Sees y (gridPt X Y (wit roles k t)) := by
  have hV : ∀ p∈C.cyc,p.1<X.length ∧ p.2<Y.length := by
    intro p hp; rw [G.lx,G.ly]; exact G.verts p hp
  have good : ∀ e∈cellsOf C.cyc,Inner X.length e.1 ∧ Inner Y.length e.2 ∧ (e.1%2=1 ∨ e.2%2=1) := by
    intro e he; rw [G.lx,G.ly]; exact G.cells e he
  obtain ⟨cell,mem,zx,zy,_⟩ := boundary_cell G.hx G.hy hV G.axis good hy
  obtain ⟨en,c⟩ := allZip_mem cert mem
  cases en with
  | anchor e => exact absurd sa (ok_sound G (wit_range inR hi ha) mem c zx zy)
  | foreign es =>
    have fk := List.all_eq_true.mp c k (List.mem_range.mpr hk)
    simp only [Bool.or_eq_true,beq_iff_eq,ne,false_or,List.all_eq_true,List.mem_range] at fk
    obtain ⟨x,_,hx⟩ := List.any_eq_true.mp (fk t ht)
    simp only [Bool.and_eq_true,beq_iff_eq] at hx
    obtain ⟨⟨e1,e2⟩,okx⟩ := hx
    subst e1 e2
    have hwk := wit_range inR hk htk
    have hwa := wit_range inR hi ha
    cases hf : x.2.2 with
    | plain e =>
      rw [hf] at okx
      exact ok_sound G hwk mem okx zx zy
    | split ps =>
      rw [hf] at okx
      simp only [Chart.fexOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at okx
      obtain ⟨⟨_,cov⟩,pieces⟩ := okx
      have hc := G.cells cell mem
      have hcx : Inner X.length cell.1 := by rw [G.lx]; exact hc.1
      have hcy : Inner Y.length cell.2 := by rw [G.ly]; exact hc.2.1
      obtain ⟨u,u0,u1,zu⟩ := Geometry.mem_segment_iff_lerp.mp (segment_of_cell G.hx G.hy hcx hcy hc.2.2 zx zy)
      obtain ⟨p,hp,pl,pu⟩ := chainCover_real cov u (by simpa using u0) u1
      have ok := pieces p hp
      cases who : p.1
      · rw [who] at ok
        exact piece_sound G hwk hc ok zx zy zu pl pu
      · rw [who] at ok
        exact absurd sa (piece_sound G hwa hc ok zx zy zu pl pu)

end Sound

end ArtGallery.Orthogonal.BoundaryPoint.SepCert
end
