module

public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles
public import ArtGallery.Orthogonal.BoundaryPoint.CopyChannel

/-! # Exclusion of a guard segment from the bottom strip of a grid cell

The nook test only uses target points just above its axis, the lower grid line of its
target cell. A `crossH` certificate is a `cross` certificate whose four corners are those of
the bottom strip of the open cell, of height `1/256` of the cell: two grid nodes and two
interpolated points, given as register forms. All its signs are strict. `CellExL` extends the cell certificates of `CellRoles` by these, and
`othersL` excludes every other role from that strip of the target cell. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CellHalf
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert RegisterForm MarginCert CellCert CellRoles
open ArtGallery.Orthogonal.Hard CopyChannel

/-- The four sign families at one corner of the bottom strip. -/
def cornerOK (C : Chart) (pos : Bool) (g₀ g₁ a b w : PForm) (q : Quad) : Bool :=
  detSignF C.B pos w g₀ a q.1 && detSignF C.B (!pos) w g₀ b q.2.1 &&
    detSignF C.B pos w g₁ a q.2.2.1 && detSignF C.B (!pos) w g₁ b q.2.2.2

/-- A crossing certificate of edge `k` over the bottom strip (height 1/256) of the open cell `(2xc+2,2iy+2)`. -/
def crossH (C : Chart) (g₀ g₁ : Index) (xc iy k : Nat) (pos : Bool) (q00 q10 q01 q11 : Quad) : Bool :=
  let a := C.node k
  let b := C.next k
  let cell := (2*xc+2,2*iy+2)
  let G₀ := C.nodeF g₀
  let G₁ := C.nodeF g₁
  let A := C.nodeF a
  let B := C.nodeF b
  let c00 := C.nodeF (xc,iy)
  let c10 := C.nodeF (xc+1,iy)
  let c01 := lerpF c00 (C.nodeF (xc,iy+1)) (1/256)
  let c11 := lerpF c10 (C.nodeF (xc+1,iy+1)) (1/256)
  decide (k<C.n) && decide (side a b cell≠0) && decide (sideNode a b g₀= -side a b cell) &&
    decide (sideNode a b g₁= -side a b cell) &&
    cornerOK C pos G₀ G₁ A B c00 q00 && cornerOK C pos G₀ G₁ A B c10 q10 &&
    cornerOK C pos G₀ G₁ A B c01 q01 && cornerOK C pos G₀ G₁ A B c11 q11 &&
    decide (g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny) && decide (xc+1<C.nx ∧ iy+1<C.ny)

section Sound
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

private theorem interp (g v : Point) (x₀ x₁ y₀ y₁ μ ν : ℝ) :
    ArtGallery.det (x₀+μ*(x₁-x₀),y₀+ν*(y₁-y₀)) g v=
      (1-μ)*(1-ν)*ArtGallery.det (x₀,y₀) g v+μ*(1-ν)*ArtGallery.det (x₁,y₀) g v+
      (1-μ)*ν*ArtGallery.det (x₀,y₁) g v+μ*ν*ArtGallery.det (x₁,y₁) g v := by
  simp only [ArtGallery.det]; ring

/-- A strictly signed bilinear combination with interior weights. -/
private theorem comb_pos {d00 d10 d01 d11 μ ν : ℝ} (m0 : 0<μ) (m1 : μ<1) (n0 : 0<ν) (n1 : ν<1)
    (h00 : 0<d00) (h10 : 0<d10) (h01 : 0<d01) (h11 : 0<d11) :
    0<(1-μ)*(1-ν)*d00+μ*(1-ν)*d10+(1-μ)*ν*d01+μ*ν*d11 := by
  have w00 : 0<(1-μ)*(1-ν) := mul_pos (by linarith) (by linarith)
  have w10 : 0<μ*(1-ν) := mul_pos m0 (by linarith)
  have w01 : 0<(1-μ)*ν := mul_pos (by linarith) n0
  have w11 : 0<μ*ν := mul_pos m0 n0
  nlinarith [mul_pos w00 h00,mul_pos w10 h10,mul_pos w01 h01,mul_pos w11 h11]

private theorem cornerOK_sound (G : Good C X Y s A) {pos : Bool} {g₀ g₁ a b w : PForm} {q : Quad}
    {qg₀ qg₁ qa qb qw : Point} (r₀ : Realizes s A g₀ qg₀) (r₁ : Realizes s A g₁ qg₁) (ra : Realizes s A a qa)
    (rb : Realizes s A b qb) (rw : Realizes s A w qw) (h : cornerOK C pos g₀ g₁ a b w q=true) :
    ∀ σ : ℝ, (pos=true → σ=1) → (pos=false → σ=-1) →
      0<σ*ArtGallery.det qw qg₀ qa ∧ 0< -σ*ArtGallery.det qw qg₀ qb ∧
      0<σ*ArtGallery.det qw qg₁ qa ∧ 0< -σ*ArtGallery.det qw qg₁ qb := by
  intro σ hp hn
  simp only [cornerOK,Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have e1 := detSignF_sound G rw r₀ ra h1
  have e2 := detSignF_sound G rw r₀ rb h2
  have e3 := detSignF_sound G rw r₁ ra h3
  have e4 := detSignF_sound G rw r₁ rb h4
  cases pos with
  | true =>
    rw [hp rfl]
    exact ⟨by linarith [e1.1 rfl],by linarith [e2.2 rfl],by linarith [e3.1 rfl],by linarith [e4.2 rfl]⟩
  | false =>
    rw [hn rfl]
    exact ⟨by linarith [e1.2 rfl],by linarith [e2.1 rfl],by linarith [e3.2 rfl],by linarith [e4.1 rfl]⟩

set_option maxHeartbeats 4000000 in
theorem crossH_sound (G : Good C X Y s A) {g₀ g₁ : Index} {xc iy k : Nat} {pos : Bool} {q00 q10 q01 q11 : Quad}
    (h : crossH C g₀ g₁ xc iy k pos q00 q10 q01 q11=true) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁)) {w : Point}
    (wx0 : X.getD xc 0<w.1) (wx1 : w.1<X.getD (xc+1) 0) (wy0 : Y.getD iy 0<w.2)
    (wy1 : w.2<Y.getD iy 0+(Y.getD (iy+1) 0-Y.getD iy 0)/256) : ¬(C.poly X Y).Sees z w := by
  simp only [crossH,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hk,ne⟩,o₀⟩,o₁⟩,c00⟩,c10⟩,c01⟩,c11⟩,⟨r₀x,r₀y,r₁x,r₁y⟩⟩,hxn,hyn⟩ := h
  intro sees
  have nr := node_range G k hk
  have xr := next_range G k hk
  have ax := axis_next G.axis hk
  have hk' : k<(C.poly X Y).n := by rw [poly_n]; exact hk
  have rn : (C.node k).1<C.nx ∧ (C.node k).2<C.ny := by rw [←G.lx,←G.ly]; exact nr
  have rx : (C.next k).1<C.nx ∧ (C.next k).2<C.ny := by rw [←G.lx,←G.ly]; exact xr
  have hxc : xc+1<X.length := by rw [G.lx]; exact hxn
  have hiy : iy+1<Y.length := by rw [G.ly]; exact hyn
  -- the realized corners
  have R (p : Index) (hp : p.1<C.nx ∧ p.2<C.ny) := node_realizes G hp
  have R00 := R (xc,iy) ⟨by omega,by omega⟩
  have R10 := R (xc+1,iy) ⟨hxn,by omega⟩
  have R01 := lerp_realizes R00 (R (xc,iy+1) ⟨by omega,hyn⟩) (1/256)
  have R11 := lerp_realizes R10 (R (xc+1,iy+1) ⟨hxn,hyn⟩) (1/256)
  have Rg₀ := R g₀ ⟨r₀x,r₀y⟩
  have Rg₁ := R g₁ ⟨r₁x,r₁y⟩
  have Ra := R _ rn
  have Rb := R _ rx
  -- the sign of the first edge end
  set σ : ℝ := if pos then 1 else -1 with hσ
  have sp : pos=true → σ=1 := fun e => by simp [σ,e]
  have sn : pos=false → σ=-1 := fun e => by simp [σ,e]
  have f00 := cornerOK_sound G Rg₀ Rg₁ Ra Rb R00 c00 σ sp sn
  have f10 := cornerOK_sound G Rg₀ Rg₁ Ra Rb R10 c10 σ sp sn
  have f01 := cornerOK_sound G Rg₀ Rg₁ Ra Rb R01 c01 σ sp sn
  have f11 := cornerOK_sound G Rg₀ Rg₁ Ra Rb R11 c11 σ sp sn
  -- the target as a point of the bottom strip
  set x₀ := X.getD xc 0
  set x₁ := X.getD (xc+1) 0
  set y₀ := Y.getD iy 0
  set y₂ := Y.getD (iy+1) 0
  have gx : 0<x₁-x₀ := by linarith
  have gy : 0<y₂-y₀ := by linarith
  set μ := (w.1-x₀)/(x₁-x₀)
  set ν := (w.2-y₀)/((y₀+(1/256:ℚ)*(y₂-y₀))-y₀)
  have hy' : 0<(y₀+(1/256:ℚ)*(y₂-y₀))-y₀ := by push_cast; linarith
  have m0 : 0<μ := div_pos (by linarith) gx
  have m1 : μ<1 := (div_lt_one gx).mpr (by linarith)
  have n0 : 0<ν := div_pos (by linarith) hy'
  have n1 : ν<1 := (div_lt_one hy').mpr (by push_cast; linarith)
  have wpt : w=(x₀+μ*(x₁-x₀),y₀+ν*((y₀+(1/256:ℚ)*(y₂-y₀))-y₀)) := by
    ext
    · simp only [μ]; field_simp; ring
    · simp only [ν]; field_simp; ring
  have p00 : Geometry.lerp (gridPt X Y (xc,iy)) (gridPt X Y (xc,iy+1)) ((1/256:ℚ):ℝ)=(x₀,y₀+(1/256:ℚ)*(y₂-y₀)) := by
    simp only [Geometry.lerp,gridPt,x₀,y₀,y₂]; ext <;> simp
  have p11 : Geometry.lerp (gridPt X Y (xc+1,iy)) (gridPt X Y (xc+1,iy+1)) ((1/256:ℚ):ℝ)=(x₁,y₀+(1/256:ℚ)*(y₂-y₀)) := by
    simp only [Geometry.lerp,gridPt,x₁,y₀,y₂]; ext <;> simp
  rw [p00] at f01; rw [p11] at f11
  rw [show gridPt X Y (xc,iy)=(x₀,y₀) from rfl] at f00
  rw [show gridPt X Y (xc+1,iy)=(x₁,y₀) from rfl] at f10
  -- one strict sign family at the target, for each guard end and edge end
  have at_w (g v : Point) (s₀ : 0<σ*ArtGallery.det (x₀,y₀) g v) (s₁ : 0<σ*ArtGallery.det (x₁,y₀) g v)
      (s₂ : 0<σ*ArtGallery.det (x₀,y₀+(1/256:ℚ)*(y₂-y₀)) g v) (s₃ : 0<σ*ArtGallery.det (x₁,y₀+(1/256:ℚ)*(y₂-y₀)) g v) :
      0<σ*ArtGallery.det w g v := by
    rw [wpt,interp]
    have := comb_pos m0 m1 n0 n1 s₀ s₁ s₂ s₃
    linarith [this]
  have at_wn (g v : Point) (s₀ : 0< -σ*ArtGallery.det (x₀,y₀) g v) (s₁ : 0< -σ*ArtGallery.det (x₁,y₀) g v)
      (s₂ : 0< -σ*ArtGallery.det (x₀,y₀+(1/256:ℚ)*(y₂-y₀)) g v) (s₃ : 0< -σ*ArtGallery.det (x₁,y₀+(1/256:ℚ)*(y₂-y₀)) g v) :
      0< -σ*ArtGallery.det w g v := by
    rw [wpt,interp]
    have := comb_pos m0 m1 n0 n1 s₀ s₁ s₂ s₃
    linarith [this]
  have wa₀ := at_w _ _ f00.1 f10.1 f01.1 f11.1
  have wa₁ := at_w _ _ f00.2.2.1 f10.2.2.1 f01.2.2.1 f11.2.2.1
  have wb₀ := at_wn _ _ f00.2.1 f10.2.1 f01.2.1 f11.2.1
  have wb₁ := at_wn _ _ f00.2.2.2 f10.2.2.2 f01.2.2.2 f11.2.2.2
  obtain ⟨t,t0,t1,zt⟩ := Geometry.mem_segment_iff_lerp.mp hz
  have mixP {a b : ℝ} (ha : 0<σ*a) (hb : 0<σ*b) : 0<σ*((1-t)*a+t*b) := by
    have e : σ*((1-t)*a+t*b)=(1-t)*(σ*a)+t*(σ*b) := by ring
    rw [e]
    rcases eq_or_lt_of_le t0 with h|h
    · subst h; simpa using ha
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) ha.le) (mul_pos h hb)
  have mixN {a b : ℝ} (ha : 0< -σ*a) (hb : 0< -σ*b) : 0< -σ*((1-t)*a+t*b) := by
    have e : -σ*((1-t)*a+t*b)=(1-t)*(-σ*a)+t*(-σ*b) := by ring
    rw [e]
    rcases eq_or_lt_of_le t0 with h|h
    · subst h; simpa using ha
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) ha.le) (mul_pos h hb)
  have za : 0<σ*ArtGallery.det w z (gridPt X Y (C.node k)) := by
    rw [zt,Geometry.det_lerp_mid]; exact mixP wa₀ wa₁
  have zb : 0< -σ*ArtGallery.det w z (gridPt X Y (C.next k)) := by
    rw [zt,Geometry.det_lerp_mid]; exact mixN wb₀ wb₁
  have σsq : σ*σ=1 := by cases pos <;> simp [σ]
  have crossW : ArtGallery.det w z (gridPt X Y (C.node k))*ArtGallery.det w z (gridPt X Y (C.next k))<0 := by
    have h := mul_pos za zb
    have e : σ*ArtGallery.det w z (gridPt X Y (C.node k))*(-σ*ArtGallery.det w z (gridPt X Y (C.next k)))=
        -(σ*σ)*(ArtGallery.det w z (gridPt X Y (C.node k))*ArtGallery.det w z (gridPt X Y (C.next k))) := by ring
    rw [e,σsq] at h; linarith
  -- the edge line separates the guard segment from the cell
  clear f00 f10 f01 f11 wa₀ wa₁ wb₀ wb₁ za zb mixP mixN at_w at_wn wpt c00 c10 c01 c11
  have wx : atom w.1 X=2*xc+2 := atom_between G.hx hxc wx0 wx1
  have wy : atom w.2 Y=2*iy+2 := atom_between G.hy hiy wy0 (by linarith)
  have hg₀ : g₀.1<X.length ∧ g₀.2<Y.length := by rw [G.lx,G.ly]; exact ⟨r₀x,r₀y⟩
  have hg₁ : g₁.1<X.length ∧ g₁.2<Y.length := by rw [G.lx,G.ly]; exact ⟨r₁x,r₁y⟩
  have s₀ := side_node G.hx G.hy nr xr hg₀ ax
  have s₁ := side_node G.hx G.hy nr xr hg₁ ax
  have sw := side_sound G.hx G.hy nr xr ax (c:=(2*xc+2,2*iy+2)) wx wy
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

end Sound

/-! ## Cell certificates of the nook test -/

/-- A certificate for the whole cell, or for its bottom strip. -/
inductive CellExL
  | full (e : CellEx)
  | low (k : Nat) (pos : Bool) (q00 q10 q01 q11 : Quad)

def CellExL.ok (C : Chart) (g₀ g₁ : Index) (xc iy : Nat) : CellExL → Bool
  | .full e => e.ok C g₀ g₁ (2*xc+2,2*iy+2)
  | .low k pos q00 q10 q01 q11 => crossH C g₀ g₁ xc iy k pos q00 q10 q01 q11

/-- Every role except the receiver `rr` carries a valid certificate. -/
def allOKL (C : Chart) (xc iy rr : Nat) : Nat → List (List Index) → List (Option CellExL) → Bool
  | _,[],[] => true
  | i,r::rs,e::es => (if i=rr then true else match e with
      | some e => e.ok C (spotA r) (spotB r) xc iy
      | none => false) && allOKL C xc iy rr (i+1) rs es
  | _,_,_ => false

/-- Checking along a split of the role list. -/
theorem allOKL_split {C : Chart} {xc iy rr : Nat} : ∀ (n i : Nat) (rs : List (List Index)) (es : List (Option CellExL)),
    allOKL C xc iy rr i (rs.take n) (es.take n)=true → allOKL C xc iy rr (i+n) (rs.drop n) (es.drop n)=true →
      allOKL C xc iy rr i rs es=true
  | 0,i,rs,es,_,h => by simpa using h
  | n+1,i,[],[],_,_ => rfl
  | n+1,i,r::rs,e::es,h1,h2 => by
    simp only [List.take_succ_cons,allOKL,Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1,allOKL_split n (i+1) rs es h1.2 (by simpa [Nat.add_assoc,Nat.add_comm 1 n] using h2)⟩
  | n+1,i,_::_,[],h1,_ => by simp [allOKL] at h1
  | n+1,i,[],_::_,h1,_ => by simp [allOKL] at h1

theorem allOKL_get {C : Chart} {xc iy rr : Nat} :
    ∀ {i : Nat} {rs : List (List Index)} {es : List (Option CellExL)}, allOKL C xc iy rr i rs es=true →
      ∀ j (hj : j<rs.length), i+j≠rr → ∃ e, es[j]?=some (some e) ∧ e.ok C (spotA rs[j]) (spotB rs[j]) xc iy=true
  | _,[],[],_ => by intro j hj; simp at hj
  | _,[],_::_,h => by simp [allOKL] at h
  | _,_::_,[],h => by simp [allOKL] at h
  | i,r::rs,e::es,h => by
    intro j hj ne
    simp only [allOKL,Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [Nat.add_zero] at ne
      simp only [ne,ite_false] at h
      cases e with
      | none => simp at h
      | some e => exact ⟨e,rfl,h.1⟩
    | succ j =>
      obtain ⟨e',h1,h2⟩ := allOKL_get h.2 j (by simpa using hj) (by omega)
      exact ⟨e',by simpa using h1,by simpa using h2⟩

variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

theorem CellExL.sound (G : Good C X Y s A) {g₀ g₁ : Index} {xc iy : Nat} {e : CellExL}
    (h : e.ok C g₀ g₁ xc iy=true) (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2)) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁)) {w : Point}
    (wx0 : X.getD xc 0<w.1) (wx1 : w.1<X.getD (xc+1) 0) (wy0 : Y.getD iy 0<w.2)
    (wy1 : w.2<Y.getD iy 0+(Y.getD (iy+1) 0-Y.getD iy 0)/256) : ¬(C.poly X Y).Sees z w := by
  cases e with
  | full e =>
    have hxc : xc+1<X.length := by rw [G.lx]; have := hc.1.2; simp only [SpanCells.hi] at this; omega
    have hiy : iy+1<Y.length := by rw [G.ly]; have := hc.2.2; simp only [SpanCells.hi] at this; omega
    exact e.sound G h hc hz (atom_between G.hx hxc wx0 wx1) (atom_between G.hy hiy wy0 (by linarith))
  | low k pos q00 q10 q01 q11 => exact crossH_sound G h hz wx0 wx1 wy0 wy1

/-- No point of another role's spot sees the bottom strip (height 1/256) of the open target cell. -/
theorem othersL (G : Good C X Y s A) {xc iy rr : Nat} {rs : List (List Index)}
    {es : List (Option CellExL)} (h : allOKL C xc iy rr 0 rs es=true) (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2))
    {j : Nat} (hj : j<rs.length) (ne : j≠rr) {z : Point}
    (hz : z∈ArtGallery.segment (gridPt X Y (spotA rs[j])) (gridPt X Y (spotB rs[j]))) {w : Point}
    (wx0 : X.getD xc 0<w.1) (wx1 : w.1<X.getD (xc+1) 0) (wy0 : Y.getD iy 0<w.2)
    (wy1 : w.2<Y.getD iy 0+(Y.getD (iy+1) 0-Y.getD iy 0)/256) : ¬(C.poly X Y).Sees z w := by
  obtain ⟨e,-,he⟩ := allOKL_get h j hj (by omega)
  exact e.sound G he hc hz wx0 wx1 wy0 wy1

end ArtGallery.Orthogonal.BoundaryPoint.CellHalf
end
