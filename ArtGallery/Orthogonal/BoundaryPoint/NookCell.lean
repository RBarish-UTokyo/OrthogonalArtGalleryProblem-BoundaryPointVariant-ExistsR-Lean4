module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyCover
public import ArtGallery.Orthogonal.BoundaryPoint.QuadCheck
public import ArtGallery.Orthogonal.BoundaryPoint.CopyLower

/-! # The cells of a copy nook are seen by the base or the receiver

A cell above the nook axis of a channel is seen, for matched values, by the receiver (a chain
certificate from its spot whose assumed ends are the window corner and the window gap) or by the
base guard (a chain certificate from the door segment whose assumed ends are the door corners).
Which one is decided by `CopyCover.nook_union`; the assumed ends are discharged by the union case,
by shifts, and by quadratic bounds in the chart coordinates (`QuadCheck`) that use the exact
crossing of the receiver rays with the axis. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.NookCell
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CoverChain CoverAssume BaseSight CopyCover QuadCheck
open ArtGallery.Orthogonal.Hard

/-- Grid data of the nook of a channel. -/
structure Nook where
  ra : Index
  rb : Index
  win : Index
  dl : Index
  dr : Index
  /-- the nook axis -/
  iy : Nat
  /-- the receiver rays cross the axis in `[X xl, X (xl+1)]` -/
  xl : Nat

def lx (i : Nat) : Lin := [⟨1,0,.x i⟩]
def ly (j : Nat) : Lin := [⟨1,0,.y j⟩]
def lneg (a : Lin) : Lin := a.map fun t => {t with c := -t.c}
def ldiff (a b : Lin) : Lin := a++lneg b

/-- The negated bound of `CopyCover.receiver_below` for the cell `[·,x']×[·,y']` and the node `w`. -/
def belowQuad (N : Nook) (x' y' : Nat) (w : Index) : Quad :=
  [(lneg (ldiff (ly N.win.2) (ly N.ra.2)),ldiff (lx x') (lx N.xl)),
   (lneg (ldiff (lx N.rb.1) (lx N.win.1)),ldiff (ly y') (ly N.iy)),
   (lneg (ldiff (lx x') (lx N.ra.1)),ldiff (ly w.2) (ly N.win.2)),
   (lneg (ldiff (lx N.win.1) (lx w.1)),ldiff (ly y') (ly N.ra.2))]

/-- The bound of `CopyCover.base_right_of` for the cell `[x,·]×[y,·]` and the door corner at height
`Y c`, with `K = 50 (c-1)`. -/
def rightQuad (N : Nook) (x y c : Nat) : Quad :=
  [(ldiff (ly N.iy) (ly N.win.2),lx x),
   (ldiff (lx N.dr.1) (lx (N.xl+1)),ldiff (ly y) (ly c)),
   ([⟨-1/1001,2,.y c⟩,⟨1/1001,2,.y N.win.2⟩],[⟨1,0,.one⟩])]

/-- `50 - H (W - x) > 0` for the crude bound `K`. -/
def crudeQuad (N : Nook) (x : Nat) : Quad :=
  [([⟨50,0,.one⟩],[⟨1,0,.one⟩]),(lneg (ldiff (ly N.iy) (ly N.win.2)),ldiff (lx N.dr.1) (lx x))]

section Reals
variable {X Y : List ℝ} {s : ℝ}

@[simp] theorem lx_real (i : Nat) : Lin.real X Y s (lx i)=X.getD i 0 := by simp [lx,Lin.real,Atom.real]
@[simp] theorem ly_real (j : Nat) : Lin.real X Y s (ly j)=Y.getD j 0 := by simp [ly,Lin.real,Atom.real]
@[simp] theorem lneg_real (a : Lin) : Lin.real X Y s (lneg a)= -Lin.real X Y s a := by
  induction a with
  | nil => simp [lneg,Lin.real]
  | cons t a ih => simp only [lneg,Lin.real,List.map_cons,List.sum_cons] at ih ⊢; rw [ih]; push_cast; ring
@[simp] theorem ldiff_real (a b : Lin) : Lin.real X Y s (ldiff a b)=Lin.real X Y s a-Lin.real X Y s b := by
  simp only [ldiff,Lin.real,List.map_append,List.sum_append]
  have := lneg_real (X:=X) (Y:=Y) (s:=s) b
  simp only [Lin.real] at this; rw [this]; ring

theorem belowQuad_real (N : Nook) (x' y' : Nat) (w : Index) :
    (belowQuad N x' y' w).real X Y s=
      -((Y.getD N.win.2 0-Y.getD N.ra.2 0)*(X.getD x' 0-X.getD N.xl 0)+
        (X.getD N.rb.1 0-X.getD N.win.1 0)*(Y.getD y' 0-Y.getD N.iy 0)+
        (X.getD x' 0-X.getD N.ra.1 0)*(Y.getD w.2 0-Y.getD N.win.2 0)+
        (X.getD N.win.1 0-X.getD w.1 0)*(Y.getD y' 0-Y.getD N.ra.2 0)) := by
  simp [belowQuad,Quad.real]; ring

theorem rightQuad_real (N : Nook) (x y c : Nat) :
    (rightQuad N x y c).real X Y s=
      (Y.getD N.iy 0-Y.getD N.win.2 0)*X.getD x 0+(X.getD N.dr.1 0-X.getD (N.xl+1) 0)*(Y.getD y 0-Y.getD c 0)-
        (Y.getD c 0-Y.getD N.win.2 0)*s^2/1001 := by
  simp only [rightQuad,Quad.real,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ldiff_real,lx_real,ly_real]
  simp [Lin.real,Atom.real]; ring

theorem crudeQuad_real (N : Nook) (x : Nat) :
    (crudeQuad N x).real X Y s=50-(Y.getD N.iy 0-Y.getD N.win.2 0)*(X.getD N.dr.1 0-X.getD x 0) := by
  simp only [crudeQuad,Quad.real,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ldiff_real,lx_real,ly_real,
    lneg_real]
  simp [Lin.real,Atom.real]; ring

end Reals


/-- Assumed ends of a receiver certificate: on the window line, left of or at the corner, wanting
`det ≥ 0` (the union case and its shifts), or above the window line, left of the corner, wanting
`det ≤ 0`, with a certified bound. -/
def rDis (C : Chart) (N : Nook) (x' y' : Nat) (e : Index × Bool) (k : Nat) : Bool :=
  (e.2 && decide (e.1.2=N.win.2 ∧ e.1.1≤N.win.1 ∧ e.1.1<C.nx)) ||
  (!e.2 && decide (N.win.2≤e.1.2 ∧ e.1.1≤N.win.1 ∧ e.1.2<C.ny) && (belowQuad N x' y' e.1).ok C k)

/-- Assumed ends of a door certificate: above the right door corner wanting `det ≤ 0` (a shift of
the union case), or above the left door corner wanting `det ≥ 0`, with a certified bound. -/
def bDis (C : Chart) (N : Nook) (x y : Nat) (e : Index × Bool) (k : Nat) : Bool :=
  (!e.2 && decide (e.1.1=N.dr.1 ∧ N.dr.2≤e.1.2 ∧ e.1.2<C.ny)) ||
  (e.2 && decide (e.1.1=N.dl.1 ∧ N.dl.2≤e.1.2 ∧ e.1.2≤y) && (rightQuad N x y e.1.2).ok C k)

/-- The checks of a nook cell `[x,x']×[y,y']`. -/
def cellOK (C : Chart) (N : Nook) (x x' y y' : Nat) (cR cB : CertA) (hR hB : List Nat) (k0 kc : Nat) : Bool :=
  cR.ok C N.ra N.rb x x' y y' && cB.ok C N.dl N.dr x x' y y' &&
  decide (hR.length=cR.assumed.length) && (cR.assumed.zip hR).all (fun p => rDis C N x' y' p.1 p.2) &&
  decide (hB.length=cB.assumed.length) && (cB.assumed.zip hB).all (fun p => bDis C N x y p.1 p.2) &&
  (rightQuad N x y N.win.2).ok C k0 && (crudeQuad N x).ok C kc &&
  decide (N.iy≤y ∧ x'≤N.dr.1 ∧ N.xl+1≤N.dr.1 ∧ N.win.2≤y ∧ N.dl.2=N.win.2 ∧ N.dr.2=N.win.2 ∧ N.ra.2<N.win.2 ∧
    N.rb.2=N.ra.2 ∧ N.win.2<N.iy ∧ x'≤N.win.1 ∧ N.dr.1<C.nx ∧ N.win.1<C.nx ∧ N.iy<C.ny ∧ N.xl+1<C.nx ∧ N.ra.1<C.nx ∧
    N.rb.1<C.nx ∧ N.ra.2<C.ny ∧ N.win.2<C.ny ∧ x'<C.nx ∧ y'<C.ny ∧ y<y')

theorem zip_all {α β : Type} {P : α → β → Bool} : ∀ {l : List α} {h : List β}, h.length=l.length →
    (l.zip h).all (fun p => P p.1 p.2)=true → ∀ e∈l, ∃ k, P e k=true
  | [],_,_,_ => by simp
  | a::l,[],e,_ => by simp at e
  | a::l,k::h,e,hall => by
    simp only [List.zip_cons_cons,List.all_cons,Bool.and_eq_true] at hall
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact ⟨k,hall.1⟩
    · exact zip_all (by simpa using e) hall.2 x hx

section Cell
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

set_option maxHeartbeats 2000000 in
/-- A nook cell above the axis is seen by the receiver or by the base guard (matched values). -/
theorem cell (G : Good C X Y s A) (one : A 0=1) {P : Polygon} (sub : (C.poly X Y).filled⊆P.filled)
    {N : Nook} {x x' y y' : Nat} {cR cB : CertA} {hR hB : List Nat} {k0 kc : Nat}
    (ok : cellOK C N x x' y y' cR cB hR hB k0 kc=true)
    {W b D t : ℝ} (hD : 0<D) (hW0 : 0≤W) (hDs : D=50050/(s:ℝ)^2) (hW : X.getD N.dr.1 0=W) (hdl0 : X.getD N.dl.1 0=0)
    (hwy : Y.getD N.win.2 0=1)
    (hrb : X.getD N.rb.1 0=X.getD N.ra.1 0+3/2*(1-Y.getD N.ra.2 0)/D)
    (L1 : 0<ArtGallery.det (X.getD N.rb.1 0,Y.getD N.rb.2 0) (X.getD N.win.1 0,Y.getD N.win.2 0) (X.getD N.xl 0,Y.getD N.iy 0))
    (L2 : ArtGallery.det (X.getD N.ra.1 0,Y.getD N.ra.2 0) (X.getD N.win.1 0,Y.getD N.win.2 0)
      (X.getD (N.xl+1) 0,Y.getD N.iy 0)<0)
    (incidence : W-b*(Y.getD N.iy 0-1)=X.getD N.win.1 0-
      ((X.getD N.ra.1 0-X.getD N.win.1 0)/(1-Y.getD N.ra.2 0))*(Y.getD N.iy 0-1))
    (hbr : b≤(X.getD N.ra.1 0-X.getD N.win.1 0)/(1-Y.getD N.ra.2 0)) (hb0 : 0≤b)
    (ht : 0≤t ∧ t≤3/2) (hdoor : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b*D+t,1-D) d)
    {z : Point} (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    P.Sees (CopyLower.receiver X Y N.ra N.rb t) z ∨ P.Sees (W+b*D+t,1-D) z := by
  simp only [cellOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨okR,okB⟩,lR⟩,dR⟩,lB⟩,dB⟩,q0⟩,qc⟩,ix⟩ := ok
  obtain ⟨iyy,xdr,xldr,winy,dlw,drw,raw,rbra,winiy,xwin,drn,winn,iyn,xln,ran,rbn,rayn,winyn,x'n,y'n,yy'⟩ := ix
  have lx := G.lx; have ly := G.ly
  have lvx {i j : Nat} (hj : j<C.nx) (h : i≤j) := lev_le G.hx (by omega : j<X.length) h
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  have ltx {i j : Nat} (hj : j<C.nx) (h : i<j) := SepGeom.level_lt G.hx (by omega : j<X.length) h
  have lty {i j : Nat} (hj : j<C.ny) (h : i<j) := SepGeom.level_lt G.hy (by omega : j<Y.length) h
  -- the frame
  set cx := X.getD N.win.1 0 with hcx
  set d := 1-Y.getD N.ra.2 0 with hd'
  have hd : 0<d := by have := lty winyn raw; rw [hwy] at this; simp only [d]; linarith
  set r := (X.getD N.ra.1 0-cx)/d with hr'
  set H := Y.getD N.iy 0-1 with hH'
  have hH : 0<H := by have := lty iyn winiy; rw [hwy] at this; simp only [H]; linarith
  have hra : X.getD N.ra.1 0=cx+d*r := by simp only [r]; field_simp; ring
  have hrbx : X.getD N.rb.1 0=cx+d*(r+3/(2*D)) := by rw [hrb,hra]; field_simp; ring
  have hrby : Y.getD N.rb.2 0=1-d := by rw [rbra]; simp only [d]; ring
  have hray : Y.getD N.ra.2 0=1-d := by simp only [d]; ring
  have hrec : CopyLower.receiver X Y N.ra N.rb t=(cx+d*(r+t/D),1-d) := by
    simp only [CopyLower.receiver,gridPt]
    rw [hrbx,hra,hray]; ext <;> simp <;> field_simp <;> ring
  -- the axis crossings of the receiver rays
  have pdet (ρ q : ℝ) : ArtGallery.det (cx+d*ρ,1-d) (cx,1) (q,1+H)=d*((cx-ρ*H)-q) := by
    simp only [ArtGallery.det]; ring
  have pmin : X.getD N.xl 0≤cx-(r+t/D)*H := by
    have e := L1
    rw [hrbx,hrby,hwy,show Y.getD N.iy 0=1+H by simp only [H]; ring,pdet] at e
    have : 0<(cx-(r+3/(2*D))*H)-X.getD N.xl 0 := by
      by_contra h; push Not at h; nlinarith
    have : (r+t/D)*H≤(r+3/(2*D))*H := by
      apply mul_le_mul_of_nonneg_right _ hH.le
      have : t/D≤3/(2*D) := by rw [div_le_div_iff₀ hD (by positivity)]; nlinarith
      linarith
    linarith
  have pmax : cx-(r+t/D)*H<X.getD (N.xl+1) 0 := by
    have e := L2
    rw [hra,hray,hwy,show Y.getD N.iy 0=1+H by simp only [H]; ring,pdet] at e
    have : (cx-r*H)-X.getD (N.xl+1) 0<0 := by
      by_contra h; push Not at h; nlinarith
    have : 0≤t/D*H := mul_nonneg (div_nonneg ht.1 hD.le) hH.le
    nlinarith
  have hinc : W-b*H=cx-r*H := by simpa only [H,r,d] using incidence
  have hbr' : b≤r := by simpa only [r,d] using hbr
  have hr0 : 0≤r := le_trans hb0 hbr'
  -- the cell
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have zax : 1+H≤z.2 := by
    have := lvy (by omega : y<C.ny) iyy; simp only [H]; linarith
  have zx' : z.1≤W := by have := lvx drn xdr; rw [hW] at this; linarith
  rcases nook_union (W:=W) (b:=b) (D:=D) (cx:=cx) (d:=d) (r:=r) (H:=H) (t:=t) hD hd hbr' hinc zax with hB|hRc
  · -- the base sees the point through the door
    right
    have hdl : gridPt X Y N.dl=((0:ℝ),(1:ℝ)) := by
      simp only [gridPt]; rw [hdl0,dlw,hwy]
    have hdr : gridPt X Y N.dr=(W,1) := by simp only [gridPt]; rw [hW,drw,hwy]
    have hzy : 1≤z.2 := by linarith
    have hWp : X.getD (N.xl+1) 0≤W := by rw [← hW]; exact lvx drn xldr
    have hbase : W-(b+t/D)*H≤X.getD (N.xl+1) 0 := by nlinarith
    have q0' := Quad.sound G one q0
    rw [rightQuad_real] at q0'
    have y1 : 1≤Y.getD y 0 := by have := lvy (by omega : y<C.ny) winy; rw [hwy] at this; exact this
    have cross0 : 0≤ArtGallery.det (W+b*D+t,1-D) z ((0:ℝ),(1:ℝ)) := by
      apply base_right_of (H:=H) (pmax:=X.getD (N.xl+1) 0) (x0:=X.getD x 0) (y0:=Y.getD y 0) (c:=1) (K:=0)
        hD hH hbase hWp z0 z2 y1 le_rfl hW0 (by simp)
      rw [hwy,hW] at q0'; simp only [sub_self,zero_mul,zero_div,sub_zero] at q0' ⊢; simp only [H]; linarith
    have hBy : (W+b*D+t,1-D).2<1 := by simp; linarith
    refine base_sees G sub hdl hdr hBy hdoor okB ⟨z0,z1,z2,z3⟩ hzy cross0 hB ?_
    intro e he
    obtain ⟨k,hk⟩ := zip_all lB dB e he
    simp only [bDis,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hk
    rcases hk with ⟨he2,ex,ey,eyn⟩|⟨⟨he2,ex,ey1,ey2⟩,hq⟩
    · -- above the right door corner: a shift of the union case
      have c1 : 1≤Y.getD e.1.2 0 := by have := lvy eyn (drw ▸ ey); rw [hwy] at this; exact this
      have wpt : gridPt X Y e.1=(W,Y.getD e.1.2 0) := by simp only [gridPt]; rw [ex,hW]
      simp only [Holds,he2,Bool.false_eq_true,ite_false]
      rw [wpt,det_shift (W+b*D+t,1-D) z (W,1) (W,Y.getD e.1.2 0)]
      have zB : z.1-(W+b*D+t)≤0 := by nlinarith [mul_nonneg hb0 hD.le]
      simp only
      nlinarith [mul_nonpos_of_nonpos_of_nonneg zB (sub_nonneg.2 c1)]
    · -- right of the left door corner
      have eyn : e.1.2<C.ny := by omega
      have c1 : 1≤Y.getD e.1.2 0 := by have := lvy eyn (dlw ▸ ey1); rw [hwy] at this; exact this
      have cy : Y.getD e.1.2 0≤Y.getD y 0 := lvy (by omega) ey2
      have wpt : gridPt X Y e.1=((0:ℝ),Y.getD e.1.2 0) := by simp only [gridPt]; rw [ex,hdl0]
      simp only [Holds,he2,ite_true,one_mul]
      rw [wpt]
      have qc' := Quad.sound G one qc; rw [crudeQuad_real,hwy,hW] at qc'
      have hq' := Quad.sound G one hq; rw [rightQuad_real,hwy,hW] at hq'
      apply base_right_of (H:=H) (pmax:=X.getD (N.xl+1) 0) (x0:=X.getD x 0) (y0:=Y.getD y 0) (c:=Y.getD e.1.2 0)
        (K:=50*(Y.getD e.1.2 0-1)) hD hH hbase hWp z0 z2 cy c1 hW0
      · have : H*(W-X.getD x 0)≤50 := by simp only [H]; linarith
        nlinarith [mul_le_mul_of_nonneg_right this (sub_nonneg.2 c1)]
      · have e50 : 50*(Y.getD e.1.2 0-1)/D=(Y.getD e.1.2 0-1)*(s:ℝ)^2/1001 := by
          rw [hDs]; have : (s:ℝ)≠0 := by exact_mod_cast G.pos.ne'
          field_simp; ring
        rw [e50]; simp only [H]; linarith
  · -- the receiver sees the point
    left
    rw [hrec]
    have Rseg : ((cx+d*(r+t/D),1-d):Point)∈ArtGallery.segment (gridPt X Y N.ra) (gridPt X Y N.rb) := by
      have ea : gridPt X Y N.ra=(cx+d*r,1-d) := by simp only [gridPt]; rw [hra,hray]
      have eb : gridPt X Y N.rb=(cx+d*(r+3/(2*D)),1-d) := by simp only [gridPt]; rw [hrbx,hrby]
      rw [ea,eb]; exact CopyChannel.receiver_on_spot hD ht
    refine fun p hp => sub (CertA.sound G okR Rseg ⟨z0,z1,z2,z3⟩ ?_ hp)
    intro e he
    obtain ⟨k,hk⟩ := zip_all lR dR e he
    simp only [rDis,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hk
    have zR : 0<z.2-(1-d) := by linarith
    rcases hk with ⟨he2,ey,ex,exn⟩|⟨⟨he2,ey,ex,eyn⟩,hq⟩
    · -- on the window line left of the corner
      have wx : X.getD e.1.1 0≤cx := lvx winn ex
      have wpt : gridPt X Y e.1=(X.getD e.1.1 0,1) := by simp only [gridPt]; rw [ey,hwy]
      simp only [Holds,he2,ite_true,one_mul]
      rw [wpt,det_shift (cx+d*(r+t/D),1-d) z (cx,1) (X.getD e.1.1 0,1)]
      simp only [sub_self,mul_zero,add_zero]
      nlinarith [mul_nonneg (sub_nonneg.2 wx) zR.le]
    · -- above the window line left of the corner
      have wx : X.getD e.1.1 0≤cx := lvx winn ex
      have wy : 1≤Y.getD e.1.2 0 := by have := lvy eyn ey; rw [hwy] at this; exact this
      simp only [Holds,he2,Bool.false_eq_true,ite_false]
      have hq' := Quad.sound G one hq; rw [belowQuad_real,hwy] at hq'
      have lt := receiver_below (cx:=cx) (d:=d) (ρ:=r+t/D) (ρmax:=r+3/(2*D)) (H:=H) (pmin:=X.getD N.xl 0)
        (x1:=X.getD x' 0) (y1:=Y.getD y' 0) (RxMin:=X.getD N.ra.1 0) (w:=gridPt X Y e.1) (z:=z) hd
        (by have := div_nonneg ht.1 hD.le; linarith)
        (by have : t/D≤3/(2*D) := by rw [div_le_div_iff₀ hD (by positivity)]; nlinarith
            linarith) pmin z1 z3 zax (by rw [hra]; nlinarith [div_nonneg ht.1 hD.le]) (by simpa [gridPt] using wy)
        (by simpa [gridPt] using wx) (by
          simp only [gridPt]
          have e1 : d*(r+3/(2*D))=X.getD N.rb.1 0-cx := by rw [hrbx]; ring
          have : d*((X.getD x' 0-X.getD N.xl 0)+(r+3/(2*D))*(Y.getD y' 0-1-H))=
              d*(X.getD x' 0-X.getD N.xl 0)+(X.getD N.rb.1 0-cx)*(Y.getD y' 0-Y.getD N.iy 0) := by
            rw [← e1]; simp only [H]; ring
          rw [this]; simp only [d] at hq' ⊢; linarith)
      linarith

end Cell


/-! ## Chamber cells -/

/-- Grid data of the chamber of a channel: the receiver corner, the base corner, the axis. -/
structure Chamber where
  cR : Index
  cB : Index
  iy : Nat
  /-- the base rays to `(X xr, Y iy)` cross the door line left of the right door corner -/
  xr : Nat

/-- The bound of `CopyCover.receiver_right` (window corner, nook data) for the cell `[x,·]×[y,·]`. -/
def winQuad (N : Nook) (x y : Nat) : Quad :=
  [(ldiff (ly N.win.2) (ly N.ra.2),ldiff (lx x) (lx (N.xl+1))),
   (ldiff (lx N.ra.1) (lx N.win.1),ldiff (ly y) (ly N.iy))]

/-- The bound of `CopyCover.base_left_of` (right door corner, nook data) for the cell `[·,x']×[·,y']`. -/
def leftQuad (N : Nook) (x' y' : Nat) : Quad :=
  [(ldiff (ly N.iy) (ly N.win.2),ldiff (lx N.xl) (lx x')),
   (lneg (ldiff (lx N.dr.1) (lx N.xl)),ldiff (ly y') (ly N.iy))]

/-- The slope order of the base and receiver rays, with `b ≤ bhi` and the crude bound
`W + 3/2 - X cB ≤ 12`. -/
def slopeQuad (N : Nook) (Ch : Chamber) (bhi : ℚ) : Quad :=
  [(ldiff (lx N.ra.1) (lx Ch.cR.1),[⟨1,0,.one⟩]),
   ([⟨-bhi,0,.one⟩],ldiff (ly Ch.cR.2) (ly N.ra.2)),
   ([⟨-12/50050,2,.one⟩],ldiff (ly Ch.cR.2) (ly N.ra.2))]

def crude2Quad (N : Nook) (Ch : Chamber) : Quad :=
  [([⟨10,0,.one⟩],[⟨1,0,.one⟩]),(lneg (ldiff (lx N.dr.1) (lx Ch.cB.1)),[⟨1,0,.one⟩])]

section Reals
variable {X Y : List ℝ} {s : ℝ}

theorem winQuad_real (N : Nook) (x y : Nat) :
    (winQuad N x y).real X Y s=(Y.getD N.win.2 0-Y.getD N.ra.2 0)*(X.getD x 0-X.getD (N.xl+1) 0)+
      (X.getD N.ra.1 0-X.getD N.win.1 0)*(Y.getD y 0-Y.getD N.iy 0) := by
  simp [winQuad,Quad.real]

theorem leftQuad_real (N : Nook) (x' y' : Nat) :
    (leftQuad N x' y').real X Y s=(Y.getD N.iy 0-Y.getD N.win.2 0)*(X.getD N.xl 0-X.getD x' 0)-
      (X.getD N.dr.1 0-X.getD N.xl 0)*(Y.getD y' 0-Y.getD N.iy 0) := by
  simp [leftQuad,Quad.real]; ring

theorem slopeQuad_real (N : Nook) (Ch : Chamber) (bhi : ℚ) :
    (slopeQuad N Ch bhi).real X Y s=(X.getD N.ra.1 0-X.getD Ch.cR.1 0)-(bhi:ℝ)*(Y.getD Ch.cR.2 0-Y.getD N.ra.2 0)-
      12*s^2/50050*(Y.getD Ch.cR.2 0-Y.getD N.ra.2 0) := by
  simp only [slopeQuad,Quad.real,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ldiff_real,lx_real,ly_real]
  simp [Lin.real,Atom.real]; ring

theorem crude2Quad_real (N : Nook) (Ch : Chamber) :
    (crude2Quad N Ch).real X Y s=10-(X.getD N.dr.1 0-X.getD Ch.cB.1 0) := by
  simp only [crude2Quad,Quad.real,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ldiff_real,lx_real,ly_real,
    lneg_real]
  simp [Lin.real,Atom.real]; ring

end Reals

/-- Assumed ends of a receiver certificate of a chamber cell. -/
def rDisC (C : Chart) (N : Nook) (Ch : Chamber) (x' y' : Nat) (e : Index × Bool) (k : Nat) : Bool :=
  (e.2 && decide (e.1.2=N.win.2 ∧ e.1.1≤N.win.1 ∧ e.1.1<C.nx)) ||
  (!e.2 && decide (N.win.2≤e.1.2 ∧ e.1.1≤N.win.1 ∧ e.1.2<C.ny) && (belowQuad N x' y' e.1).ok C k) ||
  (!e.2 && decide (e.1.1=Ch.cR.1 ∧ Ch.cR.2≤e.1.2 ∧ e.1.2<C.ny)) ||
  (!e.2 && decide (e.1.2=Ch.cR.2 ∧ Ch.cR.1≤e.1.1 ∧ e.1.1<C.nx))

/-- Assumed ends of a door certificate of a chamber cell. -/
def bDisC (C : Chart) (N : Nook) (Ch : Chamber) (x y : Nat) (e : Index × Bool) (k : Nat) : Bool :=
  (e.2 && decide (e.1.1=Ch.cB.1 ∧ e.1.2≤Ch.cB.2)) ||
  (e.2 && decide (e.1.2=Ch.cB.2 ∧ e.1.1≤Ch.cB.1)) ||
  (!e.2 && decide (e.1.1=N.dr.1 ∧ N.dr.2≤e.1.2 ∧ e.1.2<C.ny)) ||
  (e.2 && decide (e.1.1=N.dl.1 ∧ N.dl.2≤e.1.2 ∧ e.1.2≤y) && (rightQuad N x y e.1.2).ok C k)

/-- The checks of a chamber cell `[x,x']×[y,y']`. -/
def chamberOK (C : Chart) (N : Nook) (Ch : Chamber) (x x' y y' : Nat) (cR cB : CertA) (hR hB : List Nat)
    (bhi : ℚ) (k0 kc kw ks kc2 : Nat) : Bool :=
  cR.ok C N.ra N.rb x x' y y' && cB.ok C N.dl N.dr x x' y y' &&
  decide (hR.length=cR.assumed.length) && (cR.assumed.zip hR).all (fun p => rDisC C N Ch x' y' p.1 p.2) &&
  decide (hB.length=cB.assumed.length) && (cB.assumed.zip hB).all (fun p => bDisC C N Ch x y p.1 p.2) &&
  (rightQuad N x y N.win.2).ok C k0 && (crudeQuad N x).ok C kc && (winQuad N x y).ok C kw &&
  (slopeQuad N Ch bhi).ok C ks && (crude2Quad N Ch).ok C kc2 &&
  decide (N.iy≤y ∧ y'≤Ch.iy ∧ x'≤N.dr.1 ∧ N.xl+1≤N.dr.1 ∧ N.win.2≤y ∧ N.dl.2=N.win.2 ∧ N.dr.2=N.win.2 ∧
    N.ra.2<N.win.2 ∧ N.rb.2=N.ra.2 ∧ N.win.2<N.iy ∧ x'≤N.win.1 ∧ N.dr.1<C.nx ∧ N.win.1<C.nx ∧ N.iy<C.ny ∧
    N.xl+1<C.nx ∧ N.ra.1<C.nx ∧ N.rb.1<C.nx ∧ N.ra.2<C.ny ∧ N.win.2<C.ny ∧ x'<C.nx ∧ y'<C.ny ∧ y<y' ∧
    Ch.iy<C.ny ∧ Ch.cR.1<C.nx ∧ Ch.cR.2<C.ny ∧ Ch.cB.1<C.nx ∧ Ch.cB.2<C.ny ∧ N.ra.2<Ch.cR.2 ∧ N.win.2<Ch.cB.2 ∧
    x'≤Ch.cR.1 ∧ N.win.1≤N.ra.1 ∧ x'≤Ch.xr ∧ Ch.xr<C.nx)


section ChamberCell
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

set_option maxHeartbeats 20000000 in
/-- A chamber cell below the chamber axis (and above the nook axis) is seen by the receiver or by
the base guard (matched values). -/
theorem chamber_cell (G : Good C X Y s A) (one : A 0=1) {P : Polygon} (sub : (C.poly X Y).filled⊆P.filled)
    {N : Nook} {Ch : Chamber} {x x' y y' : Nat} {cR cB : CertA} {hR hB : List Nat} {bhi : ℚ}
    {k0 kc kw ks kc2 : Nat}
    (ok : chamberOK C N Ch x x' y y' cR cB hR hB bhi k0 kc kw ks kc2=true)
    {W b D t : ℝ} (hD : 0<D) (hW0 : 0≤W) (hDs : D=50050/(s:ℝ)^2) (hW : X.getD N.dr.1 0=W) (hdl0 : X.getD N.dl.1 0=0)
    (hwy : Y.getD N.win.2 0=1)
    (hrb : X.getD N.rb.1 0=X.getD N.ra.1 0+3/2*(1-Y.getD N.ra.2 0)/D)
    (L1 : 0<ArtGallery.det (X.getD N.rb.1 0,Y.getD N.rb.2 0) (X.getD N.win.1 0,Y.getD N.win.2 0) (X.getD N.xl 0,Y.getD N.iy 0))
    (L2 : ArtGallery.det (X.getD N.ra.1 0,Y.getD N.ra.2 0) (X.getD N.win.1 0,Y.getD N.win.2 0)
      (X.getD (N.xl+1) 0,Y.getD N.iy 0)<0)
    (incidence : W-b*(Y.getD N.iy 0-1)=X.getD N.win.1 0-
      ((X.getD N.ra.1 0-X.getD N.win.1 0)/(1-Y.getD N.ra.2 0))*(Y.getD N.iy 0-1))
    (matched : CopyChannel.lineX (W+b*D+t,1-D) (X.getD Ch.cB.1 0,Y.getD Ch.cB.2 0) (Y.getD Ch.iy 0)=
      CopyChannel.lineX (X.getD N.ra.1 0+2/3*(X.getD N.rb.1 0-X.getD N.ra.1 0)*t,Y.getD N.ra.2 0)
        (X.getD Ch.cR.1 0,Y.getD Ch.cR.2 0) (Y.getD Ch.iy 0))
    (hb0 : 0≤b) (hbhi : b≤bhi) (hBlow : 1-D<Y.getD Ch.cB.2 0)
    (CW0 : ArtGallery.det (W+b*D,1-D) (X.getD Ch.xr 0,Y.getD Ch.iy 0) (W,1)<0)
    (CW1 : ArtGallery.det (W+b*D+3/2,1-D) (X.getD Ch.xr 0,Y.getD Ch.iy 0) (W,1)<0)
    (ht : 0≤t ∧ t≤3/2) (hdoor : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b*D+t,1-D) d)
    {z : Point} (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    P.Sees (CopyLower.receiver X Y N.ra N.rb t) z ∨ P.Sees (W+b*D+t,1-D) z := by
  simp only [chamberOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨okR,okB⟩,lR⟩,dR⟩,lB⟩,dB⟩,q0⟩,qc⟩,qw⟩,qs⟩,qc2⟩,ix⟩ := ok
  obtain ⟨iyy,y'iy,xdr,xldr,winy,dlw,drw,raw,rbra,winiy,xwin,drn,winn,iyn,xln,ran,rbn,rayn,winyn,x'n,y'n,yy',
    chn,cR1n,cR2n,cB1n,cB2n,racR,wincB,x'cR,winra,x'xr,xrn⟩ := ix
  have lx := G.lx; have ly := G.ly
  have lvx {i j : Nat} (hj : j<C.nx) (h : i≤j) := lev_le G.hx (by omega : j<X.length) h
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  have lty {i j : Nat} (hj : j<C.ny) (h : i<j) := SepGeom.level_lt G.hy (by omega : j<Y.length) h
  set cx := X.getD N.win.1 0 with hcx
  set d := 1-Y.getD N.ra.2 0 with hd'
  have hd : 0<d := by have := lty winyn raw; rw [hwy] at this; simp only [d]; linarith
  set r := (X.getD N.ra.1 0-cx)/d with hr'
  set H := Y.getD N.iy 0-1 with hH'
  have hH : 0<H := by have := lty iyn winiy; rw [hwy] at this; simp only [H]; linarith
  have hra : X.getD N.ra.1 0=cx+d*r := by simp only [r]; field_simp; ring
  have hr0 : 0≤r := by
    have : cx≤X.getD N.ra.1 0 := lvx ran winra
    simp only [r]; exact div_nonneg (by linarith) hd.le
  have hrbx : X.getD N.rb.1 0=cx+d*(r+3/(2*D)) := by rw [hrb,hra]; field_simp; ring
  have hrby : Y.getD N.rb.2 0=1-d := by rw [rbra]; simp only [d]; ring
  have hray : Y.getD N.ra.2 0=1-d := by simp only [d]; ring
  have hrec : CopyLower.receiver X Y N.ra N.rb t=(cx+d*(r+t/D),1-d) := by
    simp only [CopyLower.receiver,gridPt]
    rw [hrbx,hra,hray]; ext <;> simp <;> field_simp <;> ring
  have pdet (ρ q : ℝ) : ArtGallery.det (cx+d*ρ,1-d) (cx,1) (q,1+H)=d*((cx-ρ*H)-q) := by
    simp only [ArtGallery.det]; ring
  have htD : t/D≤3/(2*D) := by rw [div_le_div_iff₀ hD (by positivity)]; nlinarith
  have htD0 : 0≤t/D := div_nonneg ht.1 hD.le
  have pmin : X.getD N.xl 0≤cx-(r+t/D)*H := by
    have e := L1
    rw [hrbx,hrby,hwy,show Y.getD N.iy 0=1+H by simp only [H]; ring,pdet] at e
    have : 0<(cx-(r+3/(2*D))*H)-X.getD N.xl 0 := by
      by_contra h; push Not at h; nlinarith
    have : (r+t/D)*H≤(r+3/(2*D))*H := mul_le_mul_of_nonneg_right (by linarith) hH.le
    linarith
  have pmax : cx-(r+t/D)*H<X.getD (N.xl+1) 0 := by
    have e := L2
    rw [hra,hray,hwy,show Y.getD N.iy 0=1+H by simp only [H]; ring,pdet] at e
    have : (cx-r*H)-X.getD (N.xl+1) 0<0 := by
      by_contra h; push Not at h; nlinarith
    have : 0≤t/D*H := mul_nonneg htD0 hH.le
    nlinarith
  have hinc : W-b*H=cx-r*H := by simpa only [H,r,d] using incidence
  have hbase : W-(b+t/D)*H≤X.getD (N.xl+1) 0 := by nlinarith
  have hbase' : X.getD N.xl 0≤W-(b+t/D)*H := by nlinarith
  -- quads
  have qs' := Quad.sound G one qs; rw [slopeQuad_real] at qs'
  have qc2' := Quad.sound G one qc2; rw [crude2Quad_real,hW] at qc2'
  have hF : 0<Y.getD Ch.cR.2 0-(1-d) := by have := lty cR2n racR; rw [hray] at this; linarith
  have hbhi0 : (0:ℝ)≤bhi := le_trans hb0 hbhi
  have raCR : X.getD Ch.cR.1 0≤X.getD N.ra.1 0 := by
    rw [hray] at qs'
    nlinarith [mul_nonneg hbhi0 hF.le, sq_nonneg (s:ℝ)]
  -- the cell
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have zax : 1+H≤z.2 := by have := lvy (by omega : y<C.ny) iyy; simp only [H]; linarith
  have zch : z.2≤Y.getD Ch.iy 0 := by have := lvy chn y'iy; linarith
  have zW : z.1≤W := by have := lvx drn xdr; rw [hW] at this; linarith
  have zcR : z.1≤X.getD Ch.cR.1 0 := by have := lvx cR1n x'cR; linarith
  have cB1 : 1≤Y.getD Ch.cB.2 0 := by have := lvy cB2n wincB.le; rw [hwy] at this; exact this
  rcases chamber_union (B:=(W+b*D+t,1-D)) (R:=(cx+d*(r+t/D),1-d)) (cB:=(X.getD Ch.cB.1 0,Y.getD Ch.cB.2 0))
      (cR:=(X.getD Ch.cR.1 0,Y.getD Ch.cR.2 0)) (z:=z) (Ya:=Y.getD Ch.iy 0) hBlow
      (by simp only; linarith)
      (by
        have hRpt : ((X.getD N.ra.1 0+2/3*(X.getD N.rb.1 0-X.getD N.ra.1 0)*t,Y.getD N.ra.2 0):Point)=
            (cx+d*(r+t/D),1-d) := by
          rw [hrbx,hra,hray]; ext <;> simp only <;> field_simp <;> ring
        rw [matched,hRpt])
      (by
        simp only
        have A1 : X.getD N.ra.1 0-X.getD Ch.cR.1 0≤cx+d*(r+t/D)-X.getD Ch.cR.1 0 := by
          rw [hra]; nlinarith
        have E1 : D≤Y.getD Ch.cB.2 0-(1-D) := by linarith
        have G1 : -(b*D)-12≤X.getD Ch.cB.1 0-(W+b*D+t) := by linarith
        have key : (X.getD N.ra.1 0-X.getD Ch.cR.1 0)*D-b*D*(Y.getD Ch.cR.2 0-(1-d))-12*(Y.getD Ch.cR.2 0-(1-d))≥0 := by
          rw [hray] at qs'
          have hs : (0:ℝ)<s := by exact_mod_cast G.pos
          have e : D*((s:ℝ)^2/50050)=1 := by rw [hDs]; field_simp
          have : D*((X.getD N.ra.1 0-X.getD Ch.cR.1 0)-bhi*(Y.getD Ch.cR.2 0-(1-d))-
              12*(s:ℝ)^2/50050*(Y.getD Ch.cR.2 0-(1-d)))≥0 := mul_nonneg hD.le qs'.le
          have hb' : b*D*(Y.getD Ch.cR.2 0-(1-d))≤bhi*D*(Y.getD Ch.cR.2 0-(1-d)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbhi hD.le) hF.le
          nlinarith
        nlinarith [mul_le_mul A1 E1 hD.le (by linarith), mul_le_mul_of_nonneg_right G1 hF.le])
      zch with hBc|hRc
  · -- the base sees the point through the door
    right
    have hdl : gridPt X Y N.dl=((0:ℝ),(1:ℝ)) := by simp only [gridPt]; rw [hdl0,dlw,hwy]
    have hdr : gridPt X Y N.dr=(W,1) := by simp only [gridPt]; rw [hW,drw,hwy]
    have hzy : 1≤z.2 := by linarith
    have hWp : X.getD (N.xl+1) 0≤W := by rw [← hW]; exact lvx drn xldr
    have q0' := Quad.sound G one q0
    rw [rightQuad_real] at q0'
    have y1 : 1≤Y.getD y 0 := by have := lvy (by omega : y<C.ny) winy; rw [hwy] at this; exact this
    have cross0 : 0≤ArtGallery.det (W+b*D+t,1-D) z ((0:ℝ),(1:ℝ)) := by
      apply base_right_of (H:=H) (pmax:=X.getD (N.xl+1) 0) (x0:=X.getD x 0) (y0:=Y.getD y 0) (c:=1) (K:=0)
        hD hH hbase hWp z0 z2 y1 le_rfl hW0 (by simp)
      rw [hwy,hW] at q0'; simp only [sub_self,zero_mul,zero_div,sub_zero] at q0' ⊢; simp only [H]; linarith
    have crossW : ArtGallery.det (W+b*D+t,1-D) z (W,1)≤0 := by
      have zq1 : z.1≤X.getD Ch.xr 0 := by have := lvx xrn x'xr; linarith
      have zq2 : z.2≤Y.getD Ch.iy 0 := zch
      have hq : ArtGallery.det (W+b*D+t,1-D) (X.getD Ch.xr 0,Y.getD Ch.iy 0) (W,1)<0 := by
        have e : ArtGallery.det (W+b*D+t,1-D) (X.getD Ch.xr 0,Y.getD Ch.iy 0) (W,1)=
            (1-2*t/3)*ArtGallery.det (W+b*D,1-D) (X.getD Ch.xr 0,Y.getD Ch.iy 0) (W,1)+
              (2*t/3)*ArtGallery.det (W+b*D+3/2,1-D) (X.getD Ch.xr 0,Y.getD Ch.iy 0) (W,1) := by
          simp only [ArtGallery.det]; ring
        rw [e]
        rcases eq_or_lt_of_le ht.1 with h0|h0
        · rw [← h0]; simp only [mul_zero,zero_div,sub_zero,one_mul,zero_mul,add_zero]; exact CW0
        · nlinarith [mul_neg_of_pos_of_neg (by linarith : 0<2*t/3) CW1,
            mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤1-2*t/3) CW0.le]
      have e : ArtGallery.det (W+b*D+t,1-D) z (W,1)=ArtGallery.det (W+b*D+t,1-D) (X.getD Ch.xr 0,Y.getD Ch.iy 0) (W,1)+
          (z.1-X.getD Ch.xr 0)*D+(b*D+t)*(z.2-Y.getD Ch.iy 0) := by
        simp only [ArtGallery.det]; ring
      rw [e]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : z.1-X.getD Ch.xr 0≤0) hD.le,
        mul_nonpos_of_nonneg_of_nonpos (by nlinarith [mul_nonneg hb0 hD.le] : 0≤b*D+t) (by linarith : z.2-Y.getD Ch.iy 0≤0)]
    have hBy : (W+b*D+t,1-D).2<1 := by simp; linarith
    refine base_sees G sub hdl hdr hBy hdoor okB ⟨z0,z1,z2,z3⟩ hzy cross0 crossW ?_
    intro e he
    obtain ⟨k,hk⟩ := zip_all lB dB e he
    simp only [bDisC,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hk
    have zB : z.1-(W+b*D+t)≤0 := by nlinarith [mul_nonneg hb0 hD.le]
    have zBy : 0≤z.2-(1-D) := by linarith
    rcases hk with (((⟨he2,ex,ey⟩|⟨he2,ey,ex⟩)|⟨he2,ex,ey,eyn⟩)|⟨⟨he2,ex,ey1,ey2⟩,hq⟩)
    · -- a column shift of the base corner
      have wpt : gridPt X Y e.1=(X.getD Ch.cB.1 0,Y.getD e.1.2 0) := by simp only [gridPt]; rw [ex]
      simp only [Holds,he2,ite_true,one_mul]
      rw [wpt]
      have hc := det_col (W+b*D+t,1-D) z (X.getD Ch.cB.1 0,Y.getD Ch.cB.2 0) (Y.getD e.1.2 0)
      have : Y.getD e.1.2 0≤Y.getD Ch.cB.2 0 := lvy cB2n ey
      have m := mul_nonneg_of_nonpos_of_nonpos zB (by linarith : Y.getD e.1.2 0-Y.getD Ch.cB.2 0≤0)
      dsimp only at hc hBc m ⊢
      rw [hc]; linarith
    · -- a row shift of the base corner
      have wpt : gridPt X Y e.1=(X.getD e.1.1 0,Y.getD Ch.cB.2 0) := by simp only [gridPt]; rw [ey]
      simp only [Holds,he2,ite_true,one_mul]
      rw [wpt]
      have hc := det_row (W+b*D+t,1-D) z (X.getD Ch.cB.1 0,Y.getD Ch.cB.2 0) (X.getD e.1.1 0)
      have : X.getD e.1.1 0≤X.getD Ch.cB.1 0 := lvx cB1n ex
      have m := mul_nonneg (by linarith : 0≤X.getD Ch.cB.1 0-X.getD e.1.1 0) zBy
      dsimp only at hc hBc m ⊢
      rw [hc]; nlinarith
    · -- above the right door corner
      have c1 : 1≤Y.getD e.1.2 0 := by have := lvy eyn (drw ▸ ey); rw [hwy] at this; exact this
      have wpt : gridPt X Y e.1=(W,Y.getD e.1.2 0) := by simp only [gridPt]; rw [ex,hW]
      simp only [Holds,he2,Bool.false_eq_true,ite_false]
      rw [wpt,det_shift (W+b*D+t,1-D) z (W,1) (W,Y.getD e.1.2 0)]
      simp only
      nlinarith [mul_nonpos_of_nonpos_of_nonneg zB (sub_nonneg.2 c1)]
    · -- right of the left door corner
      have eyn : e.1.2<C.ny := by omega
      have c1 : 1≤Y.getD e.1.2 0 := by have := lvy eyn (dlw ▸ ey1); rw [hwy] at this; exact this
      have cy : Y.getD e.1.2 0≤Y.getD y 0 := lvy (by omega) ey2
      have wpt : gridPt X Y e.1=((0:ℝ),Y.getD e.1.2 0) := by simp only [gridPt]; rw [ex,hdl0]
      simp only [Holds,he2,ite_true,one_mul]
      rw [wpt]
      have qc' := Quad.sound G one qc; rw [crudeQuad_real,hwy,hW] at qc'
      have hq' := Quad.sound G one hq; rw [rightQuad_real,hwy,hW] at hq'
      apply base_right_of (H:=H) (pmax:=X.getD (N.xl+1) 0) (x0:=X.getD x 0) (y0:=Y.getD y 0) (c:=Y.getD e.1.2 0)
        (K:=50*(Y.getD e.1.2 0-1)) hD hH hbase hWp z0 z2 cy c1 hW0
      · have : H*(W-X.getD x 0)≤50 := by simp only [H]; linarith
        nlinarith [mul_le_mul_of_nonneg_right this (sub_nonneg.2 c1)]
      · have e50 : 50*(Y.getD e.1.2 0-1)/D=(Y.getD e.1.2 0-1)*(s:ℝ)^2/1001 := by
          rw [hDs]; have : (s:ℝ)≠0 := by exact_mod_cast G.pos.ne'
          field_simp; ring
        rw [e50]; simp only [H]; linarith
  · -- the receiver sees the point
    left
    rw [hrec]
    have Rseg : ((cx+d*(r+t/D),1-d):Point)∈ArtGallery.segment (gridPt X Y N.ra) (gridPt X Y N.rb) := by
      have ea : gridPt X Y N.ra=(cx+d*r,1-d) := by simp only [gridPt]; rw [hra,hray]
      have eb : gridPt X Y N.rb=(cx+d*(r+3/(2*D)),1-d) := by simp only [gridPt]; rw [hrbx,hrby]
      rw [ea,eb]; exact CopyChannel.receiver_on_spot hD ht
    refine fun p hp => sub (CertA.sound G okR Rseg ⟨z0,z1,z2,z3⟩ ?_ hp)
    intro e he
    obtain ⟨k,hk⟩ := zip_all lR dR e he
    simp only [rDisC,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hk
    have zR : 0<z.2-(1-d) := by linarith
    have zRx : z.1-(cx+d*(r+t/D))≤0 := by
      have h1 : cx+d*r≤cx+d*(r+t/D) := by nlinarith [mul_nonneg hd.le htD0]
      have h2 : X.getD Ch.cR.1 0≤cx+d*r := hra ▸ raCR
      linarith
    have qw' := Quad.sound G one qw; rw [winQuad_real,hwy] at qw'
    have hy0 : 1+H≤Y.getD y 0 := by have := lvy (by omega : y<C.ny) iyy; simp only [H]; linarith
    have bw : 0<d*(X.getD x 0-X.getD (N.xl+1) 0)+d*r*(Y.getD y 0-1-H) := by
      have e1 : d*r=X.getD N.ra.1 0-cx := by rw [hra]; ring
      rw [e1]
      have e2 : Y.getD y 0-1-H=Y.getD y 0-Y.getD N.iy 0 := by simp only [H]; ring
      rw [e2]; simpa only [d] using qw'
    have hwin : 0≤ArtGallery.det (cx+d*(r+t/D),1-d) z (cx,1) :=
      receiver_right (r:=r) (pmax:=X.getD (N.xl+1) 0) (x0:=X.getD x 0) (y0:=Y.getD y 0) hd
        (le_add_of_nonneg_right htD0) pmax.le z0 z2 hy0 hr0 bw
    rcases hk with (((⟨he2,ey,ex,exn⟩|⟨⟨he2,ey,ex,eyn⟩,hq⟩)|⟨he2,ex,ey,eyn⟩)|⟨he2,ey,ex,exn⟩)
    · -- on the window line left of the corner
      have wx : X.getD e.1.1 0≤cx := lvx winn ex
      have wpt : gridPt X Y e.1=(X.getD e.1.1 0,1) := by simp only [gridPt]; rw [ey,hwy]
      simp only [Holds,he2,ite_true,one_mul]
      rw [wpt,det_shift (cx+d*(r+t/D),1-d) z (cx,1) (X.getD e.1.1 0,1)]
      simp only [sub_self,mul_zero,add_zero]
      nlinarith [mul_nonneg (sub_nonneg.2 wx) zR.le]
    · -- above the window line left of the corner
      have wx : X.getD e.1.1 0≤cx := lvx winn ex
      have wy : 1≤Y.getD e.1.2 0 := by have := lvy eyn ey; rw [hwy] at this; exact this
      simp only [Holds,he2,Bool.false_eq_true,ite_false]
      have hq' := Quad.sound G one hq; rw [belowQuad_real,hwy] at hq'
      have lt := receiver_below (cx:=cx) (d:=d) (ρ:=r+t/D) (ρmax:=r+3/(2*D)) (H:=H) (pmin:=X.getD N.xl 0)
        (x1:=X.getD x' 0) (y1:=Y.getD y' 0) (RxMin:=X.getD N.ra.1 0) (w:=gridPt X Y e.1) (z:=z) hd
        (by linarith) (by linarith) pmin z1 z3 zax
        (by rw [hra]; nlinarith [mul_nonneg hd.le htD0]) (by simpa [gridPt] using wy)
        (by simpa [gridPt] using wx) (by
          simp only [gridPt]
          have e1 : d*(r+3/(2*D))=X.getD N.rb.1 0-cx := by rw [hrbx]; ring
          have : d*((X.getD x' 0-X.getD N.xl 0)+(r+3/(2*D))*(Y.getD y' 0-1-H))=
              d*(X.getD x' 0-X.getD N.xl 0)+(X.getD N.rb.1 0-cx)*(Y.getD y' 0-Y.getD N.iy 0) := by
            rw [← e1]; simp only [H]; ring
          rw [this]; simp only [d] at hq' ⊢; linarith)
      linarith
    · -- a column shift of the receiver corner
      have wpt : gridPt X Y e.1=(X.getD Ch.cR.1 0,Y.getD e.1.2 0) := by simp only [gridPt]; rw [ex]
      simp only [Holds,he2,Bool.false_eq_true,ite_false]
      rw [wpt]
      have hc := det_col (cx+d*(r+t/D),1-d) z (X.getD Ch.cR.1 0,Y.getD Ch.cR.2 0) (Y.getD e.1.2 0)
      have : Y.getD Ch.cR.2 0≤Y.getD e.1.2 0 := lvy eyn ey
      have m := mul_nonpos_of_nonpos_of_nonneg zRx (by linarith : 0≤Y.getD e.1.2 0-Y.getD Ch.cR.2 0)
      dsimp only at hc hRc m ⊢
      rw [hc]; linarith
    · -- a row shift of the receiver corner
      have wpt : gridPt X Y e.1=(X.getD e.1.1 0,Y.getD Ch.cR.2 0) := by simp only [gridPt]; rw [ey]
      simp only [Holds,he2,Bool.false_eq_true,ite_false]
      rw [wpt]
      have hc := det_row (cx+d*(r+t/D),1-d) z (X.getD Ch.cR.1 0,Y.getD Ch.cR.2 0) (X.getD e.1.1 0)
      have : X.getD Ch.cR.1 0≤X.getD e.1.1 0 := lvx exn ex
      have m := mul_nonneg (by linarith : 0≤X.getD e.1.1 0-X.getD Ch.cR.1 0) zR.le
      dsimp only at hc hRc m ⊢
      rw [hc]; nlinarith

end ChamberCell

end ArtGallery.Orthogonal.BoundaryPoint.NookCell
end
