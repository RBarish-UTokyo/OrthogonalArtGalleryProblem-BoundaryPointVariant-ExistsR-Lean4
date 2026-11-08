module

public import ArtGallery.Orthogonal.BoundaryPoint.CoverChain

/-! # Chain certificates with assumed window ends

A chain certificate (`CoverChain`) whose windows may leave the sign at an end unchecked: that
sign is then a hypothesis on the sightline (an open half-plane condition of the guard and the
target). Special cells are covered by several such certificates whose conditions together hold
for every target, by an argument outside the chart (a copy incidence or a margin). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CoverAssume
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert RegisterForm MarginCert CoverChain ArtGallery.Orthogonal.Hard

section Sound
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

set_option maxHeartbeats 4000000 in
/-- A sightline meets a window of two consecutive tiles once it has the window signs. -/
theorem meet_core (G : Good C X Y s A) {g₀ g₁ : Index} {x x' y y' : Nat} {w : Win}
    {a b : CorridorProgram.Rect Nat}
    (ha : a.1<X.length ∧ a.2.1<X.length ∧ a.2.2.1<Y.length ∧ a.2.2.2<Y.length)
    (hb : b.1<X.length ∧ b.2.1<X.length ∧ b.2.2.1<Y.length ∧ b.2.2.2<Y.length)
    (hp : w.place a b=true) (hs : w.sep g₀ g₁ x x' y y'=true)
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0))
    (sLo : 0≤(if w.posLo then 1 else -1)*ArtGallery.det g z (gridPt X Y w.lo'))
    (sHi : 0≤(if !w.posLo then 1 else -1)*ArtGallery.det g z (gridPt X Y w.hi')) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ Geometry.lerp g z t∈realRect X Y a∩realRect X Y b := by
  obtain ⟨r0x,r0y,r1x,r1y,rx,ry⟩ := rg
  have lx := G.lx; have ly := G.ly
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have c1 (v : ℝ) := seg_coord hg Prod.fst (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  have c2 (v : ℝ) := seg_coord hg Prod.snd (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  simp only [gridPt] at c1 c2
  have lvx {i j : Nat} (hj : j<C.nx) (h : i≤j) := lev_le G.hx (by omega : j<X.length) h
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  have ltx {i j : Nat} (hj : j<C.nx) (h : i<j) := SepGeom.level_lt G.hx (by omega : j<X.length) h
  have lty {i j : Nat} (hj : j<C.ny) (h : i<j) := SepGeom.level_lt G.hy (by omega : j<Y.length) h
  have ax2 : a.2.1<C.nx := by rw [← lx]; exact ha.2.1
  have ay2 : a.2.2.2<C.ny := by rw [← ly]; exact ha.2.2.2
  have bx2 : b.2.1<C.nx := by rw [← lx]; exact hb.2.1
  have by2 : b.2.2.2<C.ny := by rw [← ly]; exact hb.2.2.2
  rcases w with ⟨vert,dir,c,lo,hi⟩
  cases vert <;> cases dir <;>
    simp only [Win.place,Win.sep,Win.posLo,Win.lo',Win.hi',gridPt,ite_true,ite_false,Bool.false_eq_true,
      decide_eq_true_eq,bne_self_eq_false,Bool.true_bne,Bool.false_bne,Bool.not_true,Bool.not_false] at hp hs sLo sHi
  · -- horizontal, guard above
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨v1,u0,u1,str⟩ := hs
    have hcy : c<C.ny := by omega
    have e0 := lvy r0y u0; have e1 := lvy r1y u1; have e2 := lvy hcy v1
    have gc := (c2 (Y.getD c 0)).2.2.1 e0 e1
    have strict : z.2<g.2 := by
      rcases str with st|⟨s0,s1⟩
      · have := lty hcy st; linarith
      · have := (c2 (Y.getD c 0)).2.2.2 (lty r0y s0) (lty r1y s1); linarith
    obtain ⟨t,t0,t1,ey,elo,ehi⟩ := meetH (g:=g) (z:=z) (c:=Y.getD c 0) (lo:=X.getD lo 0) (hi:=X.getD hi 0) false
      (by simp only [Bool.false_eq_true,ite_false]; exact ⟨by linarith,gc,strict⟩)
      (by simp only [Bool.false_eq_true,ite_false]; linarith) (by simp only [Bool.false_eq_true,ite_false]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · have := lvx (by omega) p5; linarith
    · have := lvx ax2 p8; linarith
    · rw [ey]; exact lvy hcy p1
    · rw [ey]; exact lvy ay2 p2
    · have := lvx (by omega) p6; linarith
    · have := lvx bx2 p9; linarith
    · rw [ey]; exact lvy hcy p3
    · rw [ey]; exact lvy by2 p4
  · -- horizontal, guard below
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨u0,u1,v1,str⟩ := hs
    have hcy : c<C.ny := by omega
    have e0 := lvy hcy u0; have e1 := lvy hcy u1; have e2 := lvy (by omega) v1
    have gc := (c2 (Y.getD c 0)).1 e0 e1
    have strict : g.2<z.2 := by
      rcases str with ⟨s0,s1⟩|st
      · have := (c2 (Y.getD c 0)).2.1 (lty hcy s0) (lty hcy s1); linarith
      · have := lty (by omega) st; linarith
    obtain ⟨t,t0,t1,ey,elo,ehi⟩ := meetH (g:=g) (z:=z) (c:=Y.getD c 0) (lo:=X.getD lo 0) (hi:=X.getD hi 0) true
      (by simp only [ite_true]; exact ⟨gc,by linarith,strict⟩)
      (by simp only [ite_true]; linarith) (by simp only [ite_true]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · have := lvx (by omega) p5; linarith
    · have := lvx ax2 p8; linarith
    · rw [ey]; exact lvy hcy p1
    · rw [ey]; exact lvy ay2 p2
    · have := lvx (by omega) p6; linarith
    · have := lvx bx2 p9; linarith
    · rw [ey]; exact lvy hcy p3
    · rw [ey]; exact lvy by2 p4
  · -- vertical, guard right
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨v1,u0,u1,str⟩ := hs
    have hcx : c<C.nx := by omega
    have e0 := lvx r0x u0; have e1 := lvx r1x u1; have e2 := lvx hcx v1
    have gc := (c1 (X.getD c 0)).2.2.1 e0 e1
    have strict : z.1<g.1 := by
      rcases str with st|⟨s0,s1⟩
      · have := ltx hcx st; linarith
      · have := (c1 (X.getD c 0)).2.2.2 (ltx r0x s0) (ltx r1x s1); linarith
    obtain ⟨t,t0,t1,ex,elo,ehi⟩ := meetV (g:=g) (z:=z) (c:=X.getD c 0) (lo:=Y.getD lo 0) (hi:=Y.getD hi 0) false
      (by simp only [Bool.false_eq_true,ite_false]; exact ⟨by linarith,gc,strict⟩)
      (by simp only [Bool.false_eq_true,ite_false]; linarith) (by simp only [Bool.false_eq_true,ite_false]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · rw [ex]; exact lvx hcx p1
    · rw [ex]; exact lvx ax2 p2
    · have := lvy (by omega) p5; linarith
    · have := lvy ay2 p8; linarith
    · rw [ex]; exact lvx hcx p3
    · rw [ex]; exact lvx bx2 p4
    · have := lvy (by omega) p6; linarith
    · have := lvy by2 p9; linarith
  · -- vertical, guard left
    obtain ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9⟩ := hp
    obtain ⟨u0,u1,v1,str⟩ := hs
    have hcx : c<C.nx := by omega
    have e0 := lvx hcx u0; have e1 := lvx hcx u1; have e2 := lvx (by omega) v1
    have gc := (c1 (X.getD c 0)).1 e0 e1
    have strict : g.1<z.1 := by
      rcases str with ⟨s0,s1⟩|st
      · have := (c1 (X.getD c 0)).2.1 (ltx hcx s0) (ltx hcx s1); linarith
      · have := ltx (by omega) st; linarith
    obtain ⟨t,t0,t1,ex,elo,ehi⟩ := meetV (g:=g) (z:=z) (c:=X.getD c 0) (lo:=Y.getD lo 0) (hi:=Y.getD hi 0) true
      (by simp only [ite_true]; exact ⟨gc,by linarith,strict⟩)
      (by simp only [ite_true]; linarith) (by simp only [ite_true]; linarith)
    refine ⟨t,t0,t1,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · rw [ex]; exact lvx hcx p1
    · rw [ex]; exact lvx ax2 p2
    · have := lvy (by omega) p5; linarith
    · have := lvy ay2 p8; linarith
    · rw [ex]; exact lvx hcx p3
    · rw [ex]; exact lvx bx2 p4
    · have := lvy (by omega) p6; linarith
    · have := lvy by2 p9; linarith


/-- A window end on the grid line of the guard segment: `det(g,z,w)` is a product of two
coordinate differences whose signs follow from the grid order. -/
def axisOK (pos : Bool) (w g₀ g₁ : Index) (x x' y y' : Nat) : Bool :=
  (decide (g₀.1=w.1 ∧ g₁.1=w.1) &&
    ((decide (w.1≤x ∧ g₀.2≤w.2 ∧ g₁.2≤w.2) && pos) ||
     (decide (w.1≤x ∧ w.2≤g₀.2 ∧ w.2≤g₁.2) && !pos) ||
     (decide (x'≤w.1 ∧ g₀.2≤w.2 ∧ g₁.2≤w.2) && !pos) ||
     (decide (x'≤w.1 ∧ w.2≤g₀.2 ∧ w.2≤g₁.2) && pos))) ||
  (decide (g₀.2=w.2 ∧ g₁.2=w.2) &&
    ((decide (g₀.1≤w.1 ∧ g₁.1≤w.1 ∧ w.2≤y) && !pos) ||
     (decide (g₀.1≤w.1 ∧ g₁.1≤w.1 ∧ y'≤w.2) && pos) ||
     (decide (w.1≤g₀.1 ∧ w.1≤g₁.1 ∧ w.2≤y) && pos) ||
     (decide (w.1≤g₀.1 ∧ w.1≤g₁.1 ∧ y'≤w.2) && !pos)))

set_option maxHeartbeats 1000000 in
theorem axis_sign (G : Good C X Y s A) {pos : Bool} {w g₀ g₁ : Index} {x x' y y' : Nat}
    (h : axisOK pos w g₀ g₁ x x' y y'=true)
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)
    (hw : w.1<C.nx ∧ w.2<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    0≤(if pos then 1 else -1)*ArtGallery.det g z (gridPt X Y w) := by
  obtain ⟨r0x,r0y,r1x,r1y,rx,ry⟩ := rg
  have lx := G.lx; have ly := G.ly
  have lvx {i j : Nat} (hj : j<C.nx) (h : i≤j) := lev_le G.hx (by omega : j<X.length) h
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  have c1 (v : ℝ) := seg_coord hg Prod.fst (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  have c2 (v : ℝ) := seg_coord hg Prod.snd (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  simp only [gridPt] at c1 c2
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have hxx : X.getD x 0≤X.getD x' 0 := lvx (by omega) (by omega)
  have hyy : Y.getD y 0≤Y.getD y' 0 := lvy (by omega) (by omega)
  simp only [ArtGallery.det,gridPt]
  simp only [axisOK,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  rcases h with ⟨⟨e0,e1⟩,h⟩|⟨⟨e0,e1⟩,h⟩
  · -- vertical line `x = X[w.1]`: det = (z.x - Xc) * (w.y - g.y)
    have gx : g.1=X.getD w.1 0 := by
      have a := (c1 (X.getD w.1 0)).1 (by rw [e0]) (by rw [e1])
      have b := (c1 (X.getD w.1 0)).2.2.1 (by rw [e0]) (by rw [e1])
      linarith
    rw [gx,sub_self,zero_mul,sub_zero]
    rcases h with ((⟨⟨a,b,c⟩,p⟩|⟨⟨a,b,c⟩,p⟩)|⟨⟨a,b,c⟩,p⟩)|⟨⟨a,b,c⟩,p⟩ <;> subst p <;> simp only [ite_true,ite_false,Bool.false_eq_true]
    · have u := lvx (by omega) a; have v := (c2 (Y.getD w.2 0)).1 (lvy hw.2 b) (lvy hw.2 c)
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤z.1-X.getD w.1 0) (by linarith : (0:ℝ)≤Y.getD w.2 0-g.2)]
    · have u := lvx (by omega) a; have v := (c2 (Y.getD w.2 0)).2.2.1 (lvy r0y b) (lvy r1y c)
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤z.1-X.getD w.1 0) (by linarith : (0:ℝ)≤g.2-Y.getD w.2 0)]
    · have u := lvx hw.1 a; have v := (c2 (Y.getD w.2 0)).1 (lvy hw.2 b) (lvy hw.2 c)
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤X.getD w.1 0-z.1) (by linarith : (0:ℝ)≤Y.getD w.2 0-g.2)]
    · have u := lvx hw.1 a; have v := (c2 (Y.getD w.2 0)).2.2.1 (lvy r0y b) (lvy r1y c)
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤X.getD w.1 0-z.1) (by linarith : (0:ℝ)≤g.2-Y.getD w.2 0)]
  · -- horizontal line `y = Y[w.2]`: det = -(w.x - g.x) * (z.y - Yc)
    have gy : g.2=Y.getD w.2 0 := by
      have a := (c2 (Y.getD w.2 0)).1 (by rw [e0]) (by rw [e1])
      have b := (c2 (Y.getD w.2 0)).2.2.1 (by rw [e0]) (by rw [e1])
      linarith
    rw [gy,sub_self,mul_zero,zero_sub]
    rcases h with ((⟨⟨a,b,c⟩,p⟩|⟨⟨a,b,c⟩,p⟩)|⟨⟨a,b,c⟩,p⟩)|⟨⟨a,b,c⟩,p⟩ <;> subst p <;> simp only [ite_true,ite_false,Bool.false_eq_true]
    · have u := (c1 (X.getD w.1 0)).1 (lvx hw.1 a) (lvx hw.1 b); have v := lvy (by omega) c
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤X.getD w.1 0-g.1) (by linarith : (0:ℝ)≤z.2-Y.getD w.2 0)]
    · have u := (c1 (X.getD w.1 0)).1 (lvx hw.1 a) (lvx hw.1 b); have v := lvy hw.2 c
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤X.getD w.1 0-g.1) (by linarith : (0:ℝ)≤Y.getD w.2 0-z.2)]
    · have u := (c1 (X.getD w.1 0)).2.2.1 (lvx r0x a) (lvx r1x b); have v := lvy (by omega) c
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤g.1-X.getD w.1 0) (by linarith : (0:ℝ)≤z.2-Y.getD w.2 0)]
    · have u := (c1 (X.getD w.1 0)).2.2.1 (lvx r0x a) (lvx r1x b); have v := lvy hw.2 c
      nlinarith [mul_nonneg (by linarith : (0:ℝ)≤g.1-X.getD w.1 0) (by linarith : (0:ℝ)≤Y.getD w.2 0-z.2)]

/-- A window whose end signs are certified at the eight pairs (mode `0`), assumed of the
sightline (mode `1`), or decided by the grid order on a common grid line (mode `2`). -/
structure WinA where
  w : Win
  ss : List Sign
  mLo : Nat
  mHi : Nat

def endOK (C : Chart) (m : Nat) (pos : Bool) (v g₀ g₁ : Index) (x x' y y' : Nat) (ss : List Sign) (off : Nat) : Bool :=
  let pairs := ([g₀,g₁].flatMap fun g => (cornersOf x x' y y').map fun z => (g,z))
  m==1 || (m==2 && axisOK pos v g₀ g₁ x x' y y') ||
    (List.range 8).all fun i =>
      let p := pairs.getD i ((0,0),(0,0))
      C.detSign pos v p.1 p.2 (ss.getD (2*i+off) .zero)

def WinA.signs (C : Chart) (a : WinA) (g₀ g₁ : Index) (x x' y y' : Nat) : Bool :=
  endOK C a.mLo a.w.posLo a.w.lo' g₀ g₁ x x' y y' a.ss 0 &&
  endOK C a.mHi (!a.w.posLo) a.w.hi' g₀ g₁ x x' y y' a.ss 1

/-- The assumed ends of a window: a node and the wanted sign of `det(g,z,node)`. -/
def WinA.assumed (a : WinA) : List (Index × Bool) :=
  (if a.mLo==1 then [(a.w.lo',a.w.posLo)] else [])++(if a.mHi==1 then [(a.w.hi',!a.w.posLo)] else [])

def chainA (C : Chart) (g₀ g₁ : Index) (x x' y y' : Nat) : List Nat → List WinA → Bool
  | [t],[] => cellIn (tileOf C t) x x' y y'
  | t::u::rest,a::ws => a.w.place (tileOf C t) (tileOf C u) && a.w.sep g₀ g₁ x x' y y' &&
      a.signs C g₀ g₁ x x' y y' && chainA C g₀ g₁ x x' y y' (u::rest) ws
  | _,_ => false

structure CertA where
  ts : List Nat
  ws : List WinA

def CertA.ok (C : Chart) (g₀ g₁ : Index) (x x' y y' : Nat) (c : CertA) : Bool :=
  match c.ts with
  | [] => false
  | t::_ => inRect (tileOf C t) g₀ && inRect (tileOf C t) g₁ && chainA C g₀ g₁ x x' y y' c.ts c.ws &&
      c.ts.all (· < C.tiles.length) && decide (g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)

def CertA.assumed (c : CertA) : List (Index × Bool) := c.ws.flatMap WinA.assumed

/-- The sign condition of an assumed end for the sightline from `g` to `z`. -/
def Holds (X Y : List ℝ) (g z : Point) (e : Index × Bool) : Prop :=
  0≤(if e.2 then 1 else -1)*ArtGallery.det g z (gridPt X Y e.1)

set_option maxHeartbeats 1000000 in
theorem endOK_sound (G : Good C X Y s A) {m : Nat} {pos : Bool} {v g₀ g₁ : Index} {x x' y y' : Nat}
    {ss : List Sign} {off : Nat} (h : endOK C m pos v g₀ g₁ x x' y y' ss off=true) (hm : m≠1)
    (hv : v.1<C.nx ∧ v.2<C.ny)
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    0≤(if pos then 1 else -1)*ArtGallery.det g z (gridPt X Y v) := by
  have rg' := rg
  obtain ⟨r0x,r0y,r1x,r1y,rx,ry⟩ := rg'
  have lx := G.lx; have ly := G.ly
  simp only [endOK,Bool.or_eq_true,beq_iff_eq,hm,false_or,Bool.and_eq_true,List.all_eq_true,List.mem_range] at h
  rcases h with ⟨-,ax⟩|hall
  · exact axis_sign G ax rg hv hg hz
  have cr (z' : Index) (hz' : z'∈cornersOf x x' y y') : z'.1<C.nx ∧ z'.2<C.ny := by
    simp only [cornersOf,List.mem_cons,List.not_mem_nil,or_false] at hz'
    rcases hz' with rfl|rfl|rfl|rfl <;> simp <;> omega
  have gr (g' : Index) (hg' : g'∈[g₀,g₁]) : g'.1<C.nx ∧ g'.2<C.ny := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg'; rcases hg' with rfl|rfl <;> simp_all
  have cell : x'<X.length ∧ y'<Y.length := ⟨by omega,by omega⟩
  have hxx : X.getD x 0≤X.getD x' 0 := lev_le G.hx cell.1 (by omega)
  have hyy : Y.getD y 0≤Y.getD y' 0 := lev_le G.hy cell.2 (by omega)
  apply nonneg_on _ hxx hyy _ hg hz
  intro g' hg' z' hz'
  have corner : ∀ g''∈[g₀,g₁], ∀ z''∈cornersOf x x' y y',
      0≤(if pos then 1 else -1)*ArtGallery.det (gridPt X Y g'') (gridPt X Y z'') (gridPt X Y v) := by
    intro g'' hg'' z'' hz''
    obtain ⟨i,hi,e⟩ := pairs_mem hg'' hz''
    have h := hall i hi
    rw [e] at h
    exact sign_fact G hv (gr g'' hg'') (cr z'' hz'') h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg' hz'
  have m0 : g₀∈[g₀,g₁] := List.mem_cons_self
  have m1 : g₁∈[g₀,g₁] := List.mem_cons_of_mem _ List.mem_cons_self
  have c00 : ((x,y):Index)∈cornersOf x x' y y' := List.mem_cons_self
  have c10 : ((x',y):Index)∈cornersOf x x' y y' := by simp [cornersOf]
  have c01 : ((x,y'):Index)∈cornersOf x x' y y' := by simp [cornersOf]
  have c11 : ((x',y'):Index)∈cornersOf x x' y y' := by simp [cornersOf]
  rcases hg' with rfl|rfl <;> rcases hz' with rfl|rfl|rfl|rfl
  · exact corner g₀ m0 _ c00
  · exact corner g₀ m0 _ c10
  · exact corner g₀ m0 _ c01
  · exact corner g₀ m0 _ c11
  · exact corner g₁ m1 _ c00
  · exact corner g₁ m1 _ c10
  · exact corner g₁ m1 _ c01
  · exact corner g₁ m1 _ c11

/-- Every sightline satisfying the assumed ends meets the window of two consecutive tiles. -/
theorem windowA_meet (G : Good C X Y s A) {g₀ g₁ : Index} {x x' y y' : Nat} {wa : WinA}
    {a b : CorridorProgram.Rect Nat}
    (ha : a.1<X.length ∧ a.2.1<X.length ∧ a.2.2.1<Y.length ∧ a.2.2.2<Y.length)
    (hb : b.1<X.length ∧ b.2.1<X.length ∧ b.2.2.1<Y.length ∧ b.2.2.2<Y.length)
    (hp : wa.w.place a b=true) (hs : wa.w.sep g₀ g₁ x x' y y'=true) (hsg : wa.signs C g₀ g₁ x x' y y'=true)
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0))
    (hA : ∀ e∈wa.assumed, Holds X Y g z e) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ Geometry.lerp g z t∈realRect X Y a∩realRect X Y b := by
  have lx := G.lx; have ly := G.ly
  have hlo : wa.w.lo'.1<C.nx ∧ wa.w.lo'.2<C.ny := by
    rcases hw : wa.w with ⟨vert,dir,c,lo,hi⟩
    rw [hw] at hp
    cases vert <;> simp only [Win.place,Win.lo',ite_true,ite_false,Bool.false_eq_true,decide_eq_true_eq] at hp ⊢ <;> omega
  have hhi : wa.w.hi'.1<C.nx ∧ wa.w.hi'.2<C.ny := by
    rcases hw : wa.w with ⟨vert,dir,c,lo,hi⟩
    rw [hw] at hp
    cases vert <;> simp only [Win.place,Win.hi',ite_true,ite_false,Bool.false_eq_true,decide_eq_true_eq] at hp ⊢ <;> omega
  simp only [WinA.signs,Bool.and_eq_true] at hsg
  have sLo : 0≤(if wa.w.posLo then 1 else -1)*ArtGallery.det g z (gridPt X Y wa.w.lo') := by
    by_cases hl : wa.mLo=1
    · exact hA (wa.w.lo',wa.w.posLo) (by simp [WinA.assumed,hl])
    · exact endOK_sound G hsg.1 hl hlo rg hg hz
  have sHi : 0≤(if !wa.w.posLo then 1 else -1)*ArtGallery.det g z (gridPt X Y wa.w.hi') := by
    by_cases hh : wa.mHi=1
    · exact hA (wa.w.hi',!wa.w.posLo) (by simp [WinA.assumed,hh])
    · exact endOK_sound G hsg.2 hh hhi rg hg hz
  exact meet_core G ha hb hp hs rg hg hz sLo sHi

theorem chainA_facts (G : Good C X Y s A) {g₀ g₁ : Index} {x x' y y' : Nat}
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    ∀ (ts : List Nat) (ws : List WinA), chainA C g₀ g₁ x x' y y' ts ws=true →
      (∀ i∈ts, i<C.tiles.length) → (∀ e∈ws.flatMap WinA.assumed, Holds X Y g z e) →
      (∀ R, (ts.map (fun i => realRect X Y (tileOf C i))).getLast?=some R → z∈R) ∧
      (ts.map (fun i => realRect X Y (tileOf C i))).IsChain
        (fun R R' => ∃ t : ℝ, 0≤t ∧ t≤1 ∧ Geometry.lerp g z t∈R∩R')
  | [],_,h,_,_ => by simp [chainA] at h
  | [t],[],h,hi,_ => by
    have ti := tile_idx G (hi t (by simp))
    simp only [chainA,cellIn,decide_eq_true_eq] at h
    obtain ⟨a0,a1,a2,a3⟩ := h
    obtain ⟨z0,z1,z2,z3⟩ := hz
    refine ⟨fun R hR => ?_,List.isChain_singleton _⟩
    simp only [List.map_cons,List.map_nil,List.getLast?_singleton,Option.some.injEq] at hR
    subst hR
    have lx := G.lx; have ly := G.ly
    refine ⟨?_,?_,?_,?_⟩
    · exact (lev_le G.hx (by omega) a0).trans z0
    · exact z1.trans (lev_le G.hx ti.2.1 a1)
    · exact (lev_le G.hy (by omega) a2).trans z2
    · exact z3.trans (lev_le G.hy ti.2.2.2 a3)
  | [_],_::_,h,_,_ => by simp [chainA] at h
  | _::_::_,[],h,_,_ => by simp [chainA] at h
  | t::u::rest,wa::ws,h,hi,hA => by
    simp only [chainA,Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp,hs⟩,hsg⟩,hrest⟩ := h
    have ih := chainA_facts G rg hg hz (u::rest) ws hrest (fun i hi' => hi i (List.mem_cons_of_mem _ hi'))
      (fun e he => hA e (by simp only [List.flatMap_cons]; exact List.mem_append_right _ he))
    have m := windowA_meet G (tile_idx G (hi t (by simp))) (tile_idx G (hi u (by simp))) hp hs hsg rg hg hz
      (fun e he => hA e (by simp only [List.flatMap_cons]; exact List.mem_append_left _ he))
    refine ⟨fun R hR => ih.1 R (by simpa using hR),?_⟩
    simp only [List.map_cons] at ih ⊢
    exact List.isChain_cons_cons.mpr ⟨m,ih.2⟩

/-- Soundness of a certificate with assumed ends: a point of the guard segment sees a point of
the closed cell whenever the sightline satisfies the assumed signs. -/
theorem CertA.sound (G : Good C X Y s A) {g₀ g₁ : Index} {x x' y y' : Nat} {c : CertA}
    (h : c.ok C g₀ g₁ x x' y y'=true)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0))
    (hA : ∀ e∈c.assumed, Holds X Y g z e) : (C.poly X Y).Sees g z := by
  unfold CertA.ok at h
  split at h
  · simp at h
  · next t rest hts =>
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
    obtain ⟨⟨⟨⟨i0,i1⟩,hch⟩,hidx⟩,rg⟩ := h
    have hidx' : ∀ i∈c.ts, i<C.tiles.length := fun i hi => by simpa using hidx i hi
    have ti := tile_idx G (hidx' t (by rw [hts]; simp))
    have g0 := node_in G ti i0
    have g1 := node_in G ti i1
    have gR : g∈realRect X Y (tileOf C t) := by
      obtain ⟨u,u0,u1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hg
      exact lerp_rect g0 g1 u0 u1
    have facts := chainA_facts G rg hg hz c.ts c.ws hch hidx' hA
    have sub := segment_in_chain (c.ts.map (fun i => realRect X Y (tileOf C i)))
      (fun R hR => by obtain ⟨i,-,rfl⟩ := List.mem_map.mp hR; exact rect_convex _ _ _ _)
      (fun R hR => by rw [hts] at hR; simp only [List.map_cons,List.head?_cons,Option.some.injEq] at hR; rw [← hR]; exact gR)
      facts.1 facts.2 (by rw [hts]; simp)
    intro p hp
    obtain ⟨R,hR,hpR⟩ := Set.mem_iUnion₂.mp (sub hp)
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hR
    exact tile_sub G (hidx' i hi) hpR

end Sound


/-! ## Covering a chart by certified rectangles -/

section Cover
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

/-- A rectangle of cells `[x,x']×[y,y']` seen from the canonical point of a role (`point`) or
from its whole spot, by a certificate without assumed ends. -/
structure EntryA where
  x : Nat
  x' : Nat
  y : Nat
  y' : Nat
  role : Nat
  point : Bool
  cert : CertA

def EntryA.ends (roles : List (List Index)) (e : EntryA) : Index × Index :=
  let l := roles.getD e.role []
  if e.point then (l.getD 0 (0,0),l.getD 0 (0,0)) else (CellRoles.spotA l,CellRoles.spotB l)

def EntryA.good (C : Chart) (roles : List (List Index)) (e : EntryA) : Bool :=
  decide (e.role<roles.length) && e.cert.assumed.isEmpty &&
    e.cert.ok C (e.ends roles).1 (e.ends roles).2 e.x e.x' e.y e.y'

/-- A chart covered by certified rectangles of cells and special cells: every point is seen from
the guard segment of one entry or lies in a special closed cell. -/
theorem coverA (G : Good C X Y s A) (hnd : ∀ t∈C.tiles, t.1<t.2.1 ∧ t.2.2.1<t.2.2.2)
    {roles : List (List Index)} {rects : List EntryA} {special : List (Nat × Nat)}
    (hok : rects.all (EntryA.good C roles)=true)
    (hcomp : ∀ t∈C.tiles, ∀ i j, t.1 ≤ i → i<t.2.1 → t.2.2.1≤j → j<t.2.2.2 →
      (i,j)∈special ∨ ∃ e∈rects, e.x ≤ i ∧ i+1≤e.x' ∧ e.y≤j ∧ j+1≤e.y')
    {z : Point} (hz : z∈(C.poly X Y).filled) :
    (∃ e∈rects, e.role<roles.length ∧
      ∀ g∈ArtGallery.segment (gridPt X Y (e.ends roles).1) (gridPt X Y (e.ends roles).2), (C.poly X Y).Sees g z) ∨
    ∃ c∈special, z∈Rect (X.getD c.1 0) (X.getD (c.1+1) 0) (Y.getD c.2 0) (Y.getD (c.2+1) 0) := by
  obtain ⟨t,ht,i,j,i0,i1,j0,j1,hzc⟩ := point_cell G hnd hz
  rcases hcomp t ht i j i0 i1 j0 j1 with sp|⟨e,he,e0,e1,e2,e3⟩
  · exact Or.inr ⟨(i,j),sp,hzc⟩
  · left
    have hg := List.all_eq_true.mp hok e he
    simp only [EntryA.good,Bool.and_eq_true,decide_eq_true_eq] at hg
    obtain ⟨⟨hk,hnil⟩,hc⟩ := hg
    have hz' : z∈Rect (X.getD e.x 0) (X.getD e.x' 0) (Y.getD e.y 0) (Y.getD e.y' 0) := by
      obtain ⟨z0,z1,z2,z3⟩ := hzc
      have lx := G.lx; have ly := G.ly
      have idx := G.tileIdx t ht
      have hc' := hc
      unfold CertA.ok at hc'
      split at hc'
      · simp at hc'
      · simp only [Bool.and_eq_true,decide_eq_true_eq] at hc'
        obtain ⟨-,-,-,-,-,ex1,-,ey1⟩ := hc'.2
        exact ⟨(lev_le G.hx (by omega) e0).trans z0,z1.trans (lev_le G.hx (by omega) e1),
          (lev_le G.hy (by omega) e2).trans z2,z3.trans (lev_le G.hy (by omega) e3)⟩
    refine ⟨e,he,hk,fun g hg => CertA.sound G hc hg hz' ?_⟩
    intro a ha
    rw [List.isEmpty_iff.mp hnil] at ha
    simp at ha

end Cover

/-- The cell check of a tiling with the special cells and the certified rectangles first filtered
to those meeting each tile: a cell found in the filtered lists is found in the full ones. -/
theorem complete_of_filter {tiles : List (CorridorProgram.Rect Nat)} {special : List (Nat × Nat)}
    {rects : List EntryA}
    (h : tiles.all (fun t =>
      (List.range' t.1 (t.2.1-t.1)).all fun i => (List.range' t.2.2.1 (t.2.2.2-t.2.2.1)).all fun j =>
        (special.filter (fun c => decide (t.1 ≤ c.1 ∧ c.1 < t.2.1 ∧ t.2.2.1 ≤ c.2 ∧ c.2 < t.2.2.2))).contains (i,j) ||
        (rects.filter (fun e => decide (e.x < t.2.1 ∧ t.1 < e.x' ∧ e.y < t.2.2.2 ∧ t.2.2.1 < e.y'))).any
          (fun e => decide (e.x ≤ i ∧ i+1 ≤ e.x' ∧ e.y ≤ j ∧ j+1 ≤ e.y')))=true) :
    tiles.all (fun t => (List.range' t.1 (t.2.1-t.1)).all fun i => (List.range' t.2.2.1 (t.2.2.2-t.2.2.1)).all fun j =>
      special.contains (i,j) || rects.any (fun e => decide (e.x ≤ i ∧ i+1 ≤ e.x' ∧ e.y ≤ j ∧ j+1 ≤ e.y')))=true := by
  simp only [List.all_eq_true] at h ⊢
  intro t ht i hi j hj
  have h' := h t ht i hi j hj
  simp only [Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true] at h' ⊢
  rcases h' with h'|⟨e,he,h'⟩
  · exact Or.inl (List.mem_of_mem_filter h')
  · exact Or.inr ⟨e,List.mem_of_mem_filter he,h'⟩

end ArtGallery.Orthogonal.BoundaryPoint.CoverAssume
end
