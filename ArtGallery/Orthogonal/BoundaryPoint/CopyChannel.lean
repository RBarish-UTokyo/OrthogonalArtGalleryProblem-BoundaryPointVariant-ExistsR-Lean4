module

public import ArtGallery.Orthogonal.BoundaryPoint.CellCert
public import ArtGallery.Orthogonal.BoundaryPoint.CopyTest

/-! # Copy tests on a certified wing chart

The target box of a copy test is an open grid cell. A rectangle of the chart
contains it, a `crossOne` certificate for the receiver's spot excludes the
side beyond the receiver's corner ray, and the abstract tests of `CopyTest`
and `CopyGap` give the parameter inequalities. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyChannel
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CellCert ArtGallery.Orthogonal.Hard

/-- A coordinate strictly between two consecutive grid lines has the even atom code between them. -/
theorem atom_between {xs : List ℝ} (hx : xs.IsChain (·<·)) {m : Nat} (hm : m+1<xs.length) {q : ℝ}
    (h₀ : xs.getD m 0<q) (h₁ : q<xs.getD (m+1) 0) : atom q xs=2*m+2 := by
  have up := (compare_line hx hm q).1.mp h₁
  have low : ¬(q≤xs.getD m 0) := by intro h; linarith
  rw [le_line hx (by omega)] at low
  unfold line at up low; omega

/-- An open cell inside a chart rectangle lies in the filled chart polygon. -/
def inTile (tiles : List (CorridorProgram.Rect Nat)) (cell : Nat × Nat) : Bool :=
  tiles.any (fun r => inBox cell.1 cell.2 r)

theorem tile_filled {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {cell : Nat × Nat} (h : inTile C.tiles cell=true) {z : Point} (zx : atom z.1 X=cell.1) (zy : atom z.2 Y=cell.2) :
    z∈(C.poly X Y).filled := by
  rw [G.fill,cells_iff G.hx G.hy (by rw [G.lx,G.ly]; exact G.tileIdx) z,zx,zy]
  exact h

/-- The receiver's side of its ray through a corner `u`, as a determinant sign. -/
theorem receiver_det {cx d r t D y x : ℝ} (hd : 0<d) (left : x<cx-(r+t/D)*(y-1)) :
    0<ArtGallery.det (x,y) (cx+d*(r+t/D),1-d) (cx,1) := by
  simp only [ArtGallery.det]; nlinarith

/-- The receiver on its spot, as a point of the spot segment. -/
theorem receiver_on_spot {cx d r D t : ℝ} (hD : 0<D) (ht : 0≤t ∧ t≤3/2) :
    ((cx+d*(r+t/D),1-d):Point)∈ArtGallery.segment (cx+d*r,1-d) (cx+d*(r+3/(2*D)),1-d) := by
  refine ⟨2*t/3,by linarith,by linarith,?_⟩
  ext <;> simp <;> field_simp <;> ring

/-- The lower (nook) test on a certified chart: `tB ≤ tR`. -/
theorem lower_local {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb : Index} {kR : Nat} {first : Bool} {pairs : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR false first pairs=true)
    {cx d r b D tB tR H : ℝ}
    (hu : gridPt X Y (if first then C.next kR else C.node kR)=(cx,1))
    (hra : gridPt X Y ra=(cx+d*r,1-d)) (hrb : gridPt X Y rb=(cx+d*(r+3/(2*D)),1-d))
    (hD : 0<D) (hH : 0<H) (hd : 0<d) (axis : Y.getD iy 0=1+H) (deep : Y.getD (iy+1) 0-Y.getD iy 0+H<D)
    (ht : 0≤tR ∧ tR≤3/2)
    (hB : ((W+b*D+tB,1-D):Point)∈rest) (hR : ((cx+d*(r+tR/D),1-d):Point)∈(C.poly X Y).filled)
    (others : ∀ g∈Gs, g≠(W+b*D+tB,1-D) → g≠(cx+d*(r+tR/D),1-d) → ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 →
      1+H<y → y<1+H+(Y.getD (iy+1) 0-Y.getD iy 0) → ¬P.Sees g (x,y))
    (incidence : W-b*H=cx-r*H)
    (ha : X.getD xc 0<W-(b+tB/D)*H) (hb : cx-(r+tR/D)*H<X.getD (xc+1) 0) : tB≤tR := by
  have gap : 0<Y.getD (iy+1) 0-Y.getD iy 0 := by
    have := level_lt G.hy hiy (Nat.lt_succ_self iy); linarith
  have atoms (x y : ℝ) (h0 : X.getD xc 0<x) (h1 : x<X.getD (xc+1) 0) (y0 : 1+H<y)
      (y1 : y<1+H+(Y.getD (iy+1) 0-Y.getD iy 0)) : atom x X=2*xc+2 ∧ atom y Y=2*iy+2 :=
    ⟨atom_between G.hx hxc h0 h1,atom_between G.hy hiy (by rw [axis]; exact y0) (by linarith)⟩
  apply CopyTest.lower fill closed contact hW cover hD hH gap (by linarith) hB hR
  · intro x y h0 h1 y0 y1
    obtain ⟨ax,ay⟩ := atoms x y h0 h1 y0 y1
    exact tile_filled G tile (z:=(x,y)) ax ay
  · intro x y h0 h1 y0 y1 left
    obtain ⟨ax,ay⟩ := atoms x y h0 h1 y0 y1
    apply crossOne_sound G rcert (z:=(cx+d*(r+tR/D),1-d)) (by rw [hra,hrb]; exact receiver_on_spot hD ht)
      (w:=(x,y)) ax ay
    refine ⟨fun e => by simp at e,fun _ => ?_⟩
    rw [hu]; exact receiver_det hd left
  · exact others
  · exact incidence
  · exact ha
  · exact hb

/-- Abscissa at height `y` on the line through `p` and `c`. -/
noncomputable def lineX (p c : Point) (y : ℝ) : ℝ := p.1+(c.1-p.1)*(y-p.2)/(c.2-p.2)

theorem det_lineX {p c : Point} (h : p.2<c.2) (x y : ℝ) :
    ArtGallery.det p c (x,y)=(c.2-p.2)*(lineX p c y-x) := by
  have hne : c.2-p.2≠0 := by linarith
  unfold lineX; simp only [ArtGallery.det]
  field_simp; ring

/-- The upper (chamber) test on a certified chart: with matched rays, `tR ≤ tB`. -/
theorem upper_local {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {dl dr : Index} (hdl : gridPt X Y dl=((0:ℝ),(1:ℝ))) (hdr : gridPt X Y dr=(W,1))
    {kB : Nat} {fB : Bool} {pB : List (Sign × Sign)} (bcert : crossOne C dl dr (2*xc+2,2*iy+2) kB false fB pB=true)
    {ra rb : Index} {kR : Nat} {fR : Bool} {pR : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR true fR pR=true)
    {Bx By Rx Ry κ tB tR : ℝ} {cB cR : Point}
    (hcB : gridPt X Y (if fB then C.next kB else C.node kB)=cB)
    (hcR : gridPt X Y (if fR then C.next kR else C.node kR)=cR)
    (hR0 : ((Rx+κ*tR,Ry):Point)∈ArtGallery.segment (gridPt X Y ra) (gridPt X Y rb))
    (hB : ((Bx+tB,By):Point)∈rest) (hBy : By<1) (hR : ((Rx+κ*tR,Ry):Point)∈(C.poly X Y).filled)
    (above : 1<Y.getD iy 0)
    (bLow : By<cB.2) (rLow : Ry<cR.2) (axisB : cB.2<Y.getD (iy+1) 0)
    (others : ∀ g∈Gs, g≠(Bx+tB,By) → g≠(Rx+κ*tR,Ry) → ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 →
      Y.getD iy 0<y → y<Y.getD (iy+1) 0 → ¬P.Sees g (x,y))
    (matched : ∀ t : ℝ, lineX (Bx+t,By) cB (Y.getD (iy+1) 0)=lineX (Rx+κ*t,Ry) cR (Y.getD (iy+1) 0))
    (ha : X.getD xc 0<lineX (Rx+κ*tR,Ry) cR (Y.getD (iy+1) 0))
    (hb : lineX (Bx+tB,By) cB (Y.getD (iy+1) 0)<X.getD (xc+1) 0) : tR≤tB := by
  set a := Y.getD (iy+1) 0
  have gap : 0<a-Y.getD iy 0 := by have := level_lt G.hy hiy (Nat.lt_succ_self iy); linarith
  have sub : (C.poly X Y).filled⊆P.filled := by rw [fill]; exact subset_union_left
  have atoms (x y : ℝ) (h0 : X.getD xc 0<x) (h1 : x<X.getD (xc+1) 0) (y0 : a-(a-Y.getD iy 0)<y) (y1 : y<a) :
      atom x X=2*xc+2 ∧ atom y Y=2*iy+2 :=
    ⟨atom_between G.hx hxc h0 h1,atom_between G.hy hiy (by linarith) y1⟩
  let B : Point := (Bx+tB,By)
  let R : Point := (Rx+κ*tR,Ry)
  -- the lines through the two corners, as affine functions of the height
  have lin (p c : Point) (y : ℝ) : lineX p c y=lineX p c a+((c.1-p.1)/(c.2-p.2))*(y-a) := by
    unfold lineX; ring
  have key := CopyGap.no_gap (P:=P) (G:=Gs) cover (p:=R) (q:=B) (a:=a) (ε:=a-Y.getD iy 0)
    (xa:=X.getD xc 0) (xb:=X.getD (xc+1) 0) (αp:=lineX R cR a) (βp:=(cR.1-R.1)/(cR.2-R.2))
    (αq:=lineX B cB a) (βq:=(cB.1-B.1)/(cB.2-B.2)) false gap
    (fun x y h0 h1 hy => by
      simp only [Bool.false_eq_true,ite_false] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      exact sub (tile_filled G tile (z:=(x,y)) ax ay))
    (fun x y h0 h1 hy right => by
      simp only [Bool.false_eq_true,ite_false] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      intro sees
      have convex : Convex ℝ ((C.poly X Y).filled∩rest) := contact ▸ Geometry.segment_convex _ _
      have zL := tile_filled G tile (z:=(x,y)) ax ay
      apply crossOne_sound G rcert (z:=R) hR0 (w:=(x,y)) ax ay
        ⟨fun _ => ?_,fun e => by simp at e⟩ ((SingleWindow.sees_iff fill closed convex hR zL).mp sees)
      rw [hcR]
      have d := det_lineX (p:=R) (c:=cR) (show R.2<cR.2 from rLow) x y
      have e : ArtGallery.det (x,y) R cR=ArtGallery.det R cR (x,y) := by simp only [ArtGallery.det]; ring
      rw [e,d]
      have : lineX R cR y<x := by rw [lin]; exact right
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith))
    (fun x y h0 h1 hy left => by
      simp only [Bool.false_eq_true,ite_false] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      have zL := tile_filled G tile (z:=(x,y)) ax ay
      apply CopyDoor.through_door fill closed contact hW (σ:=1) (c:=cB) hB zL (by simp; linarith)
      · rw [one_mul]
        have d := det_lineX (p:=B) (c:=cB) (show B.2<cB.2 from bLow) x y
        have e : ArtGallery.det (x,y) B cB=ArtGallery.det B cB (x,y) := by simp only [ArtGallery.det]; ring
        rw [e,d]
        have : x<lineX B cB y := by rw [lin]; exact left
        exact mul_pos (by linarith) (by linarith)
      · intro q hq pos
        rw [one_mul] at pos
        apply crossOne_sound G bcert (z:=q) (by rw [hdl,hdr]; exact hq) (w:=(x,y)) ax ay
        exact ⟨fun e => by simp at e,fun _ => by rw [hcB]; exact pos⟩)
    (fun g hg e1 e2 x y h0 h1 hy _ _ => by
      simp only [Bool.false_eq_true,ite_false] at hy
      exact others g hg e2 e1 x y h0 h1 (by linarith) hy.2)
    ha hb
  -- matched rays: the base line is decreasing in its parameter
  have mt := matched tR
  have slope : lineX (Bx+tB,By) cB a-lineX (Bx+tR,By) cB a=(tB-tR)*((cB.2-a)/(cB.2-By)) := by
    have hne : cB.2-By≠0 := by linarith
    unfold lineX; simp only; field_simp; ring
  have neg : (cB.2-a)/(cB.2-By)<0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have : (tB-tR)*((cB.2-a)/(cB.2-By))≤0 := by rw [←slope,mt]; linarith
  nlinarith

/-- The upper (chamber) test on a certified chart: with matched rays, `tR ≤ tB`. -/
theorem upper_blocked {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb : Index} {kR : Nat} {fR : Bool} {pR : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR true fR pR=true)
    {Bx By Rx Ry κ tB tR : ℝ} {cB cR : Point}
    (hcR : gridPt X Y (if fR then C.next kR else C.node kR)=cR)
    (hR0 : ((Rx+κ*tR,Ry):Point)∈ArtGallery.segment (gridPt X Y ra) (gridPt X Y rb))
    {Bg : Point} (hR : ((Rx+κ*tR,Ry):Point)∈(C.poly X Y).filled)
    (above : 1<Y.getD iy 0)
    (bLow : By<cB.2) (rLow : Ry<cR.2) (axisB : cB.2<Y.getD (iy+1) 0)
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      x<lineX (Bx+tB,By) cB y → ¬P.Sees Bg (x,y))
    (others : ∀ g∈Gs, g≠Bg → g≠(Rx+κ*tR,Ry) → ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 →
      Y.getD iy 0<y → y<Y.getD (iy+1) 0 → lineX (Rx+κ*tR,Ry) cR y<x → x<lineX (Bx+tB,By) cB y → ¬P.Sees g (x,y))
    (matched : ∀ t : ℝ, lineX (Bx+t,By) cB (Y.getD (iy+1) 0)=lineX (Rx+κ*t,Ry) cR (Y.getD (iy+1) 0))
    (ha : X.getD xc 0<lineX (Rx+κ*tR,Ry) cR (Y.getD (iy+1) 0))
    (hb : lineX (Bx+tB,By) cB (Y.getD (iy+1) 0)<X.getD (xc+1) 0) : tR≤tB := by
  set a := Y.getD (iy+1) 0
  have gap : 0<a-Y.getD iy 0 := by have := level_lt G.hy hiy (Nat.lt_succ_self iy); linarith
  have sub : (C.poly X Y).filled⊆P.filled := by rw [fill]; exact subset_union_left
  have atoms (x y : ℝ) (h0 : X.getD xc 0<x) (h1 : x<X.getD (xc+1) 0) (y0 : a-(a-Y.getD iy 0)<y) (y1 : y<a) :
      atom x X=2*xc+2 ∧ atom y Y=2*iy+2 :=
    ⟨atom_between G.hx hxc h0 h1,atom_between G.hy hiy (by linarith) y1⟩
  let B : Point := (Bx+tB,By)
  let R : Point := (Rx+κ*tR,Ry)
  -- the lines through the two corners, as affine functions of the height
  have lin (p c : Point) (y : ℝ) : lineX p c y=lineX p c a+((c.1-p.1)/(c.2-p.2))*(y-a) := by
    unfold lineX; ring
  have key := CopyGap.no_gap (P:=P) (G:=Gs) cover (p:=R) (q:=Bg) (a:=a) (ε:=a-Y.getD iy 0)
    (xa:=X.getD xc 0) (xb:=X.getD (xc+1) 0) (αp:=lineX R cR a) (βp:=(cR.1-R.1)/(cR.2-R.2))
    (αq:=lineX B cB a) (βq:=(cB.1-B.1)/(cB.2-B.2)) false gap
    (fun x y h0 h1 hy => by
      simp only [Bool.false_eq_true,ite_false] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      exact sub (tile_filled G tile (z:=(x,y)) ax ay))
    (fun x y h0 h1 hy right => by
      simp only [Bool.false_eq_true,ite_false] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      intro sees
      have convex : Convex ℝ ((C.poly X Y).filled∩rest) := contact ▸ Geometry.segment_convex _ _
      have zL := tile_filled G tile (z:=(x,y)) ax ay
      apply crossOne_sound G rcert (z:=R) hR0 (w:=(x,y)) ax ay
        ⟨fun _ => ?_,fun e => by simp at e⟩ ((SingleWindow.sees_iff fill closed convex hR zL).mp sees)
      rw [hcR]
      have d := det_lineX (p:=R) (c:=cR) (show R.2<cR.2 from rLow) x y
      have e : ArtGallery.det (x,y) R cR=ArtGallery.det R cR (x,y) := by simp only [ArtGallery.det]; ring
      rw [e,d]
      have : lineX R cR y<x := by rw [lin]; exact right
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith))
    (fun x y h0 h1 hy left => by
      simp only [Bool.false_eq_true,ite_false] at hy
      apply blockB x y h0 h1 (by linarith) hy.2
      rw [lin]; exact left)
    (fun g hg e1 e2 x y h0 h1 hy lo hi => by
      simp only [Bool.false_eq_true,ite_false] at hy
      exact others g hg e2 e1 x y h0 h1 (by linarith) hy.2 (by rw [lin]; exact lo) (by rw [lin]; exact hi))
    ha hb
  -- matched rays: the base line is decreasing in its parameter
  have mt := matched tR
  have slope : lineX (Bx+tB,By) cB a-lineX (Bx+tR,By) cB a=(tB-tR)*((cB.2-a)/(cB.2-By)) := by
    have hne : cB.2-By≠0 := by linarith
    unfold lineX; simp only; field_simp; ring
  have neg : (cB.2-a)/(cB.2-By)<0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have : (tB-tR)*((cB.2-a)/(cB.2-By))≤0 := by rw [←slope,mt]; linarith
  nlinarith

/-- The upper (chamber) test on a certified chart: with matched rays, `tR ≤ tB`. -/
theorem upper_blocked_mid {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb : Index} {kR : Nat} {fR : Bool} {pR : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR true fR pR=true)
    {Bx By Rx Ry κ tB tR : ℝ} {cB cR : Point}
    (hcR : gridPt X Y (if fR then C.next kR else C.node kR)=cR)
    (hR0 : ((Rx+κ*tR,Ry):Point)∈ArtGallery.segment (gridPt X Y ra) (gridPt X Y rb))
    {Bg : Point} (hR : ((Rx+κ*tR,Ry):Point)∈(C.poly X Y).filled)
    (above : 1<Y.getD iy 0)
    (bLow : By<cB.2) (rLow : Ry<cR.2) (axisB : cB.2<Y.getD (iy+1) 0)
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      x<lineX (Bx+tB,By) cB y → ¬P.Sees Bg (x,y))
    (others : ∀ g∈Gs, g≠Bg → g≠(Rx+κ*tR,Ry) → ∀ t' : ℝ, tB<t' → t'<tR → ∀ y : ℝ, Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      X.getD xc 0<lineX (Bx+t',By) cB y → lineX (Bx+t',By) cB y<X.getD (xc+1) 0 → ¬P.Sees g (lineX (Bx+t',By) cB y,y))
    (matched : ∀ t : ℝ, lineX (Bx+t,By) cB (Y.getD (iy+1) 0)=lineX (Rx+κ*t,Ry) cR (Y.getD (iy+1) 0))
    (ha : X.getD xc 0<lineX (Rx+κ*tR,Ry) cR (Y.getD (iy+1) 0))
    (hb : lineX (Bx+tB,By) cB (Y.getD (iy+1) 0)<X.getD (xc+1) 0) : tR≤tB := by
  set a := Y.getD (iy+1) 0
  have gap : 0<a-Y.getD iy 0 := by have := level_lt G.hy hiy (Nat.lt_succ_self iy); linarith
  have sub : (C.poly X Y).filled⊆P.filled := by rw [fill]; exact subset_union_left
  have atoms (x y : ℝ) (h0 : X.getD xc 0<x) (h1 : x<X.getD (xc+1) 0) (y0 : a-(a-Y.getD iy 0)<y) (y1 : y<a) :
      atom x X=2*xc+2 ∧ atom y Y=2*iy+2 :=
    ⟨atom_between G.hx hxc h0 h1,atom_between G.hy hiy (by linarith) y1⟩
  let B : Point := (Bx+tB,By)
  let R : Point := (Rx+κ*tR,Ry)
  -- the lines through the two corners, as affine functions of the height
  have lin (p c : Point) (y : ℝ) : lineX p c y=lineX p c a+((c.1-p.1)/(c.2-p.2))*(y-a) := by
    unfold lineX; ring
  have Aaff (t : ℝ) : lineX (Bx+t,By) cB a=lineX (Bx,By) cB a+t*((cB.2-a)/(cB.2-By)) := by
    have hne : cB.2-By≠0 := by linarith
    unfold lineX; simp only; field_simp; ring
  have κneg : (cB.2-a)/(cB.2-By)<0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have key := CopyGap.no_gap_mid (P:=P) (G:=Gs) cover (p:=R) (q:=Bg) (a:=a) (ε:=a-Y.getD iy 0)
    (xa:=X.getD xc 0) (xb:=X.getD (xc+1) 0) (αp:=lineX R cR a) (βp:=(cR.1-R.1)/(cR.2-R.2))
    (αq:=lineX B cB a) (βq:=(cB.1-B.1)/(cB.2-B.2)) false gap
    (fun x y h0 h1 hy => by
      simp only [Bool.false_eq_true,ite_false] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      exact sub (tile_filled G tile (z:=(x,y)) ax ay))
    (fun x y h0 h1 hy right => by
      simp only [Bool.false_eq_true,ite_false] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      intro sees
      have convex : Convex ℝ ((C.poly X Y).filled∩rest) := contact ▸ Geometry.segment_convex _ _
      have zL := tile_filled G tile (z:=(x,y)) ax ay
      apply crossOne_sound G rcert (z:=R) hR0 (w:=(x,y)) ax ay
        ⟨fun _ => ?_,fun e => by simp at e⟩ ((SingleWindow.sees_iff fill closed convex hR zL).mp sees)
      rw [hcR]
      have d := det_lineX (p:=R) (c:=cR) (show R.2<cR.2 from rLow) x y
      have e : ArtGallery.det (x,y) R cR=ArtGallery.det R cR (x,y) := by simp only [ArtGallery.det]; ring
      rw [e,d]
      have : lineX R cR y<x := by rw [lin]; exact right
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith))
    (fun x y h0 h1 hy left => by
      simp only [Bool.false_eq_true,ite_false] at hy
      apply blockB x y h0 h1 (by linarith) hy.2
      rw [lin]; exact left)
    (fun gapl => by
      have mR : lineX R cR a=lineX (Bx+tR,By) cB a := (matched tR).symm
      rw [mR,Aaff,Aaff] at gapl
      have lt : tB<tR := by nlinarith
      refine ⟨lineX (Bx+(tB+tR)/2,By) cB a,(cB.1-(Bx+(tB+tR)/2))/(cB.2-By),?_,?_,?_⟩
      · rw [mR,Aaff,Aaff]; nlinarith
      · show lineX (Bx+(tB+tR)/2,By) cB a<lineX B cB a
        simp only [B]; rw [Aaff,Aaff]; nlinarith
      · intro g hg e1 e2 y h0 h1 hy
        simp only [Bool.false_eq_true,ite_false] at hy
        have e : lineX (Bx+(tB+tR)/2,By) cB a+(cB.1-(Bx+(tB+tR)/2))/(cB.2-By)*(y-a)=
            lineX (Bx+(tB+tR)/2,By) cB y := by rw [lin (Bx+(tB+tR)/2,By) cB y]
        rw [e] at h0 h1 ⊢
        exact others g hg e2 e1 ((tB+tR)/2) (by linarith) (by linarith) y (by linarith) hy.2 h0 h1)
    ha hb
  -- matched rays: the base line is decreasing in its parameter
  have mt := matched tR
  have slope : lineX (Bx+tB,By) cB a-lineX (Bx+tR,By) cB a=(tB-tR)*((cB.2-a)/(cB.2-By)) := by
    have hne : cB.2-By≠0 := by linarith
    unfold lineX; simp only; field_simp; ring
  have neg : (cB.2-a)/(cB.2-By)<0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have : (tB-tR)*((cB.2-a)/(cB.2-By))≤0 := by rw [←slope,mt]; linarith
  nlinarith

/-- The lower test with the base guard given only through its blocked side. -/
theorem lower_blocked {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1))
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb : Index} {kR : Nat} {first : Bool} {pairs : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR false first pairs=true)
    {cx d r b D tB tR H : ℝ} {Bg : Point}
    (hu : gridPt X Y (if first then C.next kR else C.node kR)=(cx,1))
    (hra : gridPt X Y ra=(cx+d*r,1-d)) (hrb : gridPt X Y rb=(cx+d*(r+3/(2*D)),1-d))
    (hD : 0<D) (hH : 0<H) (hd : 0<d) (axis : Y.getD iy 0=1+H)
    (ht : 0≤tR ∧ tR≤3/2) (hR : ((cx+d*(r+tR/D),1-d):Point)∈(C.poly X Y).filled)
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → 1+H<y → y<Y.getD (iy+1) 0 →
      W-(b+tB/D)*(y-1)<x → ¬P.Sees Bg (x,y))
    (others : ∀ g∈Gs, g≠Bg → g≠(cx+d*(r+tR/D),1-d) → ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 →
      1+H<y → y<Y.getD (iy+1) 0 → W-(b+tB/D)*(y-1)<x → x<cx-(r+tR/D)*(y-1) → ¬P.Sees g (x,y))
    (incidence : W-b*H=cx-r*H)
    (ha : X.getD xc 0<W-(b+tB/D)*H) (hb : cx-(r+tR/D)*H<X.getD (xc+1) 0) : tB≤tR := by
  have gap : 0<Y.getD (iy+1) 0-Y.getD iy 0 := by
    have := level_lt G.hy hiy (Nat.lt_succ_self iy); linarith
  have sub : (C.poly X Y).filled⊆P.filled := by rw [fill]; exact subset_union_left
  have atoms (x y : ℝ) (h0 : X.getD xc 0<x) (h1 : x<X.getD (xc+1) 0) (y0 : 1+H<y)
      (y1 : y<1+H+(Y.getD (iy+1) 0-Y.getD iy 0)) : atom x X=2*xc+2 ∧ atom y Y=2*iy+2 :=
    ⟨atom_between G.hx hxc h0 h1,atom_between G.hy hiy (by rw [axis]; exact y0) (by linarith)⟩
  let R : Point := (cx+d*(r+tR/D),1-d)
  have key := CopyGap.no_gap (P:=P) (G:=Gs) cover (p:=Bg) (q:=R)
    (a:=1+H) (ε:=Y.getD (iy+1) 0-Y.getD iy 0) (xa:=X.getD xc 0) (xb:=X.getD (xc+1) 0)
    (αp:=W-(b+tB/D)*H) (βp:=-(b+tB/D)) (αq:=cx-(r+tR/D)*H) (βq:=-(r+tR/D)) true gap
    (fun x y h0 h1 hy => by
      simp only [ite_true] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      exact sub (tile_filled G tile (z:=(x,y)) ax ay))
    (fun x y h0 h1 hy right => by
      simp only [ite_true] at hy
      apply blockB x y h0 h1 hy.1 (by linarith)
      have : W-(b+tB/D)*(y-1)=W-(b+tB/D)*H+-(b+tB/D)*(y-(1+H)) := by ring
      rw [this]; exact right)
    (fun x y h0 h1 hy left => by
      simp only [ite_true] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 hy.2
      intro sees
      have convex : Convex ℝ ((C.poly X Y).filled∩rest) := contact ▸ Geometry.segment_convex _ _
      have zL := tile_filled G tile (z:=(x,y)) ax ay
      apply crossOne_sound G rcert (z:=R) (by rw [hra,hrb]; exact receiver_on_spot hD ht)
        (w:=(x,y)) ax ay ⟨fun e => by simp at e,fun _ => ?_⟩ ((SingleWindow.sees_iff fill closed convex hR zL).mp sees)
      rw [hu]; apply receiver_det hd
      have : cx-(r+tR/D)*(y-1)=cx-(r+tR/D)*H+-(r+tR/D)*(y-(1+H)) := by ring
      rw [this]; exact left)
    (fun g hg e1 e2 x y h0 h1 hy lo hi => by
      simp only [ite_true] at hy
      exact others g hg e1 e2 x y h0 h1 hy.1 (by linarith)
        (by have : W-(b+tB/D)*(y-1)=W-(b+tB/D)*H+-(b+tB/D)*(y-(1+H)) := by ring
            rw [this]; exact lo)
        (by have : cx-(r+tR/D)*(y-1)=cx-(r+tR/D)*H+-(r+tR/D)*(y-(1+H)) := by ring
            rw [this]; exact hi))
    ha hb
  have : tB*(H/D)≤tR*(H/D) := by
    have e : cx-(r+tR/D)*H-(W-(b+tB/D)*H)=(tB-tR)*(H/D) := by
      field_simp; linear_combination (-D)*incidence
    nlinarith
  exact le_of_mul_le_mul_right this (div_pos hH hD)

/-- The base guard on the floor is blocked beyond its ray through the right door corner. -/
theorem base_blocked {P L : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=L.filled∪rest)
    (closed : IsClosed rest) (contact : L.filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {b D tB : ℝ} (hD : 0<D) (hB : ((W+b*D+tB,1-D):Point)∈rest) {x y : ℝ} (hz : (x,y)∈L.filled)
    (right : W-(b+tB/D)*(y-1)<x) : ¬P.Sees (W+b*D+tB,1-D) (x,y) :=
  CopyDoor.beyond_right fill closed contact hW hB (by simp; linarith) hz (CopyTest.base_side hD right)

/-- The base guard on the floor is blocked left of its ray through the certified corner `cB`. -/
theorem base_blocked_upper {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {cell : Nat × Nat} (tile : inTile C.tiles cell=true)
    {dl dr : Index} (hdl : gridPt X Y dl=((0:ℝ),(1:ℝ))) (hdr : gridPt X Y dr=(W,1))
    {kB : Nat} {fB : Bool} {pB : List (Sign × Sign)} (bcert : crossOne C dl dr cell kB false fB pB=true)
    {cB B : Point} (hcB : gridPt X Y (if fB then C.next kB else C.node kB)=cB)
    (hB : B∈rest) (bLow : B.2<cB.2) {x y : ℝ} (ax : atom x X=cell.1) (ay : atom y Y=cell.2) (hy : 1<y)
    (left : x<lineX B cB y) : ¬P.Sees B (x,y) := by
  have zL := tile_filled G tile (z:=(x,y)) ax ay
  apply CopyDoor.through_door fill closed contact hW (σ:=1) (c:=cB) hB zL (by simpa using hy)
  · rw [one_mul]
    have d := det_lineX bLow x y
    have e : ArtGallery.det (x,y) B cB=ArtGallery.det B cB (x,y) := by simp only [ArtGallery.det]; ring
    rw [e,d]
    exact mul_pos (by linarith) (by linarith)
  · intro q hq pos
    rw [one_mul] at pos
    apply crossOne_sound G bcert (z:=q) (by rw [hdl,hdr]; exact hq) (w:=(x,y)) ax ay
    exact ⟨fun e => by simp at e,fun _ => by rw [hcB]; exact pos⟩

/-- The two polynomial conditions of matched rays: constant and parameter coefficients. -/
def E0 (Bx By cBx cBy a Rx Ry cRx cRy : ℝ) : ℝ :=
  (Bx*(cBy-By)+(cBx-Bx)*(a-By))*(cRy-Ry)-(Rx*(cRy-Ry)+(cRx-Rx)*(a-Ry))*(cBy-By)
def E1 (By cBy a Ry cRy κ : ℝ) : ℝ := (cBy-a)*(cRy-Ry)-κ*(cRy-a)*(cBy-By)

theorem matched_of {Bx By cBx cBy a Rx Ry cRx cRy κ : ℝ} (hB : cBy≠By) (hR : cRy≠Ry)
    (h0 : E0 Bx By cBx cBy a Rx Ry cRx cRy=0) (h1 : E1 By cBy a Ry cRy κ=0) (t : ℝ) :
    lineX (Bx+t,By) (cBx,cBy) a=lineX (Rx+κ*t,Ry) (cRx,cRy) a := by
  unfold E0 at h0; unfold E1 at h1
  have hB' : cBy-By≠0 := sub_ne_zero.mpr hB
  have hR' : cRy-Ry≠0 := sub_ne_zero.mpr hR
  unfold lineX; simp only
  field_simp
  linear_combination h0+t*h1

end ArtGallery.Orthogonal.BoundaryPoint.CopyChannel
end
