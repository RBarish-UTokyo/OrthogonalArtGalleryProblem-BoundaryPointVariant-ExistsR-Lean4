module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyUpper
public import ArtGallery.Orthogonal.BoundaryPoint.CellRoles
public import ArtGallery.Orthogonal.BoundaryPoint.CellHalf

/-! # The copy tests with the same-wing roles excluded by cell certificates

Every guard other than the base and the receiver either stands on the spot of
another role of the same wing, and the cell certificates exclude it from the
whole target cell, or it is an outside guard excluded at the points between
the two sight lines. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRoles
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CellCert CellRoles CopyChannel CopyLower CopyUpper
  ArtGallery.Orthogonal.Hard

/-- A same-wing guard on the spot of another role sees no point of the open target cell. -/
theorem same_wing {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1))
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {roles : List (List Index)} {rr : Nat} {es : List (Option CellEx)}
    (hall : allOK C (2*xc+2,2*iy+2) rr 0 roles es=true)
    (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2))
    {j : Nat} (hj : j<roles.length) (ne : j≠rr) {g : Point}
    (hg : g∈ArtGallery.segment (gridPt X Y (spotA roles[j])) (gridPt X Y (spotB roles[j])))
    (gL : g∈(C.poly X Y).filled) {x y : ℝ} (h0 : X.getD xc 0<x) (h1 : x<X.getD (xc+1) 0)
    (y0 : Y.getD iy 0<y) (y1 : y<Y.getD (iy+1) 0) : ¬P.Sees g (x,y) := by
  have ax : atom x X=2*xc+2 := atom_between G.hx hxc h0 h1
  have ay : atom y Y=2*iy+2 := atom_between G.hy hiy y0 y1
  have zL := tile_filled G tile (z:=(x,y)) ax ay
  have convex : Convex ℝ ((C.poly X Y).filled∩rest) := contact ▸ Geometry.segment_convex _ _
  rw [SingleWindow.sees_iff fill closed convex gL zL]
  exact CellRoles.others G hall hc hj ne hg ax ay

/-- A same-wing guard on the spot of another role sees no point of the bottom strip of the open
target cell (nook test certificates). -/
theorem same_wingL {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1))
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {roles : List (List Index)} {rr : Nat} {es : List (Option CellHalf.CellExL)}
    (hall : CellHalf.allOKL C xc iy rr 0 roles es=true)
    (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2))
    {j : Nat} (hj : j<roles.length) (ne : j≠rr) {g : Point}
    (hg : g∈ArtGallery.segment (gridPt X Y (spotA roles[j])) (gridPt X Y (spotB roles[j])))
    (gL : g∈(C.poly X Y).filled) {x y : ℝ} (h0 : X.getD xc 0<x) (h1 : x<X.getD (xc+1) 0)
    (y0 : Y.getD iy 0<y) (y1 : y<Y.getD iy 0+(Y.getD (iy+1) 0-Y.getD iy 0)/256) : ¬P.Sees g (x,y) := by
  have gap := SepGeom.level_lt G.hy hiy (Nat.lt_succ_self iy)
  have ax : atom x X=2*xc+2 := atom_between G.hx hxc h0 h1
  have ay : atom y Y=2*iy+2 := atom_between G.hy hiy y0 (by linarith)
  have zL := tile_filled G tile (z:=(x,y)) ax ay
  have convex : Convex ℝ ((C.poly X Y).filled∩rest) := contact ▸ Geometry.segment_convex _ _
  rw [SingleWindow.sees_iff fill closed convex gL zL]
  exact CellHalf.othersL G hall hc hj ne hg h0 h1 y0 y1

/-- The nook test with same-wing roles excluded by cell certificates and all other guards
given as outside guards excluded between the two rays. -/
theorem lower_chart {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1))
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb win : Index} {kR : Nat} {first : Bool} {pairs : List (SepCert.Sign × SepCert.Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR false first pairs=true)
    (hu : (if first then C.next kR else C.node kR)=win)
    {roles : List (List Index)} {rr : Nat} {es : List (Option CellHalf.CellExL)}
    (hall : CellHalf.allOKL C xc iy rr 0 roles es=true)
    (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2))
    (hwx : X.getD win.1 0=301/2) (hwy : Y.getD win.2 0=1)
    (hyr : rb.2=ra.2) (o1 : ra.2<win.2) (o2 : win.2 < iy)
    {b D : ℝ} (hD : 0<D)
    (hrb : X.getD rb.1 0=X.getD ra.1 0+3/2*(1-Y.getD ra.2 0)/D)
    (deep : 0<(1:ℝ)*D+(-1:ℝ)*(Y.getD (iy+1) 0)+(1:ℝ)*(1))
    (L1 : 0<ArtGallery.det (X.getD rb.1 0,Y.getD rb.2 0) (X.getD win.1 0,Y.getD win.2 0) (X.getD xc 0,Y.getD iy 0))
    (L2 : ArtGallery.det (X.getD ra.1 0,Y.getD ra.2 0) (X.getD win.1 0,Y.getD win.2 0) (X.getD (xc+1) 0,Y.getD iy 0)<0)
    (incidence : W-b*(Y.getD iy 0-1)=301/2-((X.getD ra.1 0-301/2)/(1-Y.getD ra.2 0))*(Y.getD iy 0-1))
    {tB tR : ℝ} (htB : 0≤tB ∧ tB≤3/2) (htR : 0≤tR ∧ tR≤3/2) {Bg : Point}
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      W-(b+tB/D)*(y-1)<x → ¬P.Sees Bg (x,y))
    (hR : receiver X Y ra rb tR∈(C.poly X Y).filled)
    (owned : ∀ g∈Gs, g≠Bg → g≠receiver X Y ra rb tR →
      (∃ k, ∃ hk : k<roles.length, k≠rr ∧
        g∈ArtGallery.segment (gridPt X Y (spotA roles[k])) (gridPt X Y (spotB roles[k])) ∧ g∈(C.poly X Y).filled) ∨
      (∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
        W-(b+tB/D)*(y-1)<x → x<lineX (receiver X Y ra rb tR) (gridPt X Y win) y → ¬P.Sees g (x,y))) :
    tB≤tR := by
  have hwin : gridPt X Y win=((301/2:ℝ),(1:ℝ)) := by simp only [gridPt,hwx,hwy]
  have rlow : (gridPt X Y ra).2<1 := by
    simp only [gridPt]; rw [←hwy]; exact SepGeom.level_lt G.hy (by omega) o1
  have hy0 : 1<Y.getD iy 0 := by rw [←hwy]; exact SepGeom.level_lt G.hy (by omega) o2
  apply lower_test G fill closed contact cover hxc hiy tile rcert hu hwin (by simp only [gridPt,hyr]) rlow hy0 hD
    (by simp only [gridPt]; exact hrb) (by linarith) L1 L2 (by simp only [gridPt]; exact incidence) htB htR blockB hR
  intro g hg e1 e2 x y h0 h1 y0 y1 lo hi
  rcases owned g hg e1 e2 with ⟨k,hk,ne,hseg,gL⟩|out
  · exact same_wingL G fill closed contact hxc hiy tile hall hc hk ne hseg gL h0 h1 y0 y1
  · have gap := SepGeom.level_lt G.hy hiy (Nat.lt_succ_self iy)
    exact out x y h0 h1 y0 (by linarith) lo hi

/-- The chamber test with same-wing roles excluded by cell certificates and all other guards
given as outside guards excluded on the base rays through the corner `cB`. -/
theorem upper_chart {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb cRn cBn win : Index} {kR : Nat} {fR : Bool} {pR : List (SepCert.Sign × SepCert.Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR true fR pR=true)
    (hcRn : (if fR then C.next kR else C.node kR)=cRn)
    {roles : List (List Index)} {rr : Nat} {es : List (Option CellEx)}
    (hall : allOK C (2*xc+2,2*iy+2) rr 0 roles es=true)
    (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2))
    (hwy : Y.getD win.2 0=1) (hyr : rb.2=ra.2) (o1 : win.2 < iy) (o2 : ra.2 < cRn.2) (o3 : cBn.2 < iy+1)
    (o4 : cRn.2 < Y.length)
    {Bx By tB tR : ℝ} (htB : 0≤tB ∧ tB≤3/2) (htR : 0≤tR ∧ tR≤3/2) {Bg : Point}
    (hR : receiver X Y ra rb tR∈(C.poly X Y).filled)
    (bLow : 0<(1:ℝ)*(Y.getD cBn.2 0)+(-1:ℝ)*By)
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      x<lineX (Bx+tB,By) (gridPt X Y cBn) y → ¬P.Sees Bg (x,y))
    (matched : ∀ t : ℝ, lineX (Bx+t,By) (X.getD cBn.1 0,Y.getD cBn.2 0) (Y.getD (iy+1) 0)=
      lineX (X.getD ra.1 0+2/3*(X.getD rb.1 0-X.getD ra.1 0)*t,Y.getD ra.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (Y.getD (iy+1) 0))
    (Ua0 : 0<ArtGallery.det (X.getD ra.1 0,Y.getD ra.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD xc 0,Y.getD (iy+1) 0))
    (Ua1 : 0<ArtGallery.det (X.getD rb.1 0,Y.getD rb.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD xc 0,Y.getD (iy+1) 0))
    (Ub0 : ArtGallery.det (X.getD ra.1 0,Y.getD ra.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD (xc+1) 0,Y.getD (iy+1) 0)<0)
    (Ub1 : ArtGallery.det (X.getD rb.1 0,Y.getD rb.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD (xc+1) 0,Y.getD (iy+1) 0)<0)
    (owned : ∀ g∈Gs, g≠Bg → g≠receiver X Y ra rb tR →
      (∃ k, ∃ hk : k<roles.length, k≠rr ∧
        g∈ArtGallery.segment (gridPt X Y (spotA roles[k])) (gridPt X Y (spotB roles[k])) ∧ g∈(C.poly X Y).filled) ∨
      (∀ t' : ℝ, tB<t' → t'<tR → ∀ y : ℝ, Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
        X.getD xc 0<lineX (Bx+t',By) (gridPt X Y cBn) y → lineX (Bx+t',By) (gridPt X Y cBn) y<X.getD (xc+1) 0 →
        ¬P.Sees g (lineX (Bx+t',By) (gridPt X Y cBn) y,y))) :
    tR≤tB := by
  have above : 1<Y.getD iy 0 := by rw [←hwy]; exact SepGeom.level_lt G.hy (by omega) o1
  have rLow : (gridPt X Y ra).2<(gridPt X Y cRn).2 := by
    simp only [gridPt]; exact SepGeom.level_lt G.hy o4 o2
  have axisB : (gridPt X Y cBn).2<Y.getD (iy+1) 0 := by
    simp only [gridPt]; exact SepGeom.level_lt G.hy hiy o3
  apply upper_test_mid G fill closed contact hW cover hxc hiy tile rcert hcRn (by simp only [gridPt,hyr]) htB htR hR
    above (by simp only [gridPt]; linarith) rLow axisB blockB _ (fun t => matched t) Ua0 Ua1 Ub0 Ub1
  intro g hg e1 e2 t' h1 h2 y y0 y1 x0 x1
  rcases owned g hg e1 e2 with ⟨k,hk,ne,hseg,gL⟩|out
  · exact same_wing G fill closed contact hxc hiy tile hall hc hk ne hseg gL x0 x1 y0 y1
  · exact out t' h1 h2 y y0 y1 x0 x1

/-- An outside guard blind to every wing point above height `7/3` on a sight line from a base
position `W+b*D+τ` on the floor `1-D` through a door point `(c,1)`. -/
def Blind (P : Polygon) (L : Set Point) (W b D : ℝ) (g : Point) : Prop :=
  ∀ τ c y : ℝ, 0≤τ → τ≤3/2 → 0≤c → c≤W → 7/3≤y →
    ((c+(c-(W+b*D+τ))*(y-1)/D,y):Point)∈L → ¬P.Sees g (c+(c-(W+b*D+τ))*(y-1)/D,y)

/-- Nook targets between the two rays lie on a door-corner ray of a base position. -/
theorem lower_on_ray {W b D r H tB tR x y : ℝ} (hD : 0<D) (hH : 0<H) (hW : W<301/2)
    (inc : W-b*H=301/2-r*H) (htB : tB≤3/2) (htR : 0≤tR) (hy : 1+H<y)
    (lo : W-(b+tB/D)*(y-1)<x) (hi : x<301/2-(r+tR/D)*(y-1)) :
    ∃ τ : ℝ, 0≤τ ∧ τ≤3/2 ∧ x=W+(W-(W+b*D+τ))*(y-1)/D := by
  have hy1 : 0<y-1 := by linarith
  refine ⟨D*((W-x)/(y-1)-b),?_,?_,?_⟩
  · -- the ray of the receiver lies right of the base ray of offset 0 above the axis
    have key : (W-x)/(y-1)-b>tR/D+(r-b)*(1-H/(y-1)) := by
      rw [gt_iff_lt,lt_sub_iff_add_lt,lt_div_iff₀ hy1]
      have e : (tR/D+(r-b)*(1-H/(y-1))+b)*(y-1)=(r+tR/D)*(y-1)-(r-b)*H := by field_simp; ring
      rw [e]; linarith
    have rb : 0≤r-b := by nlinarith
    have q : 0≤1-H/(y-1) := by rw [sub_nonneg,div_le_one hy1]; linarith
    have : 0≤tR/D+(r-b)*(1-H/(y-1)) := add_nonneg (div_nonneg htR hD.le) (mul_nonneg rb q)
    nlinarith
  · have : (W-x)/(y-1)-b<tB/D := by
      rw [sub_lt_iff_lt_add,div_lt_iff₀ hy1]; nlinarith
    calc D*((W-x)/(y-1)-b)≤D*(tB/D) := by nlinarith
      _ = tB := by field_simp
      _ ≤ 3/2 := htB
  · field_simp; ring

/-- A line from a point below the door line through a corner above it crosses the door line at
`lineX p c 1`, strictly between `0` and `W` when the door corners lie on opposite sides. -/
theorem door_crossing {p c : Point} {W : ℝ} (h : p.2<c.2)
    (l : 0<ArtGallery.det p c ((0:ℝ),(1:ℝ))) (r : ArtGallery.det p c (W,(1:ℝ))<0) :
    0<lineX p c 1 ∧ lineX p c 1<W := by
  have dl := det_lineX h (0:ℝ) (1:ℝ)
  have dr := det_lineX h W (1:ℝ)
  rw [dl] at l; rw [dr] at r
  have hc : 0<c.2-p.2 := by linarith
  constructor
  · have := pos_of_mul_pos_right l hc.le; linarith
  · have : lineX p c 1-W<0 := by
      by_contra hn; push Not at hn; nlinarith
    linarith

/-- The point at height `y` of the line from `p` through `c` lies on the line from `p` through
the door crossing. -/
theorem through_crossing {p c : Point} (h : p.2<1) (h' : p.2<c.2) (y : ℝ) :
    lineX p c y=lineX p c 1+(lineX p c 1-p.1)*(y-1)/(1-p.2) := by
  unfold lineX
  have h1 : c.2-p.2≠0 := by linarith
  have h2 : 1-p.2≠0 := by linarith
  field_simp; ring

/-- The nook test with outside guards given as blind guards. -/
theorem lower_chart2 {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW0 : 0≤W) (hW : W<301/2)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb win : Index} {kR : Nat} {first : Bool} {pairs : List (SepCert.Sign × SepCert.Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR false first pairs=true)
    (hu : (if first then C.next kR else C.node kR)=win)
    {roles : List (List Index)} {rr : Nat} {es : List (Option CellHalf.CellExL)}
    (hall : CellHalf.allOKL C xc iy rr 0 roles es=true)
    (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2))
    (hwx : X.getD win.1 0=301/2) (hwy : Y.getD win.2 0=1)
    (hyr : rb.2=ra.2) (o1 : ra.2<win.2) (o2 : win.2 < iy)
    {b D : ℝ} (hD : 0<D)
    (hrb : X.getD rb.1 0=X.getD ra.1 0+3/2*(1-Y.getD ra.2 0)/D)
    (deep : 0<(1:ℝ)*D+(-1:ℝ)*(Y.getD (iy+1) 0)+(1:ℝ)*(1))
    (L1 : 0<ArtGallery.det (X.getD rb.1 0,Y.getD rb.2 0) (X.getD win.1 0,Y.getD win.2 0) (X.getD xc 0,Y.getD iy 0))
    (L2 : ArtGallery.det (X.getD ra.1 0,Y.getD ra.2 0) (X.getD win.1 0,Y.getD win.2 0) (X.getD (xc+1) 0,Y.getD iy 0)<0)
    (H43 : 0<(3:ℝ)*(Y.getD iy 0)+(-7:ℝ)*(1))
    (incidence : W-b*(Y.getD iy 0-1)=301/2-((X.getD ra.1 0-301/2)/(1-Y.getD ra.2 0))*(Y.getD iy 0-1))
    {tB tR : ℝ} (htB : 0≤tB ∧ tB≤3/2) (htR : 0≤tR ∧ tR≤3/2) {Bg : Point}
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      W-(b+tB/D)*(y-1)<x → ¬P.Sees Bg (x,y))
    (hR : receiver X Y ra rb tR∈(C.poly X Y).filled)
    (owned : ∀ g∈Gs, g≠Bg → g≠receiver X Y ra rb tR →
      (∃ k, ∃ hk : k<roles.length, k≠rr ∧
        g∈ArtGallery.segment (gridPt X Y (spotA roles[k])) (gridPt X Y (spotB roles[k])) ∧ g∈(C.poly X Y).filled) ∨
      Blind P (C.poly X Y).filled W b D g) :
    tB≤tR := by
  have hy0 : 1<Y.getD iy 0 := by rw [←hwy]; exact SepGeom.level_lt G.hy (by omega) o2
  have rlow : Y.getD ra.2 0<1 := by rw [←hwy]; exact SepGeom.level_lt G.hy (by omega) o1
  set d := 1-Y.getD ra.2 0
  have hd : 0<d := by simp only [d]; linarith
  set r := (X.getD ra.1 0-301/2)/d
  have hrx : X.getD ra.1 0=301/2+d*r := by simp only [r]; field_simp; ring
  apply lower_chart G fill closed contact cover hxc hiy tile rcert hu hall hc hwx hwy hyr o1 o2 hD hrb deep L1 L2
    incidence htB htR blockB hR
  intro g hg e1 e2
  rcases owned g hg e1 e2 with h|blind
  · exact Or.inl h
  · right
    intro x y h0 h1 y0 y1 lo hi
    have hrec : receiver X Y ra rb tR=(301/2+d*(r+tR/D),1-d) := by
      unfold receiver; simp only [gridPt]; rw [hrb,hrx]; ext <;> simp only [d] <;> field_simp <;> ring
    have hwin : gridPt X Y win=((301/2:ℝ),(1:ℝ)) := by simp only [gridPt,hwx,hwy]
    rw [hrec,hwin,lineX_floor hd.ne'] at hi
    obtain ⟨τ,τ0,τ1,hx⟩ := lower_on_ray hD (by linarith) hW incidence htB.2 htR.1 (by linarith) lo hi
    have zL : (x,y)∈(C.poly X Y).filled :=
      tile_filled G tile (z:=(x,y)) (atom_between G.hx hxc h0 h1) (atom_between G.hy hiy y0 y1)
    have := blind τ W y τ0 τ1 (by linarith) le_rfl (by linarith) (by rw [←hx]; exact zL)
    rwa [←hx] at this

/-- Interpolating a determinant sign between the base offsets `0` and `3/2`. -/
theorem det_base {Bx By t : ℝ} (ht0 : 0≤t) (ht1 : t≤3/2) (c w : Point) {σ : ℝ}
    (h0 : 0<σ*ArtGallery.det (Bx,By) c w) (h1 : 0<σ*ArtGallery.det (Bx+3/2,By) c w) :
    0<σ*ArtGallery.det (Bx+t,By) c w := by
  have e : ArtGallery.det (Bx+t,By) c w=(1-2/3*t)*ArtGallery.det (Bx,By) c w+2/3*t*ArtGallery.det (Bx+3/2,By) c w := by
    simp only [ArtGallery.det]; ring
  rw [e]
  have l0 : 0≤1-2/3*t := by linarith
  have l1 : 0≤2/3*t := by linarith
  have : σ*((1-2/3*t)*ArtGallery.det (Bx,By) c w+2/3*t*ArtGallery.det (Bx+3/2,By) c w)=
      (1-2/3*t)*(σ*ArtGallery.det (Bx,By) c w)+2/3*t*(σ*ArtGallery.det (Bx+3/2,By) c w) := by ring
  rw [this]
  rcases eq_or_lt_of_le l0 with e0|e0
  · rw [←e0]; have : 0<2/3*t := by linarith
    nlinarith
  · nlinarith

/-- The chamber test with outside guards given as blind guards. -/
theorem upper_chart2 {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb cRn cBn win : Index} {kR : Nat} {fR : Bool} {pR : List (SepCert.Sign × SepCert.Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR true fR pR=true)
    (hcRn : (if fR then C.next kR else C.node kR)=cRn)
    {roles : List (List Index)} {rr : Nat} {es : List (Option CellEx)}
    (hall : allOK C (2*xc+2,2*iy+2) rr 0 roles es=true)
    (hc : Inner C.nx (2*xc+2) ∧ Inner C.ny (2*iy+2))
    (hwy : Y.getD win.2 0=1) (hyr : rb.2=ra.2) (o1 : win.2 < iy) (o2 : ra.2 < cRn.2) (o3 : cBn.2 < iy+1)
    (o4 : cRn.2 < Y.length)
    {b D tB tR : ℝ} (hD : 0<D) (htB : 0≤tB ∧ tB≤3/2) (htR : 0≤tR ∧ tR≤3/2) {Bg : Point}
    (hR : receiver X Y ra rb tR∈(C.poly X Y).filled)
    (bLow : 0<(1:ℝ)*(Y.getD cBn.2 0)+(-1:ℝ)*(1-D))
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      x<lineX (W+b*D+tB,1-D) (gridPt X Y cBn) y → ¬P.Sees Bg (x,y))
    (matched : ∀ t : ℝ, lineX (W+b*D+t,1-D) (X.getD cBn.1 0,Y.getD cBn.2 0) (Y.getD (iy+1) 0)=
      lineX (X.getD ra.1 0+2/3*(X.getD rb.1 0-X.getD ra.1 0)*t,Y.getD ra.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (Y.getD (iy+1) 0))
    (Ua0 : 0<ArtGallery.det (X.getD ra.1 0,Y.getD ra.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD xc 0,Y.getD (iy+1) 0))
    (Ua1 : 0<ArtGallery.det (X.getD rb.1 0,Y.getD rb.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD xc 0,Y.getD (iy+1) 0))
    (Ub0 : ArtGallery.det (X.getD ra.1 0,Y.getD ra.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD (xc+1) 0,Y.getD (iy+1) 0)<0)
    (Ub1 : ArtGallery.det (X.getD rb.1 0,Y.getD rb.2 0) (X.getD cRn.1 0,Y.getD cRn.2 0) (X.getD (xc+1) 0,Y.getD (iy+1) 0)<0)
    (H43u : 0<(3:ℝ)*(Y.getD iy 0)+(-7:ℝ)*(1))
    (DL0 : 0<ArtGallery.det (W+b*D,1-D) (X.getD cBn.1 0,Y.getD cBn.2 0) (0,1))
    (DL1 : 0<ArtGallery.det (W+b*D+3/2,1-D) (X.getD cBn.1 0,Y.getD cBn.2 0) (0,1))
    (DR0 : ArtGallery.det (W+b*D,1-D) (X.getD cBn.1 0,Y.getD cBn.2 0) (W,1)<0)
    (DR1 : ArtGallery.det (W+b*D+3/2,1-D) (X.getD cBn.1 0,Y.getD cBn.2 0) (W,1)<0)
    (owned : ∀ g∈Gs, g≠Bg → g≠receiver X Y ra rb tR →
      (∃ k, ∃ hk : k<roles.length, k≠rr ∧
        g∈ArtGallery.segment (gridPt X Y (spotA roles[k])) (gridPt X Y (spotB roles[k])) ∧ g∈(C.poly X Y).filled) ∨
      Blind P (C.poly X Y).filled W b D g) :
    tR≤tB := by
  apply upper_chart G fill closed contact hW cover hxc hiy tile rcert hcRn hall hc hwy hyr o1 o2 o3 o4 htB htR hR bLow
    blockB matched Ua0 Ua1 Ub0 Ub1
  intro g hg e1 e2
  rcases owned g hg e1 e2 with h|blind
  · exact Or.inl h
  · right
    intro t' h1 h2 y y0 y1 x0 x1
    have t0 : 0≤t' := by linarith
    have t1 : t'≤3/2 := by linarith
    have hlow : (W+b*D+t',1-D).2<(X.getD cBn.1 0,Y.getD cBn.2 0).2 := by simp only; linarith
    have dl := det_base (Bx:=W+b*D) (By:=1-D) t0 t1 (X.getD cBn.1 0,Y.getD cBn.2 0) ((0:ℝ),(1:ℝ)) (σ:=1) (by rw [one_mul]; exact DL0)
      (by rw [one_mul]; exact DL1)
    have dr := det_base (Bx:=W+b*D) (By:=1-D) t0 t1 (X.getD cBn.1 0,Y.getD cBn.2 0) (W,(1:ℝ)) (σ:=-1) (by linarith) (by linarith)
    rw [one_mul] at dl
    obtain ⟨c0,c1⟩ := door_crossing hlow dl (by linarith)
    have hz := through_crossing (p:=(W+b*D+t',1-D)) (c:=(X.getD cBn.1 0,Y.getD cBn.2 0)) (by simp only; linarith) hlow y
    simp only [sub_sub_cancel] at hz
    have zL : (lineX (W+b*D+t',1-D) (X.getD cBn.1 0,Y.getD cBn.2 0) y,y)∈(C.poly X Y).filled :=
      tile_filled G tile (z:=(_,y)) (atom_between G.hx hxc x0 x1) (atom_between G.hy hiy y0 y1)
    have := blind t' (lineX (W+b*D+t',1-D) (X.getD cBn.1 0,Y.getD cBn.2 0) 1) y t0 t1 c0.le c1.le (by linarith)
      (by rw [←hz]; exact zL)
    rwa [←hz] at this

end ArtGallery.Orthogonal.BoundaryPoint.CopyRoles
end
