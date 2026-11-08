module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyLower

/-! # The chamber test in chart terms

The receiver moves on its spot `[ra,rb]` and sees the target cell (just below the
chamber axis `y=Y[iy+1]`) only right of its ray through the corner node `cR`;
the base sees it only left of its ray through `cB`. With matched rays, four
determinant signs at the two upper corners of the cell (for both spot ends) give
the range conditions of `CopyChannel.upper_blocked`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyUpper
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CellCert CopyChannel CopyLower ArtGallery.Orthogonal.Hard

/-- The determinant is affine in its first point. -/
theorem det_lerp (p q c w : Point) (l : ℝ) :
    ArtGallery.det ((1-l)*p.1+l*q.1,(1-l)*p.2+l*q.2) c w=(1-l)*ArtGallery.det p c w+l*ArtGallery.det q c w := by
  simp only [ArtGallery.det]; ring

theorem receiver_lerp {X Y : List ℝ} {ra rb : Index} (hyr : (gridPt X Y rb).2=(gridPt X Y ra).2) (t : ℝ) :
    receiver X Y ra rb t=((1-2/3*t)*(gridPt X Y ra).1+2/3*t*(gridPt X Y rb).1,
      (1-2/3*t)*(gridPt X Y ra).2+2/3*t*(gridPt X Y rb).2) := by
  unfold receiver; rw [hyr]; ext <;> simp only <;> ring

theorem receiver_seg {X Y : List ℝ} {ra rb : Index} (hyr : (gridPt X Y rb).2=(gridPt X Y ra).2) {t : ℝ}
    (ht : 0≤t ∧ t≤3/2) : receiver X Y ra rb t∈ArtGallery.segment (gridPt X Y ra) (gridPt X Y rb) := by
  refine ⟨2/3*t,by linarith,by linarith,?_⟩
  unfold receiver; rw [hyr]; ext <;> simp <;> ring

/-- A determinant sign at both spot ends holds along the spot. -/
theorem det_along {X Y : List ℝ} {ra rb : Index} (hyr : (gridPt X Y rb).2=(gridPt X Y ra).2) {t : ℝ}
    (ht : 0≤t ∧ t≤3/2) {c w : Point} {σ : ℝ}
    (h0 : 0<σ*ArtGallery.det (gridPt X Y ra) c w) (h1 : 0<σ*ArtGallery.det (gridPt X Y rb) c w) :
    0<σ*ArtGallery.det (receiver X Y ra rb t) c w := by
  rw [receiver_lerp hyr,det_lerp]
  have l0 : 0≤1-2/3*t := by linarith
  have l1 : 0≤2/3*t := by linarith
  have : σ*((1-2/3*t)*ArtGallery.det (gridPt X Y ra) c w+2/3*t*ArtGallery.det (gridPt X Y rb) c w)=
      (1-2/3*t)*(σ*ArtGallery.det (gridPt X Y ra) c w)+2/3*t*(σ*ArtGallery.det (gridPt X Y rb) c w) := by ring
  rw [this]
  rcases eq_or_lt_of_le l0 with e|e
  · rw [←e]; have : 0<2/3*t := by linarith
    nlinarith
  · nlinarith

theorem upper_test {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb cRn cBn : Index} {kR : Nat} {fR : Bool} {pR : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR true fR pR=true)
    (hcRn : (if fR then C.next kR else C.node kR)=cRn)
    (hyr : (gridPt X Y rb).2=(gridPt X Y ra).2)
    {Bx By tB tR : ℝ} (htB : 0≤tB ∧ tB≤3/2) (htR : 0≤tR ∧ tR≤3/2) {Bg : Point}
    (hR : receiver X Y ra rb tR∈(C.poly X Y).filled) (above : 1<Y.getD iy 0)
    (bLow : By<(gridPt X Y cBn).2) (rLow : (gridPt X Y ra).2<(gridPt X Y cRn).2)
    (axisB : (gridPt X Y cBn).2<Y.getD (iy+1) 0)
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      x<lineX (Bx+tB,By) (gridPt X Y cBn) y → ¬P.Sees Bg (x,y))
    (others : ∀ g∈Gs, g≠Bg → g≠receiver X Y ra rb tR → ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 →
      Y.getD iy 0<y → y<Y.getD (iy+1) 0 → lineX (receiver X Y ra rb tR) (gridPt X Y cRn) y<x →
      x<lineX (Bx+tB,By) (gridPt X Y cBn) y → ¬P.Sees g (x,y))
    (matched : ∀ t : ℝ, lineX (Bx+t,By) (gridPt X Y cBn) (Y.getD (iy+1) 0)=
      lineX (receiver X Y ra rb t) (gridPt X Y cRn) (Y.getD (iy+1) 0))
    (Ua0 : 0<ArtGallery.det (gridPt X Y ra) (gridPt X Y cRn) (gridPt X Y (xc,iy+1)))
    (Ua1 : 0<ArtGallery.det (gridPt X Y rb) (gridPt X Y cRn) (gridPt X Y (xc,iy+1)))
    (Ub0 : ArtGallery.det (gridPt X Y ra) (gridPt X Y cRn) (gridPt X Y (xc+1,iy+1))<0)
    (Ub1 : ArtGallery.det (gridPt X Y rb) (gridPt X Y cRn) (gridPt X Y (xc+1,iy+1))<0) : tR≤tB := by
  set a := Y.getD (iy+1) 0
  have rY (t : ℝ) : (receiver X Y ra rb t).2=(gridPt X Y ra).2 := rfl
  have rlow (t : ℝ) : (receiver X Y ra rb t).2<(gridPt X Y cRn).2 := by rw [rY]; exact rLow
  -- left corner: right of the receiver's ray
  have ha : X.getD xc 0<lineX (receiver X Y ra rb tR) (gridPt X Y cRn) a := by
    have d := det_along hyr htR (σ:=1) (c:=gridPt X Y cRn) (w:=gridPt X Y (xc,iy+1)) (by simpa using Ua0)
      (by simpa using Ua1)
    rw [one_mul] at d
    have e := det_lineX (rlow tR) (X.getD xc 0) a
    simp only [gridPt] at d e ⊢
    rw [e] at d
    have := rlow tR; simp only [gridPt] at this
    nlinarith
  have hb : lineX (Bx+tB,By) (gridPt X Y cBn) a<X.getD (xc+1) 0 := by
    rw [matched tB]
    have d := det_along hyr htB (σ:=-1) (c:=gridPt X Y cRn) (w:=gridPt X Y (xc+1,iy+1)) (by linarith)
      (by linarith)
    have e := det_lineX (rlow tB) (X.getD (xc+1) 0) a
    simp only [gridPt] at d e ⊢
    rw [e] at d
    have := rlow tB; simp only [gridPt] at this
    nlinarith
  have hcR : gridPt X Y (if fR then C.next kR else C.node kR)=gridPt X Y cRn := by rw [hcRn]
  unfold receiver at hR others ha matched
  exact upper_blocked G fill closed contact hW cover hxc hiy tile rcert hcR
    (by have := receiver_seg hyr htR; unfold receiver at this; exact this) hR above bLow rLow axisB blockB others
    (fun t => by rw [matched t]) ha hb


theorem upper_test_mid {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1)) (hW : 0≤W)
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb cRn cBn : Index} {kR : Nat} {fR : Bool} {pR : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR true fR pR=true)
    (hcRn : (if fR then C.next kR else C.node kR)=cRn)
    (hyr : (gridPt X Y rb).2=(gridPt X Y ra).2)
    {Bx By tB tR : ℝ} (htB : 0≤tB ∧ tB≤3/2) (htR : 0≤tR ∧ tR≤3/2) {Bg : Point}
    (hR : receiver X Y ra rb tR∈(C.poly X Y).filled) (above : 1<Y.getD iy 0)
    (bLow : By<(gridPt X Y cBn).2) (rLow : (gridPt X Y ra).2<(gridPt X Y cRn).2)
    (axisB : (gridPt X Y cBn).2<Y.getD (iy+1) 0)
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      x<lineX (Bx+tB,By) (gridPt X Y cBn) y → ¬P.Sees Bg (x,y))
    (others : ∀ g∈Gs, g≠Bg → g≠receiver X Y ra rb tR → ∀ t' : ℝ, tB<t' → t'<tR → ∀ y : ℝ,
      Y.getD iy 0<y → y<Y.getD (iy+1) 0 → X.getD xc 0<lineX (Bx+t',By) (gridPt X Y cBn) y →
      lineX (Bx+t',By) (gridPt X Y cBn) y<X.getD (xc+1) 0 → ¬P.Sees g (lineX (Bx+t',By) (gridPt X Y cBn) y,y))
    (matched : ∀ t : ℝ, lineX (Bx+t,By) (gridPt X Y cBn) (Y.getD (iy+1) 0)=
      lineX (receiver X Y ra rb t) (gridPt X Y cRn) (Y.getD (iy+1) 0))
    (Ua0 : 0<ArtGallery.det (gridPt X Y ra) (gridPt X Y cRn) (gridPt X Y (xc,iy+1)))
    (Ua1 : 0<ArtGallery.det (gridPt X Y rb) (gridPt X Y cRn) (gridPt X Y (xc,iy+1)))
    (Ub0 : ArtGallery.det (gridPt X Y ra) (gridPt X Y cRn) (gridPt X Y (xc+1,iy+1))<0)
    (Ub1 : ArtGallery.det (gridPt X Y rb) (gridPt X Y cRn) (gridPt X Y (xc+1,iy+1))<0) : tR≤tB := by
  set a := Y.getD (iy+1) 0
  have rY (t : ℝ) : (receiver X Y ra rb t).2=(gridPt X Y ra).2 := rfl
  have rlow (t : ℝ) : (receiver X Y ra rb t).2<(gridPt X Y cRn).2 := by rw [rY]; exact rLow
  -- left corner: right of the receiver's ray
  have ha : X.getD xc 0<lineX (receiver X Y ra rb tR) (gridPt X Y cRn) a := by
    have d := det_along hyr htR (σ:=1) (c:=gridPt X Y cRn) (w:=gridPt X Y (xc,iy+1)) (by simpa using Ua0)
      (by simpa using Ua1)
    rw [one_mul] at d
    have e := det_lineX (rlow tR) (X.getD xc 0) a
    simp only [gridPt] at d e ⊢
    rw [e] at d
    have := rlow tR; simp only [gridPt] at this
    nlinarith
  have hb : lineX (Bx+tB,By) (gridPt X Y cBn) a<X.getD (xc+1) 0 := by
    rw [matched tB]
    have d := det_along hyr htB (σ:=-1) (c:=gridPt X Y cRn) (w:=gridPt X Y (xc+1,iy+1)) (by linarith)
      (by linarith)
    have e := det_lineX (rlow tB) (X.getD (xc+1) 0) a
    simp only [gridPt] at d e ⊢
    rw [e] at d
    have := rlow tB; simp only [gridPt] at this
    nlinarith
  have hcR : gridPt X Y (if fR then C.next kR else C.node kR)=gridPt X Y cRn := by rw [hcRn]
  unfold receiver at hR others ha matched
  exact upper_blocked_mid G fill closed contact hW cover hxc hiy tile rcert hcR
    (by have := receiver_seg hyr htR; unfold receiver at this; exact this) hR above bLow rLow axisB blockB others
    (fun t => by rw [matched t]) ha hb

end ArtGallery.Orthogonal.BoundaryPoint.CopyUpper
end
