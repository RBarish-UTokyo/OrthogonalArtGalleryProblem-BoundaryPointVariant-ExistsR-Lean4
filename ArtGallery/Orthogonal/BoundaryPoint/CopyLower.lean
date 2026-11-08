module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyChannel

/-! # The nook test in chart terms

The receiver spot is the floor segment from node `ra` to node `rb`, the window
corner is the node `win` at `(301/2,1)`, and the target cell lies above the nook
axis `y=Y[iy]`. Two determinant signs at the cell's lower corners give the range
conditions of `CopyChannel.lower_blocked`: the left corner lies left of the
window ray of the far spot end, the right corner right of the window ray of the
near spot end. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyLower
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CellCert CopyChannel ArtGallery.Orthogonal.Hard

/-- The nook gap with other guards excluded only from the bottom strip (height `1/256`) of the target cell. -/
theorem lower_blockedL {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
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
      1+H<y → y<1+H+(Y.getD (iy+1) 0-Y.getD iy 0)/256 → W-(b+tB/D)*(y-1)<x → x<cx-(r+tR/D)*(y-1) → ¬P.Sees g (x,y))
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
    (a:=1+H) (ε:=(Y.getD (iy+1) 0-Y.getD iy 0)/256) (xa:=X.getD xc 0) (xb:=X.getD (xc+1) 0)
    (αp:=W-(b+tB/D)*H) (βp:=-(b+tB/D)) (αq:=cx-(r+tR/D)*H) (βq:=-(r+tR/D)) true (by linarith)
    (fun x y h0 h1 hy => by
      simp only [ite_true] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 (by linarith [hy.2])
      exact sub (tile_filled G tile (z:=(x,y)) ax ay))
    (fun x y h0 h1 hy right => by
      simp only [ite_true] at hy
      apply blockB x y h0 h1 hy.1 (by linarith)
      have : W-(b+tB/D)*(y-1)=W-(b+tB/D)*H+-(b+tB/D)*(y-(1+H)) := by ring
      rw [this]; exact right)
    (fun x y h0 h1 hy left => by
      simp only [ite_true] at hy
      obtain ⟨ax,ay⟩ := atoms x y h0 h1 hy.1 (by linarith [hy.2])
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


/-- The receiver guard at parameter `t` on the spot `[ra,rb]`. -/
noncomputable def receiver (X Y : List ℝ) (ra rb : Index) (t : ℝ) : Point :=
  ((gridPt X Y ra).1+2/3*((gridPt X Y rb).1-(gridPt X Y ra).1)*t,(gridPt X Y ra).2)

theorem lineX_floor {cx d q : ℝ} (hd : d≠0) (y : ℝ) : lineX (cx+d*q,1-d) (cx,1) y=cx-q*(y-1) := by
  unfold lineX; simp only
  rw [show (1:ℝ)-(1-d)=d by ring]; field_simp; ring

theorem lower_test {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ} (G : Good C X Y s A)
    {P : Polygon} {rest : Set Point} {W : ℝ} (fill : P.filled=(C.poly X Y).filled∪rest) (closed : IsClosed rest)
    (contact : (C.poly X Y).filled∩rest=ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1))
    {Gs : Finset Point} (cover : ∀ z∈P.filled, ∃ g∈Gs, P.Sees g z)
    {xc iy : Nat} (hxc : xc+1<X.length) (hiy : iy+1<Y.length)
    (tile : inTile C.tiles (2*xc+2,2*iy+2)=true)
    {ra rb win : Index} {kR : Nat} {first : Bool} {pairs : List (Sign × Sign)}
    (rcert : crossOne C ra rb (2*xc+2,2*iy+2) kR false first pairs=true)
    (hu : (if first then C.next kR else C.node kR)=win)
    (hwin : gridPt X Y win=((301/2:ℝ),(1:ℝ)))
    (hyr : (gridPt X Y rb).2=(gridPt X Y ra).2) (rlow : (gridPt X Y ra).2<1)
    (hy0 : 1<Y.getD iy 0)
    {b D : ℝ} (hD : 0<D)
    (hrb : (gridPt X Y rb).1=(gridPt X Y ra).1+3/2*(1-(gridPt X Y ra).2)/D)
    (deep : Y.getD (iy+1) 0-1<D)
    (L1 : 0<ArtGallery.det (gridPt X Y rb) (gridPt X Y win) (gridPt X Y (xc,iy)))
    (L2 : ArtGallery.det (gridPt X Y ra) (gridPt X Y win) (gridPt X Y (xc+1,iy))<0)
    (incidence : W-b*(Y.getD iy 0-1)=301/2-((gridPt X Y ra).1-301/2)/(1-(gridPt X Y ra).2)*(Y.getD iy 0-1))
    {tB tR : ℝ} (htB : 0≤tB ∧ tB≤3/2) (htR : 0≤tR ∧ tR≤3/2)
    {Bg : Point}
    (blockB : ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 → Y.getD iy 0<y → y<Y.getD (iy+1) 0 →
      W-(b+tB/D)*(y-1)<x → ¬P.Sees Bg (x,y))
    (hR : receiver X Y ra rb tR∈(C.poly X Y).filled)
    (others : ∀ g∈Gs, g≠Bg → g≠receiver X Y ra rb tR → ∀ x y : ℝ, X.getD xc 0<x → x<X.getD (xc+1) 0 →
      Y.getD iy 0<y → y<Y.getD iy 0+(Y.getD (iy+1) 0-Y.getD iy 0)/256 → W-(b+tB/D)*(y-1)<x →
      x<lineX (receiver X Y ra rb tR) (gridPt X Y win) y → ¬P.Sees g (x,y)) : tB≤tR := by
  set cx : ℝ := 301/2
  set d : ℝ := 1-(gridPt X Y ra).2 with hd_def
  set r : ℝ := ((gridPt X Y ra).1-cx)/d with hr_def
  set H : ℝ := Y.getD iy 0-1 with hH_def
  have hd : 0<d := by simp only [d]; linarith
  have hH : 0<H := by simp only [H]; linarith
  have hd0 : d≠0 := hd.ne'
  have hD0 : D≠0 := hD.ne'
  have hra : gridPt X Y ra=(cx+d*r,1-d) := by
    ext
    · simp only [r]; field_simp; ring
    · simp only [d]; ring
  have hrb' : gridPt X Y rb=(cx+d*(r+3/(2*D)),1-d) := by
    ext
    · simp only [r]; rw [hrb]; field_simp; ring
    · simp only [d]; rw [hyr]; ring
  have hrec : receiver X Y ra rb tR=(cx+d*(r+tR/D),1-d) := by
    unfold receiver; rw [hra,hrb']; ext <;> simp only <;> field_simp <;> ring
  rw [hrec] at hR others
  have hu' : gridPt X Y (if first then C.next kR else C.node kR)=(cx,1) := by rw [hu,hwin]
  -- the window rays of the spot ends at the axis
  have wy : (gridPt X Y win).2=1 := by rw [hwin]
  have a1 := det_lineX (p:=gridPt X Y rb) (c:=gridPt X Y win) (by rw [wy,hrb']; simp only; linarith)
    (X.getD xc 0) (Y.getD iy 0)
  have a2 := det_lineX (p:=gridPt X Y ra) (c:=gridPt X Y win) (by rw [wy,hra]; simp only; linarith)
    (X.getD (xc+1) 0) (Y.getD iy 0)
  simp only [gridPt] at L1 L2 a1 a2
  rw [a1] at L1; rw [a2] at L2
  have e1 : lineX (gridPt X Y rb) (gridPt X Y win) (Y.getD iy 0)=cx-(r+3/(2*D))*H := by
    rw [hrb',hwin,lineX_floor hd0]
  have e2 : lineX (gridPt X Y ra) (gridPt X Y win) (Y.getD iy 0)=cx-r*H := by
    rw [hra,hwin,lineX_floor hd0]
  simp only [gridPt] at e1 e2
  have pos1 : 0<(gridPt X Y win).2-(gridPt X Y rb).2 := by rw [wy,hrb']; simp only; linarith
  have pos2 : 0<(gridPt X Y win).2-(gridPt X Y ra).2 := by rw [wy,hra]; simp only; linarith
  simp only [gridPt] at pos1 pos2
  have ha0 : X.getD xc 0<cx-(r+3/(2*D))*H := by
    rw [←e1]; nlinarith
  have hb0 : cx-r*H<X.getD (xc+1) 0 := by
    rw [←e2]; nlinarith
  have inc : W-b*H=cx-r*H := incidence
  apply lower_blockedL G fill closed contact cover hxc hiy tile rcert hu' hra hrb' hD hH hd (by simp only [H]; ring) htR hR
    (fun x y h0 h1 y0 y1 right => blockB x y h0 h1 (by simp only [H] at y0; linarith) y1 right)
    (fun g hg e1 e2 x y h0 h1 y0 y1 lo hi => others g hg e1 e2 x y h0 h1 (by simp only [H] at y0; linarith) (by simp only [H] at y1; linarith) lo
      (by rw [hwin,show (d*(r+tR/D)) = d*(r+tR/D) from rfl,lineX_floor hd0]; exact hi))
    inc
  · -- X[xc] < W-(b+tB/D)H
    have : (b+tB/D)*H≤(b+3/(2*D))*H := by
      apply mul_le_mul_of_nonneg_right _ hH.le
      have : tB/D≤3/(2*D) := by rw [div_le_div_iff₀ hD (by positivity)]; nlinarith
      linarith
    have : W-(b+tB/D)*H=cx-(r+tB/D)*H := by linear_combination inc
    have : (r+tB/D)*H≤(r+3/(2*D))*H := by
      apply mul_le_mul_of_nonneg_right _ hH.le
      have : tB/D≤3/(2*D) := by rw [div_le_div_iff₀ hD (by positivity)]; nlinarith
      linarith
    linarith
  · have : 0≤tR/D*H := mul_nonneg (div_nonneg htR.1 hD.le) hH.le
    have e : cx-(r+tR/D)*H=cx-r*H-tR/D*H := by ring
    rw [e]; exact lt_of_le_of_lt (sub_le_self _ this) hb0

end ArtGallery.Orthogonal.BoundaryPoint.CopyLower
end
