module

public import ArtGallery.Orthogonal.BoundaryPoint.BaseSight
public import ArtGallery.Orthogonal.BoundaryPoint.CopyChannel

/-! # Matched copy rays cover the copy cells

With equal values, the base ray through the door corner `(W,1)` and the receiver ray through
the window corner `(cx,1)` cross the nook axis `y = 1+H` at the same point (the incidence
`W - bH = cx - rH`). Above the axis the base sees every point left of its ray and the receiver
every point right of its own, and the receiver ray is the flatter one (`b ≤ r`): together they
see everything. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyCover
open Set

/-- The base determinant against the door corner, in slope form. -/
theorem det_base (W b D t : ℝ) (hD : D≠0) (z : Point) :
    ArtGallery.det (W+b*D+t,1-D) z (W,1)=D*(z.1-W+(b+t/D)*(z.2-1)) := by
  simp only [ArtGallery.det]; field_simp; ring

/-- The receiver determinant against the window corner, in slope form. -/
theorem det_receiver (cx d r D t : ℝ) (z : Point) :
    ArtGallery.det (cx+d*(r+t/D),1-d) z (cx,1)=d*(z.1-cx+(r+t/D)*(z.2-1)) := by
  simp only [ArtGallery.det]; ring

/-- Above the nook axis, a point is left of the base ray or right of the receiver ray. -/
theorem nook_union {W b D cx d r H t : ℝ} (hD : 0<D) (hd : 0<d) (hbr : b≤r)
    (incidence : W-b*H=cx-r*H) {z : Point} (above : 1+H≤z.2) :
    ArtGallery.det (W+b*D+t,1-D) z (W,1)≤0 ∨ 0≤ArtGallery.det (cx+d*(r+t/D),1-d) z (cx,1) := by
  rw [det_base W b D t hD.ne' z,det_receiver cx d r D t z]
  by_cases h : z.1-W+(b+t/D)*(z.2-1)≤0
  · exact Or.inl (mul_nonpos_of_nonneg_of_nonpos hD.le h)
  · right
    push Not at h
    apply mul_nonneg hd.le
    have : (r-b)*(z.2-1-H)≥0 := mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- Moving the third point of a determinant. -/
theorem det_shift (g z w w' : Point) :
    ArtGallery.det g z w'=ArtGallery.det g z w+(z.1-g.1)*(w'.2-w.2)-(w'.1-w.1)*(z.2-g.2) := by
  simp only [ArtGallery.det]; ring

/-- A receiver sightline into a nook cell passes below a node `w` above the window line and left
of the window corner, when the explicit bound (the axis crossing `p` of the receiver ray is at
least `pmin`, the cell is `[·,x1]×[1+H,y1]`) is negative. -/
theorem receiver_below {cx d ρ ρmax H pmin x1 y1 RxMin : ℝ} {w z : Point} (hd : 0<d)
    (hρ : 0≤ρ) (hρm : ρ≤ρmax) (hp : pmin≤cx-ρ*H) (hz1 : z.1≤x1) (hz2 : z.2≤y1) (hza : 1+H≤z.2)
    (hRx : RxMin≤cx+d*ρ) (hwy : 1≤w.2) (hwx : w.1≤cx)
    (bound : d*((x1-pmin)+ρmax*(y1-1-H))+(x1-RxMin)*(w.2-1)+(cx-w.1)*(y1-(1-d))<0) :
    ArtGallery.det (cx+d*ρ,1-d) z w<0 := by
  have hr : ArtGallery.det (cx+d*ρ,1-d) z (cx,1)=d*(z.1-cx+ρ*(z.2-1)) := by
    simp only [ArtGallery.det]; ring
  rw [det_shift (cx+d*ρ,1-d) z (cx,1) w,hr]
  have e1 : d*(z.1-cx+ρ*(z.2-1))≤d*((x1-pmin)+ρmax*(y1-1-H)) := by
    apply mul_le_mul_of_nonneg_left _ hd.le
    have a : ρ*(z.2-1-H)≤ρmax*(y1-1-H) :=
      mul_le_mul hρm (by linarith) (by linarith) (by linarith)
    nlinarith
  have e2 : (z.1-(cx+d*ρ))*(w.2-1)≤(x1-RxMin)*(w.2-1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have e3 : (w.1-cx)*(z.2-(1-d))≥(w.1-cx)*(y1-(1-d)) := by
    have : 0≤cx-w.1 := by linarith
    nlinarith
  simp only at e2 e3 ⊢
  nlinarith


/-- A base sightline into a nook cell passes right of the left door corner `(0,c)`, `c ≥ 1`, when
the axis crossing `p = W-(b+t/D)H` of the base ray through `(W,1)` is at most `pmax` and the
explicit bound holds. -/
theorem base_right_of {W b D t H pmax x0 y0 c K : ℝ} {z : Point} (hD : 0<D) (hH : 0<H)
    (hp : W-(b+t/D)*H≤pmax) (hWp : pmax≤W) (hz1 : x0≤z.1) (hz2 : y0≤z.2) (hyc : c≤y0) (hc : 1≤c) (hW : 0≤W)
    (hK : H*(W-x0)*(c-1)≤K) (bound : 0≤H*x0+(W-pmax)*(y0-c)-K/D) :
    0≤ArtGallery.det (W+b*D+t,1-D) z (0,c) := by
  have e : ArtGallery.det (W+b*D+t,1-D) z (0,c)=
      D*(z.1+(b+t/D)*(z.2-c))+t*(c-1)+(z.1-W-t)*(c-1)+W*(z.2-1) := by
    simp only [ArtGallery.det]; field_simp; ring
  rw [e]
  have hb : (b+t/D)*H≥W-pmax := by linarith
  have m1 : (b+t/D)*(z.2-c)≥(W-pmax)*(z.2-c)/H := by
    rw [ge_iff_le,div_le_iff₀ hH]; nlinarith
  have m2 : (W-pmax)*(z.2-c)≥(W-pmax)*(y0-c) := by nlinarith
  have m3 : z.1+(b+t/D)*(z.2-c)≥(H*x0+(W-pmax)*(y0-c))/H := by
    rw [ge_iff_le,div_le_iff₀ hH]
    have := (div_le_iff₀ hH).mp (show (W-pmax)*(z.2-c)/H≤(b+t/D)*(z.2-c) from m1)
    nlinarith
  have m4 : D*((H*x0+(W-pmax)*(y0-c))/H)≥K/H := by
    rw [ge_iff_le,div_le_iff₀ hH]
    have h1 : K/D≤H*x0+(W-pmax)*(y0-c) := by linarith
    rw [div_le_iff₀ hD] at h1
    field_simp; nlinarith
  have m5 : K/H≥(W-x0)*(c-1) := by rw [ge_iff_le,le_div_iff₀ hH]; nlinarith
  have m6 : (z.1-W-t)*(c-1)+t*(c-1)=(z.1-W)*(c-1) := by ring
  have m7 : (z.1-W)*(c-1)≥(x0-W)*(c-1) := by nlinarith
  have m8 : W*(z.2-1)≥0 := mul_nonneg hW (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left m3 hD.le]


/-- Below the chamber axis, with matched rays and the base ray steeper than the receiver ray, a
point is right of the base ray through `cB` or left of the receiver ray through `cR`. -/
theorem chamber_union {B R cB cR z : Point} {Ya : ℝ} (hB : B.2<cB.2) (hR : R.2<cR.2)
    (matched : CopyChannel.lineX B cB Ya=CopyChannel.lineX R cR Ya)
    (slope : (cR.1-R.1)*(cB.2-B.2)≤(cB.1-B.1)*(cR.2-R.2)) (hz : z.2≤Ya) :
    0≤ArtGallery.det B z cB ∨ ArtGallery.det R z cR≤0 := by
  have eB : ArtGallery.det B z cB=(cB.2-B.2)*(z.1-CopyChannel.lineX B cB z.2) := by
    have := CopyChannel.det_lineX hB z.1 z.2
    simp only [ArtGallery.det] at this ⊢; linarith
  have eR : ArtGallery.det R z cR=(cR.2-R.2)*(z.1-CopyChannel.lineX R cR z.2) := by
    have := CopyChannel.det_lineX hR z.1 z.2
    simp only [ArtGallery.det] at this ⊢; linarith
  have lB (y : ℝ) : CopyChannel.lineX B cB y=CopyChannel.lineX B cB Ya+(cB.1-B.1)/(cB.2-B.2)*(y-Ya) := by
    simp only [CopyChannel.lineX]; field_simp; ring
  have lR (y : ℝ) : CopyChannel.lineX R cR y=CopyChannel.lineX R cR Ya+(cR.1-R.1)/(cR.2-R.2)*(y-Ya) := by
    simp only [CopyChannel.lineX]; field_simp; ring
  have sl : (cR.1-R.1)/(cR.2-R.2)≤(cB.1-B.1)/(cB.2-B.2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  have order : CopyChannel.lineX B cB z.2≤CopyChannel.lineX R cR z.2 := by
    rw [lB,lR,matched]; nlinarith
  rw [eB,eR]
  by_cases h : CopyChannel.lineX B cB z.2≤z.1
  · exact Or.inl (mul_nonneg (by linarith) (by linarith))
  · right; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- A receiver sightline into a cell above the nook axis passes right of the window corner when the
explicit bound holds (the axis crossing `p` of the receiver ray is at most `pmax`). -/
theorem receiver_right {cx d r ρ H pmax x0 y0 : ℝ} {z : Point} (hd : 0<d) (hρ : r≤ρ) (hp : cx-ρ*H≤pmax)
    (hz1 : x0≤z.1) (hz2 : y0≤z.2) (hy0 : 1+H≤y0) (hr : 0≤r)
    (bound : 0<d*(x0-pmax)+d*r*(y0-1-H)) :
    0≤ArtGallery.det (cx+d*ρ,1-d) z (cx,1) := by
  have e : ArtGallery.det (cx+d*ρ,1-d) z (cx,1)=d*(z.1-cx+ρ*(z.2-1)) := by simp only [ArtGallery.det]; ring
  rw [e]; apply mul_nonneg hd.le
  have a : ρ*(z.2-1-H)≥r*(y0-1-H) := mul_le_mul hρ (by linarith) (by linarith) (by linarith)
  have b' : d*(x0-pmax)+d*r*(y0-1-H)≤d*((z.1-(cx-ρ*H))+ρ*(z.2-1-H)) := by nlinarith
  nlinarith

/-- A base sightline into a cell above the nook axis crosses the door line left of the right door
corner when the explicit bound holds (the axis crossing `p` of the base ray through `(W,1)` is at
least `pmin`). -/
theorem base_left_of {W b D t H pmin x1 y1 : ℝ} {z : Point} (hD : 0<D) (hH : 0<H) (hbt : 0≤b+t/D)
    (hp : pmin≤W-(b+t/D)*H) (hz1 : z.1≤x1) (hz2 : z.2≤y1) (hza : 1+H≤z.2)
    (bound : 0<H*(pmin-x1)-(W-pmin)*(y1-1-H)) :
    ArtGallery.det (W+b*D+t,1-D) z (W,1)≤0 := by
  rw [det_base W b D t hD.ne' z]
  apply mul_nonpos_of_nonneg_of_nonpos hD.le
  have hb : (b+t/D)*H≤W-pmin := by linarith
  have m : (b+t/D)*(z.2-1-H)*H≤(W-pmin)*(y1-1-H) := by
    have a : (b+t/D)*(z.2-1-H)≤(b+t/D)*(y1-1-H) := mul_le_mul_of_nonneg_left (by linarith) hbt
    have c : (b+t/D)*H*(y1-1-H)≤(W-pmin)*(y1-1-H) := mul_le_mul_of_nonneg_right hb (by linarith)
    nlinarith
  have : (z.1-W+(b+t/D)*(z.2-1))*H≤0 := by nlinarith
  by_contra hc; push Not at hc; nlinarith

/-- A shift along a grid column from a node with an established sign: `det(g,z,w) =
det(g,z,u) + (z.1-g.1)(w.2-u.2)` when `w.1 = u.1`. -/
theorem det_col (g z u : Point) (w2 : ℝ) :
    ArtGallery.det g z (u.1,w2)=ArtGallery.det g z u+(z.1-g.1)*(w2-u.2) := by
  simp only [ArtGallery.det]; ring

/-- A shift along a grid row: `det(g,z,w) = det(g,z,u) - (w.1-u.1)(z.2-g.2)` when `w.2 = u.2`. -/
theorem det_row (g z u : Point) (w1 : ℝ) :
    ArtGallery.det g z (w1,u.2)=ArtGallery.det g z u-(w1-u.1)*(z.2-g.2) := by
  simp only [ArtGallery.det]; ring

end ArtGallery.Orthogonal.BoundaryPoint.CopyCover
end
