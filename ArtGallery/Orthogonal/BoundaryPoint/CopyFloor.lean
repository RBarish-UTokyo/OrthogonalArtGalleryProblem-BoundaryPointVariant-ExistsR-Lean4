module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyOutside

/-! # Sight lines through a door at height one

A point `g` outside a wing seeing a point `z` of the wing above the door line
sees it through a door point `(c,1)`. At the height of `g`, its abscissa is
determined by `c`: `g.1*(z.2-1)=c*(z.2-g.2)-(1-g.2)*z.1`. Comparing with a
reference point `B` whose line through `z` crosses the door at `c'`, the two
abscissae differ by `(c-c')*(z.2-g.2)/(z.2-1)`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyFloor
open Set RoomAttachment

/-- The door crossing of a sight line from outside into a wing. -/
theorem crossing {P W : Polygon} {d w : ℝ} (hw : 0≤w) (J : Joined P W (d,1) (d+w,1)) {g z : Point}
    (hg : g∈J.rest) (hz : z∈W.filled) (hz1 : 1<z.2) (hg1 : g.2<1) (sees : P.Sees g z) :
    ∃ c : ℝ, d≤c ∧ c≤d+w ∧ g.1*(z.2-1)=c*(z.2-g.2)-(1-g.2)*z.1 := by
  obtain ⟨p,hp,hpR,hpW⟩ := SingleWindow.segment_meets_window J.closed (Jordan.isClosed_filled W) hg hz
    (by rw [Set.union_comm,←J.fill]; exact sees)
  have hseam : p∈ArtGallery.segment (d,1) (d+w,1) := by rw [←J.contact]; exact ⟨hpW,hpR⟩
  obtain ⟨s,s0,s1,hs⟩ := hseam
  obtain ⟨t,t0,t1,rfl⟩ := hp
  simp only [Prod.mk.injEq] at hs
  obtain ⟨hx,hy⟩ := hs
  have e1 : g.1+t*(z.1-g.1)=d+s*w := by rw [hx]; ring
  refine ⟨g.1+t*(z.1-g.1),by rw [e1]; nlinarith,by rw [e1]; nlinarith,?_⟩
  have ht : t*(z.2-g.2)=1-g.2 := by linarith
  have e : (g.1+t*(z.1-g.1))*(z.2-g.2)-(1-g.2)*z.1=g.1*(z.2-g.2)+(z.1-g.1)*(t*(z.2-g.2))-(1-g.2)*z.1 := by ring
  rw [e,ht]; ring

/-- Two sight lines to `z` at the same height `y`, through door abscissae `c` and `c'`. -/
theorem compare {x x' y c c' : ℝ} {z : Point} (hz : 1<z.2)
    (h : x*(z.2-1)=c*(z.2-y)-(1-y)*z.1) (h' : x'*(z.2-1)=c'*(z.2-y)-(1-y)*z.1) :
    x-x'=(c-c')*(z.2-y)/(z.2-1) := by
  have hne : z.2-1≠0 := by linarith
  field_simp; linarith

/-- A guard on the floor `1-D` seeing a target on the line from the base position `B` through a
door point lies within `W*(h+D)/h` of `B`. -/
theorem floor_near {P Wg : Polygon} {d W : ℝ} (hW : 0≤W) (J : Joined P Wg (d,1) (d+W,1))
    {D b τ c h : ℝ} (hD : 0<D) (hh : 0<h) (hc0 : 0≤c) (hc1 : c≤W) {g : Point} (hg : g∈J.rest) (hgf : g.2=1-D)
    (hz : ((d+c+(c-(W+b*D+τ))*h/D,1+h):Point)∈Wg.filled)
    (sees : P.Sees g (d+c+(c-(W+b*D+τ))*h/D,1+h)) :
    |g.1-(d+W+b*D+τ)|≤W*(h+D)/h := by
  obtain ⟨cg,c0,c1,e⟩ := crossing hW J hg hz (by simp only; linarith) (by rw [hgf]; linarith) sees
  simp only [hgf] at e
  have e2 : (g.1-(d+W+b*D+τ))*h=(cg-d-c)*(h+D) := by
    have : g.1*h=cg*(h+D)-D*(d+c+(c-(W+b*D+τ))*h/D) := by
      have := e; ring_nf at this ⊢; linarith
    field_simp at this; nlinarith
  have hq : g.1-(d+W+b*D+τ)=(cg-d-c)*(h+D)/h := by field_simp; linarith
  rw [hq,abs_div,abs_mul,abs_of_pos hh,abs_of_pos (by linarith : 0<h+D)]
  apply div_le_div_of_nonneg_right _ hh.le
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A guard on the low roof `-6` seeing such a target stands near the door. -/
theorem roof_near {P Wg : Polygon} {d W : ℝ} (hW : 0≤W) (hW1 : W≤1) (J : Joined P Wg (d,1) (d+W,1))
    {D b τ c h : ℝ} (hD : 1≤D) (hh : 4/3≤h) (hc0 : 0≤c) (hc1 : c≤W) (hτ0 : 0≤τ) (hτ1 : τ≤3/2)
    (hb0 : 0≤b) (hb1 : b≤2) {g : Point} (hg : g∈J.rest) (hgf : g.2=-6)
    (hz : ((d+c+(c-(W+b*D+τ))*h/D,1+h):Point)∈Wg.filled)
    (sees : P.Sees g (d+c+(c-(W+b*D+τ))*h/D,1+h)) :
    d-6≤g.1 ∧ g.1≤d+40 := by
  obtain ⟨cg,c0,c1,e⟩ := crossing hW J hg hz (by simp only; linarith) (by rw [hgf]; norm_num) sees
  simp only [hgf] at e
  have hh0 : 0<h := by linarith
  have hD0 : 0<D := by linarith
  -- g.1 = cg + 7*(cg-d-c)/h + 7*(W+b*D+τ-c)/D
  have eq : g.1=cg+7*(cg-d-c)/h+7*(W+b*D+τ-c)/D := by
    field_simp; field_simp at e; nlinarith
  have a1 : -W≤cg-d-c ∧ cg-d-c≤W := ⟨by linarith,by linarith⟩
  have a2 : 7*(cg-d-c)/h≤6 := by
    rw [div_le_iff₀ hh0]; nlinarith
  have a3 : -6≤7*(cg-d-c)/h := by
    rw [le_div_iff₀ hh0]; nlinarith
  have a4 : 0≤7*(W+b*D+τ-c)/D := div_nonneg (by nlinarith) hD0.le
  have a5 : 7*(W+b*D+τ-c)/D≤32 := by
    rw [div_le_iff₀ hD0]; nlinarith
  constructor <;> linarith

/-- The point of a segment at a prescribed height between its ends. -/
theorem at_height {g z : Point} {y : ℝ} (lo : g.2≤y) (hi : y≤z.2) (lt : g.2<z.2) :
    ∃ p∈ArtGallery.segment g z, p.2=y ∧ p.1≤max g.1 z.1 := by
  set t := (y-g.2)/(z.2-g.2)
  have den : 0<z.2-g.2 := by linarith
  have t0 : 0≤t := div_nonneg (by linarith) den.le
  have t1 : t≤1 := (div_le_one den).mpr (by linarith)
  refine ⟨(g.1+t*(z.1-g.1),g.2+t*(z.2-g.2)),⟨t,t0,t1,rfl⟩,?_,?_⟩
  · simp only [t]; field_simp; ring
  · simp only
    rcases le_total g.1 z.1 with h|h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

end ArtGallery.Orthogonal.BoundaryPoint.CopyFloor
end
