module

public import ArtGallery.Orthogonal.BoundaryPoint.CoverAssume

/-! # Critical room cells under the satisfied relation

In the addition room the cell of the addition triangle is seen by three guards whose rays through
three floor corners are concurrent exactly when the relation holds (the slope balance), and in the
relay mouth the two rays through the mouth corners meet on the mouth top exactly when the copied
values agree. Here: the sign conditions of the assumed window ends of the chain certificates, as
lines through the guards, cover the cell. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCell
open ArtGallery SepCert CoverChain CoverAssume RoomGrid ArtGallery.Orthogonal.Hard

/-- The determinant against a corner above the guard as the offset from the guard's ray. -/
theorem det_corner (g z c : Point) (h : g.2<c.2) :
    det g z c = (c.2-g.2)*((z.1-c.1)-(c.1-g.1)/(c.2-g.2)*(z.2-c.2)) := by
  have hne : c.2-g.2≠0 := (sub_pos.mpr h).ne'
  unfold det; field_simp; ring

/-- Moving the corner along a vertical line changes the determinant by the horizontal offset. -/
theorem det_col (g z : Point) (a w v : ℝ) : det g z (a,w) = det g z (a,v)+(z.1-g.1)*(w-v) := by
  unfold det; ring

/-- Three rays through corners on a common floor line, with balanced corners and slopes (the
combined slope at most balanced), seen above the floor line. -/
theorem triangle_union {gx gr gz z : Point} {ax ar az fy : ℝ}
    (hx : gx.2<fy) (hr : gr.2<fy) (hz : gz.2<fy) (corner : 8*ax+ar=9*az)
    (slope : 8*((ax-gx.1)/(fy-gx.2))+(ar-gr.1)/(fy-gr.2)≤9*((az-gz.1)/(fy-gz.2))) (above : fy≤z.2) :
    0≤det gx z (ax,fy) ∨ 0≤det gr z (ar,fy) ∨ det gz z (az,fy)≤0 := by
  rw [det_corner gx z (ax,fy) hx,det_corner gr z (ar,fy) hr,det_corner gz z (az,fy) hz]
  dsimp only
  set kx := (ax-gx.1)/(fy-gx.2)
  set kr := (ar-gr.1)/(fy-gr.2)
  set kz := (az-gz.1)/(fy-gz.2)
  by_contra! bad
  obtain ⟨b1,b2,b3⟩ := bad
  have f1 : (z.1-ax)-kx*(z.2-fy)<0 := neg_of_mul_neg_right (by linarith) (sub_pos.mpr hx).le
  have f2 : (z.1-ar)-kr*(z.2-fy)<0 := neg_of_mul_neg_right (by linarith) (sub_pos.mpr hr).le
  have f3 : 0<(z.1-az)-kz*(z.2-fy) := pos_of_mul_pos_right b3 (sub_pos.mpr hz).le
  have key : 8*((z.1-ax)-kx*(z.2-fy))+((z.1-ar)-kr*(z.2-fy))-9*((z.1-az)-kz*(z.2-fy))=
      (9*kz-(8*kx+kr))*(z.2-fy) := by linear_combination (-1:ℝ)*corner
  have nn : 0≤(9*kz-(8*kx+kr))*(z.2-fy) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- Beyond the second corner of the first guard the second guard sees (a margin on the cell). -/
theorem beyond {gx gr z : Point} {az ar fy y0 : ℝ} (hx : gx.2<fy) (hr : gr.2<fy)
    (hy : y0≤z.2-fy) (order : (ar-gr.1)/(fy-gr.2)≤(az-gx.1)/(fy-gx.2))
    (margin : ar-az≤((az-gx.1)/(fy-gx.2)-(ar-gr.1)/(fy-gr.2))*y0)
    (h : 0<det gx z (az,fy)) : 0≤det gr z (ar,fy) := by
  rw [det_corner gx z (az,fy) hx] at h
  rw [det_corner gr z (ar,fy) hr]
  dsimp only at h ⊢
  set k2 := (az-gx.1)/(fy-gx.2)
  set kr := (ar-gr.1)/(fy-gr.2)
  have f2 : 0<(z.1-az)-k2*(z.2-fy) := pos_of_mul_pos_right h (sub_pos.mpr hx).le
  have m := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr order)
  apply mul_nonneg (sub_pos.mpr hr).le
  nlinarith only [f2,m,margin]

/-- Two rays through the bottom corners of a mouth meeting on the mouth top line. -/
theorem relay_union {gq gr z : Point} {aL aR h0 h1 : ℝ} (hq : gq.2<h0) (hr : gr.2<h0) (top : z.2≤h1)
    (meet : aL+(aL-gq.1)/(h0-gq.2)*(h1-h0)=aR+(aR-gr.1)/(h0-gr.2)*(h1-h0))
    (order : (aR-gr.1)/(h0-gr.2)≤(aL-gq.1)/(h0-gq.2)) :
    0≤det gq z (aL,h0) ∨ det gr z (aR,h0)≤0 := by
  rw [det_corner gq z (aL,h0) hq,det_corner gr z (aR,h0) hr]
  dsimp only
  set kq := (aL-gq.1)/(h0-gq.2)
  set kr := (aR-gr.1)/(h0-gr.2)
  by_contra! bad
  obtain ⟨b1,b2⟩ := bad
  have f1 : (z.1-aL)-kq*(z.2-h0)<0 := neg_of_mul_neg_right (by linarith) (sub_pos.mpr hq).le
  have f2 : 0<(z.1-aR)-kr*(z.2-h0) := pos_of_mul_pos_right b2 (sub_pos.mpr hr).le
  have m := mul_le_mul_of_nonneg_left (sub_nonneg.mpr top) (sub_nonneg.mpr order)
  nlinarith only [f1,f2,meet,m]

/-- The determinant as the vertical offset from the guard's ray (a non-vertical ray). -/
theorem det_ray (g z c : Point) (h : c.1≠g.1) :
    det g z c = (c.1-g.1)*((g.2+(c.2-g.2)*(z.1-g.1)/(c.1-g.1))-z.2) := by
  have hne : c.1-g.1≠0 := sub_ne_zero.mpr h
  unfold det; field_simp; ring

/-- Two rays ordered at an axis, the first at least as steep: left of the axis every point is above
the first or below the second. -/
theorem axis_union {g₁ c₁ g₂ c₂ z : Point} {X0 : ℝ} (hz : z.1≤X0)
    (order : g₁.2+(c₁.2-g₁.2)*(X0-g₁.1)/(c₁.1-g₁.1)≤g₂.2+(c₂.2-g₂.2)*(X0-g₂.1)/(c₂.1-g₂.1))
    (slope : (c₂.2-g₂.2)/(c₂.1-g₂.1)≤(c₁.2-g₁.2)/(c₁.1-g₁.1)) :
    g₁.2+(c₁.2-g₁.2)*(z.1-g₁.1)/(c₁.1-g₁.1)≤z.2 ∨ z.2≤g₂.2+(c₂.2-g₂.2)*(z.1-g₂.1)/(c₂.1-g₂.1) := by
  have e (g c : Point) (X : ℝ) : g.2+(c.2-g.2)*(X-g.1)/(c.1-g.1)=
      (g.2+(c.2-g.2)*(X0-g.1)/(c.1-g.1))-(c.2-g.2)/(c.1-g.1)*(X0-X) := by ring
  rw [e g₁ c₁,e g₂ c₂]
  rw [e g₁ c₁ X0,e g₂ c₂ X0] at order
  have m := mul_le_mul_of_nonneg_right slope (sub_nonneg.mpr hz)
  by_contra! bad
  linarith [bad.1,bad.2]

/-! ## Assumed ends reduced to a few primary corners

An assumed end `w` follows from a primary end `u` with the same sign when the two lie on a common
grid line and the change `det g z w - det g z u`, a product of two coordinate differences, has the
wanted sign for every guard point of the spot and every point of the cell (decided by indices). -/

def shiftOK (g₀ g₁ : Index) (x x' y y' : Nat) (u w : Index) (pos : Bool) : Bool :=
  let zR := decide (g₀.1≤x ∧ g₁.1≤x)
  let zL := decide (x'≤g₀.1 ∧ x'≤g₁.1)
  let zA := decide (g₀.2≤y ∧ g₁.2≤y)
  let zB := decide (y'≤g₀.2 ∧ y'≤g₁.2)
  let up := decide (u.2≤w.2)
  let dn := decide (w.2≤u.2)
  let rt := decide (u.1≤w.1)
  let lf := decide (w.1≤u.1)
  (w.1==u.1 && (if pos then (zR && up) || (zL && dn) else (zR && dn) || (zL && up))) ||
  (w.2==u.2 && (if pos then (zA && lf) || (zB && rt) else (zA && rt) || (zB && lf)))

def primOK (C : Chart) (prim : List (Index × Bool)) (g₀ g₁ : Index) (x x' y y' : Nat) (c : CertA) : Bool :=
  decide (g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x≤x' ∧ x'<C.nx ∧ y≤y' ∧ y'<C.ny) &&
  prim.all (fun p => decide (p.1.1<C.nx ∧ p.1.2<C.ny)) &&
  c.assumed.all fun e => decide (e.1.1<C.nx ∧ e.1.2<C.ny) &&
    (prim.contains e || prim.any fun p => p.2==e.2 && shiftOK g₀ g₁ x x' y y' p.1 e.1 e.2)

section
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

theorem shift_sound (G : Good C X Y s A) {g₀ g₁ u w : Index} {x x' y y' : Nat} {pos : Bool}
    (h : shiftOK g₀ g₁ x x' y y' u w pos=true)
    (rg : g₀.1<C.nx ∧ g₀.2<C.ny ∧ g₁.1<C.nx ∧ g₁.2<C.ny ∧ x≤x' ∧ x'<C.nx ∧ y≤y' ∧ y'<C.ny)
    (hu : u.1<C.nx ∧ u.2<C.ny) (hw : w.1<C.nx ∧ w.2<C.ny)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0))
    (H : Holds X Y g z (u,pos)) : Holds X Y g z (w,pos) := by
  obtain ⟨r0x,r0y,r1x,r1y,rx,rx',ry,ry'⟩ := rg
  have lx := G.lx; have ly := G.ly
  have lvx {i j : Nat} (hj : j<C.nx) (h : i≤j) := lev_le G.hx (by omega : j<X.length) h
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  have c1 (v : ℝ) := seg_coord hg Prod.fst (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  have c2 (v : ℝ) := seg_coord hg Prod.snd (fun t => by simp [Geometry.lerp]; ring) (v:=v)
  simp only [gridPt] at c1 c2
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have D : ArtGallery.det g z (gridPt X Y w)-ArtGallery.det g z (gridPt X Y u)=
      (z.1-g.1)*(Y.getD w.2 0-Y.getD u.2 0)-(X.getD w.1 0-X.getD u.1 0)*(z.2-g.2) := by
    simp only [ArtGallery.det,gridPt]; ring
  -- the four position facts and the four corner orders
  have zR (a : g₀.1≤x ∧ g₁.1≤x) : 0≤z.1-g.1 := by
    have := (c1 (X.getD x 0)).1 (lvx (by omega) a.1) (lvx (by omega) a.2); linarith
  have zL (a : x'≤g₀.1 ∧ x'≤g₁.1) : z.1-g.1≤0 := by
    have := (c1 (X.getD x' 0)).2.2.1 (lvx r0x a.1) (lvx r1x a.2); linarith
  have zA (a : g₀.2≤y ∧ g₁.2≤y) : 0≤z.2-g.2 := by
    have := (c2 (Y.getD y 0)).1 (lvy (by omega) a.1) (lvy (by omega) a.2); linarith
  have zB (a : y'≤g₀.2 ∧ y'≤g₁.2) : z.2-g.2≤0 := by
    have := (c2 (Y.getD y' 0)).2.2.1 (lvy r0y a.1) (lvy r1y a.2); linarith
  have up (a : u.2≤w.2) : 0≤Y.getD w.2 0-Y.getD u.2 0 := sub_nonneg.mpr (lvy hw.2 a)
  have dn (a : w.2≤u.2) : Y.getD w.2 0-Y.getD u.2 0≤0 := sub_nonpos.mpr (lvy hu.2 a)
  have rt (a : u.1≤w.1) : 0≤X.getD w.1 0-X.getD u.1 0 := sub_nonneg.mpr (lvx hw.1 a)
  have lf (a : w.1≤u.1) : X.getD w.1 0-X.getD u.1 0≤0 := sub_nonpos.mpr (lvx hu.1 a)
  unfold Holds at H ⊢
  dsimp only at H ⊢
  simp only [shiftOK,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨e,h⟩|⟨e,h⟩
  · have e' : X.getD w.1 0-X.getD u.1 0=0 := by rw [e,sub_self]
    rw [e',zero_mul,sub_zero] at D
    cases pos <;> simp only [ite_true,ite_false,Bool.false_eq_true,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq] at h H ⊢
    · rcases h with ⟨a,b⟩|⟨a,b⟩
      · nlinarith [mul_nonneg (zR a) (neg_nonneg.mpr (dn b))]
      · nlinarith [mul_nonneg (neg_nonneg.mpr (zL a)) (up b)]
    · rcases h with ⟨a,b⟩|⟨a,b⟩
      · nlinarith [mul_nonneg (zR a) (up b)]
      · nlinarith [mul_nonneg (neg_nonneg.mpr (zL a)) (neg_nonneg.mpr (dn b))]
  · have e' : Y.getD w.2 0-Y.getD u.2 0=0 := by rw [e,sub_self]
    rw [e',mul_zero,zero_sub] at D
    cases pos <;> simp only [ite_true,ite_false,Bool.false_eq_true,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq] at h H ⊢
    · rcases h with ⟨a,b⟩|⟨a,b⟩
      · nlinarith [mul_nonneg (rt b) (zA a)]
      · nlinarith [mul_nonneg (neg_nonneg.mpr (lf b)) (neg_nonneg.mpr (zB a))]
    · rcases h with ⟨a,b⟩|⟨a,b⟩
      · nlinarith [mul_nonneg (neg_nonneg.mpr (lf b)) (zA a)]
      · nlinarith [mul_nonneg (rt b) (neg_nonneg.mpr (zB a))]

/-- A certificate whose assumed ends follow from primary corners. -/
theorem prim_sound (G : Good C X Y s A) {prim : List (Index × Bool)} {g₀ g₁ : Index} {x x' y y' : Nat}
    {c : CertA} (hok : c.ok C g₀ g₁ x x' y y'=true) (hp : primOK C prim g₀ g₁ x x' y y' c=true)
    {g z : Point} (hg : g∈ArtGallery.segment (gridPt X Y g₀) (gridPt X Y g₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0))
    (hH : ∀ e∈prim, Holds X Y g z e) : (C.poly X Y).Sees g z := by
  simp only [primOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hp
  obtain ⟨⟨rg,hpr⟩,ha⟩ := hp
  refine CertA.sound G hok hg hz fun e he => ?_
  obtain ⟨he1,hor⟩ := ha e he
  simp only [Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true,Bool.and_eq_true,beq_iff_eq] at hor
  rcases hor with m|⟨p,hp,e2,hs⟩
  · exact hH e m
  · have H := hH p hp
    obtain ⟨w,pos⟩ := e
    obtain ⟨u,pos'⟩ := p
    dsimp only at e2 hs he1
    subst e2
    exact shift_sound G hs rg (hpr _ hp) he1 hg hz H

end

end ArtGallery.Orthogonal.BoundaryPoint.RoomCell
end
