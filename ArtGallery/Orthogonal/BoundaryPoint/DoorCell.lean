module

public import ArtGallery.Orthogonal.BoundaryPoint.NookCell

/-! # The door cells

A cell `[0,W]×[Y y, Y y']` of the door passage is seen by the base guard where its sightline
crosses the door, and otherwise (a point within `(b + t/D)(y - 1)` of the right wall) by a fixed
upper guard `g` of the wing whose chain certificate assumes one window end `w`; that end holds on
the strip `[W - (bhi+1)(Y y' - 1), W] × [Y y, Y y']` by its four corners. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.DoorCell
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CoverChain CoverAssume BaseSight CopyCover QuadCheck
open NookCell ArtGallery.Orthogonal.Hard

/-- `σ det(g, p, w)` at the corner `p = (px, Y k)` of the strip, as a quadratic expression. -/
def cornerQuad (g w : Index) (px : Lin) (k : Nat) (σ : Bool) : Quad :=
  let sg : ℚ := if σ then 1 else -1
  [(ldiff px (lx g.1),(ldiff (ly w.2) (ly g.2)).map fun t => {t with c := sg*t.c}),
   (lneg (ldiff (lx w.1) (lx g.1)),(ldiff (ly k) (ly g.2)).map fun t => {t with c := sg*t.c})]

/-- The left side of the strip: `W - (bhi+1)(Y y' - 1)`. -/
def stripX (N : Nook) (y' : Nat) (bhi : ℚ) : Lin :=
  lx N.dr.1++((ldiff (ly y') (ly N.win.2)).map fun t => {t with c := -(bhi+1)*t.c})

def doorOK (C : Chart) (N : Nook) (g w : Index) (σ : Bool) (y y' : Nat) (cB cG : CertA) (bhi : ℚ)
    (k1 k2 k3 k4 : Nat) : Bool :=
  cB.ok C N.dl N.dr N.dl.1 N.dr.1 y y' && cB.assumed.isEmpty &&
  cG.ok C g g N.dl.1 N.dr.1 y y' && cG.assumed.all (· == (w,σ)) &&
  (cornerQuad g w (stripX N y' bhi) y σ).ok C k1 && (cornerQuad g w (stripX N y' bhi) y' σ).ok C k2 &&
  (cornerQuad g w (lx N.dr.1) y σ).ok C k3 && (cornerQuad g w (lx N.dr.1) y' σ).ok C k4 &&
  decide (N.dl.2=N.win.2 ∧ N.dr.2=N.win.2 ∧ N.win.2≤y ∧ y<y' ∧ y'<C.ny ∧ N.dr.1<C.nx ∧ N.dl.1<N.dr.1 ∧
    g.1<C.nx ∧ g.2<C.ny ∧ w.1<C.nx ∧ w.2<C.ny)

section
variable {X Y : List ℝ} {s : ℝ}

theorem lin_map_scale (l : Lin) (c : ℚ) :
    Lin.real X Y s (l.map fun t => {t with c := c*t.c})=(c:ℝ)*Lin.real X Y s l := by
  induction l with
  | nil => simp [Lin.real]
  | cons t l ih =>
    simp only [Lin.real,List.map_cons,List.sum_cons] at ih ⊢; rw [ih]; push_cast; ring

theorem cornerQuad_real (g w : Index) (px : Lin) (k : Nat) (σ : Bool) :
    (cornerQuad g w px k σ).real X Y s=(if σ then 1 else -1)*ArtGallery.det (gridPt X Y g)
      (Lin.real X Y s px,Y.getD k 0) (gridPt X Y w) := by
  simp only [cornerQuad,Quad.real,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ldiff_real,lx_real,
    ly_real,lneg_real,lin_map_scale]
  cases σ <;> simp [ArtGallery.det,gridPt] <;> ring

theorem stripX_real (N : Nook) (y' : Nat) (bhi : ℚ) :
    Lin.real X Y s (stripX N y' bhi)=X.getD N.dr.1 0-((bhi:ℝ)+1)*(Y.getD y' 0-Y.getD N.win.2 0) := by
  simp only [stripX,Lin.real,List.map_append,List.sum_append]
  have := lin_map_scale (X:=X) (Y:=Y) (s:=s) (ldiff (ly y') (ly N.win.2)) (-(bhi+1))
  simp only [Lin.real] at this; rw [this]
  have e1 := lx_real (X:=X) (Y:=Y) (s:=s) N.dr.1; simp only [Lin.real] at e1; rw [e1]
  have e2 := ldiff_real (X:=X) (Y:=Y) (s:=s) (ly y') (ly N.win.2); simp only [Lin.real] at e2; rw [e2]
  have e3 := ly_real (X:=X) (Y:=Y) (s:=s) y'; have e4 := ly_real (X:=X) (Y:=Y) (s:=s) N.win.2
  simp only [Lin.real] at e3 e4; rw [e3,e4]; push_cast; ring

end


section Door
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

set_option maxHeartbeats 4000000 in
/-- A door cell is seen by the base guard or by the fixed upper guard. -/
theorem door (G : Good C X Y s A) (one : A 0=1) {P : Polygon} (sub : (C.poly X Y).filled⊆P.filled)
    {N : Nook} {g w : Index} {σ : Bool} {y y' : Nat} {cB cG : CertA} {bhi : ℚ} {k1 k2 k3 k4 : Nat}
    (ok : doorOK C N g w σ y y' cB cG bhi k1 k2 k3 k4=true)
    {W b D t : ℝ} (hD : 3/2≤D) (hW : X.getD N.dr.1 0=W) (hdl0 : X.getD N.dl.1 0=0) (hwy : Y.getD N.win.2 0=1)
    (hb0 : 0≤b) (hbhi : b≤bhi) (ht : 0≤t ∧ t≤3/2)
    (hdoor : ∀ d∈ArtGallery.segment ((0:ℝ),(1:ℝ)) (W,1), P.Sees (W+b*D+t,1-D) d)
    {z : Point} (hz : z∈Rect (X.getD N.dl.1 0) (X.getD N.dr.1 0) (Y.getD y 0) (Y.getD y' 0)) :
    P.Sees (W+b*D+t,1-D) z ∨ P.Sees (gridPt X Y g) z := by
  simp only [doorOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨okB,eB⟩,okG⟩,aG⟩,q1⟩,q2⟩,q3⟩,q4⟩,ix⟩ := ok
  obtain ⟨dlw,drw,winy,yy',y'n,drn,dldr,g1n,g2n,w1n,w2n⟩ := ix
  have lx := G.lx; have ly := G.ly
  have lvy {i j : Nat} (hj : j<C.ny) (h : i≤j) := lev_le G.hy (by omega : j<Y.length) h
  have hD0 : 0<D := by linarith
  obtain ⟨z0,z1,z2,z3⟩ := hz
  rw [hdl0] at z0; rw [hW] at z1
  have hy1 : 1≤Y.getD y 0 := by have := lvy (by omega : y<C.ny) winy; rw [hwy] at this; exact this
  have hy'1 : 1≤Y.getD y' 0 := by have := lvy y'n (by omega : N.win.2≤y'); rw [hwy] at this; exact this
  by_cases h : ArtGallery.det (W+b*D+t,1-D) z (W,1)≤0
  · left
    have hdl : gridPt X Y N.dl=((0:ℝ),(1:ℝ)) := by simp only [gridPt]; rw [hdl0,dlw,hwy]
    have hdr : gridPt X Y N.dr=(W,1) := by simp only [gridPt]; rw [hW,drw,hwy]
    have hBy : (W+b*D+t,1-D).2<1 := by simp; linarith
    have cross0 : 0≤ArtGallery.det (W+b*D+t,1-D) z ((0:ℝ),(1:ℝ)) := by
      have e : ArtGallery.det (W+b*D+t,1-D) z ((0:ℝ),(1:ℝ))=z.1*D+(W+b*D+t)*(z.2-1) := by
        simp only [ArtGallery.det]; ring
      rw [e]
      have hW0 : 0≤W := by linarith
      nlinarith [mul_nonneg z0 hD0.le, mul_nonneg (by nlinarith [mul_nonneg hb0 hD0.le] : 0≤W+b*D+t) (by linarith : 0≤z.2-1)]
    refine base_sees G sub hdl hdr hBy hdoor okB ⟨by rw [hdl0]; exact z0,by rw [hW]; exact z1,z2,z3⟩
      (by linarith) cross0 h ?_
    intro e he; rw [List.isEmpty_iff.mp eB] at he; simp at he
  · right
    push Not at h
    rw [det_base W b D t hD0.ne' z] at h
    have hpos : 0<z.1-W+(b+t/D)*(z.2-1) := by
      by_contra hc; push Not at hc; nlinarith [mul_nonpos_of_nonneg_of_nonpos hD0.le hc]
    have htD : t/D≤1 := by rw [div_le_one hD0]; linarith
    set xt := W-((bhi:ℝ)+1)*(Y.getD y' 0-1) with hxt
    have zt : xt≤z.1 := by
      have a : (b+t/D)*(z.2-1)≤((bhi:ℝ)+1)*(Y.getD y' 0-1) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      simp only [xt]; linarith
    have xtW : xt≤W := by simp only [xt]; nlinarith [le_trans hb0 hbhi]
    -- the assumed end holds on the strip
    have Q (q : Quad) (k : Nat) (hq : q.ok C k=true) := Quad.sound G one hq
    have c1 := Q _ _ q1; rw [cornerQuad_real,stripX_real,hW,hwy] at c1
    have c2 := Q _ _ q2; rw [cornerQuad_real,stripX_real,hW,hwy] at c2
    have c3 := Q _ _ q3; rw [cornerQuad_real,lx_real,hW] at c3
    have c4 := Q _ _ q4; rw [cornerQuad_real,lx_real,hW] at c4
    have hσ : 0≤(if σ then 1 else -1)*ArtGallery.det (gridPt X Y g) z (gridPt X Y w) := by
      apply nonneg_on _ xtW (lev_le G.hy (by omega) yy'.le) (g₀:=gridPt X Y g) (g₁:=gridPt X Y g) _
        (Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,by simp [Geometry.lerp]⟩) ⟨zt,z1,z2,z3⟩
      intro g' hg' z' hz'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hg' hz'
      rcases hg' with rfl|rfl <;> rcases hz' with rfl|rfl|rfl|rfl <;> linarith
    have hs := CertA.sound G okG (g:=gridPt X Y g) (z:=z)
      (Geometry.mem_segment_iff_lerp.mpr ⟨0,le_rfl,zero_le_one,by simp [Geometry.lerp]⟩)
      ⟨by rw [hdl0]; exact z0,by rw [hW]; exact z1,z2,z3⟩ (fun e he => by rw [aG e he]; exact hσ)
    exact fun p hp => sub (hs hp)

end Door

end ArtGallery.Orthogonal.BoundaryPoint.DoorCell
end
