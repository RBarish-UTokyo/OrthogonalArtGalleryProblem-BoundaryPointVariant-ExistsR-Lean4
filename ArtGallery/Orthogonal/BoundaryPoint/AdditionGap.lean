module

public import ArtGallery.Orthogonal.BoundaryPoint.InverseGap

/-! # Reading the addition triangle from physical blockers
Every target in the addition box is downstream of a fixed test slice. A
sightline to the target crosses that slice. Transferring the corner inequality
along the same ray makes the test apply throughout the two-dimensional box. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.AdditionGap
open Set Geometry SlabSight SlotLines

theorem transfer {P : Polygon} {g z c : Point} (axis : ℝ) (north : Bool)
    (H : axis∈uIcc g.1 z.1) (forward : 0<(axis-g.1)/(z.1-g.1))
    (d : 100≤|z.1-g.1|) (dx : |axis-z.1|≤2) (dy : |z.2-g.2|≤4)
    (y0 : 49/100≤z.2) (y1 : z.2≤51/100)
    (test : ∀ Y : ℝ, 2/5≤Y → Y≤3/5 → P.Sees g (axis,Y) →
      if north then Y≤rayY g c axis else rayY g c axis≤Y)
    (seen : P.Sees g z) :
    if north then z.2≤rayY g c z.1 else rayY g c z.1≤z.2 := by
  have nonzero : z.1-g.1≠0 := by intro h; rw [h,abs_zero] at d; norm_num at d
  let Y := height g.1 g.2 z.1 z.2 axis
  have diff : Y-z.2=((axis-z.1)*(z.2-g.2))/(z.1-g.1) := by
    dsimp [Y,height]; field_simp [nonzero]; ring
  have dist : |Y-z.2|≤2/25 := by
    rw [diff,abs_div,abs_mul]
    apply (div_le_iff₀ (abs_pos.mpr nonzero)).mpr
    have h := mul_le_mul dx dy (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    nlinarith only [h,d]
  have hb := abs_le.mp dist
  have cut : (axis,Y)∈ArtGallery.segment g z := path (Ne.symm (sub_ne_zero.mp nonzero)) H false
  have sub : P.Sees g (axis,Y) :=
    (segment_subset_of_convex (s:=ArtGallery.segment g z) (segment_eq .. ▸ convex_segment ..)
      (left_mem_segment ..) cut).trans seen
  have hh := test Y (by linarith [hb.1]) (by linarith [hb.2]) sub
  have same : Y-rayY g c axis=(z.2-rayY g c z.1)*((axis-g.1)/(z.1-g.1)) := by
    dsimp [Y,height,rayY]
    by_cases cz : c.1-g.1=0
    · rw [cz]; simp only [div_zero,add_zero]; field_simp [nonzero]; ring
    · field_simp [nonzero,cz]; ring
  cases north <;> simp only [Bool.false_eq_true,ite_true,ite_false] at hh ⊢
  · exact sub_nonneg.mp (nonneg_of_mul_nonneg_left (same ▸ sub_nonneg.mpr hh) forward)
  · exact sub_nonpos.mp (nonpos_of_mul_nonpos_left (same ▸ sub_nonpos.mpr hh) forward)

theorem box_transfer {P : Polygon} {g c : Point} (right north : Bool) {X Y : ℝ}
    (whereG : if right then 969≤g.1 else g.1≤767) (floor : -3≤g.2 ∧ g.2≤0)
    (lx : 867≤X) (rx : X≤869) (ly : 49/100≤Y) (ry : Y≤51/100)
    (test : let T : ℝ := if right then 869 else 867
      ∀ H : ℝ, 2/5≤H → H≤3/5 → P.Sees g (T,H) →
        if north then H≤rayY g c T else rayY g c T≤H)
    (seen : P.Sees g (X,Y)) : if north then Y≤rayY g c X else rayY g c X≤Y := by
  have dy : |Y-g.2|≤4 := abs_le.mpr ⟨by linarith [floor.2],by linarith [floor.1]⟩
  cases right with
  | false =>
    change g.1≤767 at whereG
    have left : g.1<X := by linarith
    apply transfer (z:=(X,Y)) 867 north _ _ _ _ dy ly ry test seen
    · rw [uIcc_of_le left.le]; exact ⟨by linarith,lx⟩
    · exact div_pos (by linarith) (sub_pos.mpr left)
    · rw [abs_of_nonneg (sub_nonneg.mpr left.le)]; linarith
    · exact abs_le.mpr ⟨by linarith,by linarith⟩
  | true =>
    change 969≤g.1 at whereG
    have left : X<g.1 := by linarith
    apply transfer (z:=(X,Y)) 869 north _ _ _ _ dy ly ry test seen
    · rw [uIcc_of_ge left.le]; exact ⟨rx,by linarith⟩
    · exact div_pos_of_neg_of_neg (by linarith) (sub_neg.mpr left)
    · rw [abs_of_nonpos (sub_nonpos.mpr left.le)]; linarith
    · exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem slope_line {g : Point} (e X : ℝ) (hy : g.2≠0) (hx : e≠g.1) :
    xSlope e g*rayY g (e,0) X=X-e := by
  dsimp [xSlope,rayY]; field_simp [hy,sub_ne_zero.mpr hx]; ring

theorem triangle {bx br bz : ℝ}
    (bxB : 2039/10≤bx ∧ bx≤2041/10) (brB : -9031/10≤br ∧ br≤ -9029/10)
    (cover : ∀ X Y : ℝ, 867≤X → X≤869 → 49/100≤Y → Y≤51/100 →
      766+bx*Y≤X ∨ 2639/2+br*Y≤X ∨ X≤1655/2+bz*Y) :
    (8*bx+br)/9-bz≤0 := by
  by_contra! bad
  let y := (2639/2-766)/(bx-br)
  let x := 766+bx*y
  have bd : 0<bx-br := by linarith [bxB.1,brB.2]
  have ylo : 499/1000<y := by
    apply (lt_div_iff₀ bd).mpr
    linarith [bxB.2,brB.1]
  have yhi : y<501/1000 := by
    apply (div_lt_iff₀ bd).mpr
    linarith [bxB.1,brB.2]
  have yPos : 0<y := by linarith
  have lower : 867<x := by
    dsimp only [x]
    nlinarith only [mul_le_mul bxB.1 ylo.le (by norm_num : (0:ℝ)≤499/1000) (by linarith [bxB.1]:0≤bx)]
  have upper : x<869 := by
    dsimp only [x]
    nlinarith only [mul_le_mul bxB.2 yhi.le yPos.le (by norm_num : (0:ℝ)≤2041/10)]
  have yy : y*(bx-br)=2639/2-766 := by dsimp [y]; exact div_mul_cancel₀ _ bd.ne'
  have xeq : x=2639/2+br*y := by dsimp only [x]; linarith [yy]
  have gap : 0<x-(1655/2+bz*y) := by
    dsimp only [x]
    nlinarith only [yy,mul_pos bad yPos]
  let ε := min (x-867) (x-(1655/2+bz*y))/2
  have ee : 0<ε := by dsimp [ε]; exact div_pos (lt_min (sub_pos.mpr lower) gap) (by norm_num)
  have off1 : ε<x-867 := by dsimp [ε]; linarith [min_le_left (x-867) (x-(1655/2+bz*y))]
  have off2 : ε<x-(1655/2+bz*y) := by dsimp [ε]; linarith [min_le_right (x-867) (x-(1655/2+bz*y))]
  rcases cover (x-ε) y (by linarith) (by linarith) (by linarith) (by linarith) with a|b|c
  · change x≤x-ε at a; linarith
  · linarith [xeq]
  · linarith

end ArtGallery.Orthogonal.BoundaryPoint.AdditionGap
end
