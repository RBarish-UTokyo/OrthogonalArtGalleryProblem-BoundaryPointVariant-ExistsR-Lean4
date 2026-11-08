module

public import ArtGallery.Orthogonal.BoundaryPoint.DoorCell

/-! # A cell covered by two guards

Two chain certificates, each from its own guard segment with one assumed window end, cover a cell
when the sum of the two signed determinants of the assumed ends is nonnegative at the four corners of
the cell for every pair of segment ends: the sum is affine in the target and in each guard, so it is
nonnegative on the whole cell for all guard positions, and one of the two assumed ends holds. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.UnionCell
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert CoverChain CoverAssume QuadCheck
open NookCell DoorCell ArtGallery.Orthogonal.Hard

/-- The sixteen sign combinations: guard ends × guard ends × cell corners. -/
def combos (a₀ a₁ b₀ b₁ : Index) (x x' y y' : Nat) : List (Index × Index × Nat × Nat) :=
  [a₀,a₁].flatMap fun ga => [b₀,b₁].flatMap fun gb => [(ga,gb,x,y),(ga,gb,x',y),(ga,gb,x,y'),(ga,gb,x',y')]

def unionOK (C : Chart) (a₀ a₁ wa : Index) (σa : Bool) (b₀ b₁ wb : Index) (σb : Bool) (x x' y y' : Nat)
    (cA cB : CertA) (ks : List Nat) : Bool :=
  cA.ok C a₀ a₁ x x' y y' && cA.assumed.all (· == (wa,σa)) &&
  cB.ok C b₀ b₁ x x' y y' && cB.assumed.all (· == (wb,σb)) &&
  ((combos a₀ a₁ b₀ b₁ x x' y y').zip ks).all (fun p =>
    (cornerQuad p.1.1 wa (lx p.1.2.2.1) p.1.2.2.2 σa++cornerQuad p.1.2.1 wb (lx p.1.2.2.1) p.1.2.2.2 σb).okN C p.2) &&
  decide (ks.length=16 ∧ x<x' ∧ x'<C.nx ∧ y<y' ∧ y'<C.ny)

/-- The determinant is affine in the guard along a segment. -/
theorem det_lerp (p q z w : Point) (u : ℝ) :
    ArtGallery.det (Geometry.lerp p q u) z w=(1-u)*ArtGallery.det p z w+u*ArtGallery.det q z w := by
  simp only [ArtGallery.det,Geometry.lerp]; ring

/-- An affine function nonnegative at the corners of a rectangle is nonnegative on it. -/
theorem affine_rect {a b c x₀ x₁ y₀ y₁ X Y : ℝ} (hx : x₀<x₁) (hy : y₀<y₁)
    (lx : x₀≤X) (rx : X≤x₁) (ly : y₀≤Y) (ry : Y≤y₁)
    (h00 : 0≤a+b*x₀+c*y₀) (h10 : 0≤a+b*x₁+c*y₀) (h01 : 0≤a+b*x₀+c*y₁) (h11 : 0≤a+b*x₁+c*y₁) :
    0≤a+b*X+c*Y := by
  have key : (x₁-x₀)*(y₁-y₀)*(a+b*X+c*Y)=(x₁-X)*(y₁-Y)*(a+b*x₀+c*y₀)+(X-x₀)*(y₁-Y)*(a+b*x₁+c*y₀)+
      (x₁-X)*(Y-y₀)*(a+b*x₀+c*y₁)+(X-x₀)*(Y-y₀)*(a+b*x₁+c*y₁) := by ring
  have pos : 0<(x₁-x₀)*(y₁-y₀) := mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)
  have rhs : 0≤(x₁-X)*(y₁-Y)*(a+b*x₀+c*y₀)+(X-x₀)*(y₁-Y)*(a+b*x₁+c*y₀)+
      (x₁-X)*(Y-y₀)*(a+b*x₀+c*y₁)+(X-x₀)*(Y-y₀)*(a+b*x₁+c*y₁) := by
    have e1 := mul_nonneg (mul_nonneg (sub_nonneg.mpr rx) (sub_nonneg.mpr ry)) h00
    have e2 := mul_nonneg (mul_nonneg (sub_nonneg.mpr lx) (sub_nonneg.mpr ry)) h10
    have e3 := mul_nonneg (mul_nonneg (sub_nonneg.mpr rx) (sub_nonneg.mpr ly)) h01
    have e4 := mul_nonneg (mul_nonneg (sub_nonneg.mpr lx) (sub_nonneg.mpr ly)) h11
    linarith
  rw [← key] at rhs
  exact (mul_nonneg_iff_of_pos_left pos).mp rhs

section
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

set_option maxHeartbeats 4000000 in
theorem union_sound (G : Good C X Y s A) (one : A 0=1)
    {a₀ a₁ wa b₀ b₁ wb : Index} {σa σb : Bool} {x x' y y' : Nat} {cA cB : CertA} {ks : List Nat}
    (ok : unionOK C a₀ a₁ wa σa b₀ b₁ wb σb x x' y y' cA cB ks=true)
    {ga gb z : Point} (hga : ga∈ArtGallery.segment (gridPt X Y a₀) (gridPt X Y a₁))
    (hgb : gb∈ArtGallery.segment (gridPt X Y b₀) (gridPt X Y b₁))
    (hz : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0)) :
    (C.poly X Y).Sees ga z ∨ (C.poly X Y).Sees gb z := by
  simp only [unionOK,Bool.and_eq_true,List.all_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨okA,aA⟩,okB⟩,aB⟩,qs⟩,⟨klen,xx,x'n,yy,y'n⟩⟩ := ok
  have hlx := G.lx; have hly := G.ly
  have ltx := SepGeom.level_lt G.hx (by omega : x'<X.length) xx
  have lty := SepGeom.level_lt G.hy (by omega : y'<Y.length) yy
  -- the signed determinants of the two assumed ends
  let fa : Point → Point → ℝ := fun g p => (if σa then 1 else -1)*ArtGallery.det g p (gridPt X Y wa)
  let fb : Point → Point → ℝ := fun g p => (if σb then 1 else -1)*ArtGallery.det g p (gridPt X Y wb)
  -- the sixteen checked signs
  have corner (ea : Index) (hea : ea=a₀ ∨ ea=a₁) (eb : Index) (heb : eb=b₀ ∨ eb=b₁) (i j : Nat)
      (hi : i=x ∨ i=x') (hj : j=y ∨ j=y') :
      0≤fa (gridPt X Y ea) (X.getD i 0,Y.getD j 0)+fb (gridPt X Y eb) (X.getD i 0,Y.getD j 0) := by
    have mem : ((ea,eb,i,j),ks.getD ((combos a₀ a₁ b₀ b₁ x x' y y').idxOf (ea,eb,i,j)) 0)∈
        (combos a₀ a₁ b₀ b₁ x x' y y').zip ks := by
      have hm : (ea,eb,i,j)∈combos a₀ a₁ b₀ b₁ x x' y y' := by
        simp only [combos,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,Prod.mk.injEq]
        rcases hea with rfl|rfl <;> rcases heb with rfl|rfl <;> rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> simp
      have hlen : (combos a₀ a₁ b₀ b₁ x x' y y').length=16 := by simp [combos]
      have hidx := List.idxOf_lt_length_of_mem hm
      rw [List.mem_iff_getElem]
      refine ⟨(combos a₀ a₁ b₀ b₁ x x' y y').idxOf (ea,eb,i,j),by simp [List.length_zip]; omega,?_⟩
      simp only [List.getElem_zip,List.getElem_idxOf]
      rw [List.getD_eq_getElem _ _ (by omega)]
    have h := Quad.sound_nonneg G one (qs _ mem)
    simp only [Quad.real,List.map_append,List.sum_append] at h
    have e1 := cornerQuad_real (X:=X) (Y:=Y) (s:=(s:ℝ)) ea wa (lx i) j σa
    have e2 := cornerQuad_real (X:=X) (Y:=Y) (s:=(s:ℝ)) eb wb (lx i) j σb
    simp only [Quad.real,lx_real] at e1 e2
    rw [e1,e2] at h
    exact h
  -- guards as interpolations of their segment ends
  obtain ⟨u,u0,u1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hga
  obtain ⟨v,v0,v1,rfl⟩ := Geometry.mem_segment_iff_lerp.mp hgb
  have atCorner (i j : Nat) (hi : i=x ∨ i=x') (hj : j=y ∨ j=y') :
      0≤fa (Geometry.lerp (gridPt X Y a₀) (gridPt X Y a₁) u) (X.getD i 0,Y.getD j 0)+
        fb (Geometry.lerp (gridPt X Y b₀) (gridPt X Y b₁) v) (X.getD i 0,Y.getD j 0) := by
    have c00 := corner a₀ (Or.inl rfl) b₀ (Or.inl rfl) i j hi hj
    have c01 := corner a₀ (Or.inl rfl) b₁ (Or.inr rfl) i j hi hj
    have c10 := corner a₁ (Or.inr rfl) b₀ (Or.inl rfl) i j hi hj
    have c11 := corner a₁ (Or.inr rfl) b₁ (Or.inr rfl) i j hi hj
    simp only [fa,fb,det_lerp] at c00 c01 c10 c11 ⊢
    generalize (if σa then (1:ℝ) else -1)=sa at *
    generalize (if σb then (1:ℝ) else -1)=sb at *
    generalize ArtGallery.det (gridPt X Y a₀) (X.getD i 0,Y.getD j 0) (gridPt X Y wa)=A0 at *
    generalize ArtGallery.det (gridPt X Y a₁) (X.getD i 0,Y.getD j 0) (gridPt X Y wa)=A1 at *
    generalize ArtGallery.det (gridPt X Y b₀) (X.getD i 0,Y.getD j 0) (gridPt X Y wb)=B0 at *
    generalize ArtGallery.det (gridPt X Y b₁) (X.getD i 0,Y.getD j 0) (gridPt X Y wb)=B1 at *
    have w1 : 0≤(1-u)*(1-v) := mul_nonneg (by linarith) (by linarith)
    have w2 : 0≤(1-u)*v := mul_nonneg (by linarith) v0
    have w3 : 0≤u*(1-v) := mul_nonneg u0 (by linarith)
    have w4 : 0≤u*v := mul_nonneg u0 v0
    have e : sa*((1-u)*A0+u*A1)+sb*((1-v)*B0+v*B1)=(1-u)*(1-v)*(sa*A0+sb*B0)+(1-u)*v*(sa*A0+sb*B1)+
        u*(1-v)*(sa*A1+sb*B0)+u*v*(sa*A1+sb*B1) := by ring
    rw [e]
    have := mul_nonneg w1 c00; have := mul_nonneg w2 c01; have := mul_nonneg w3 c10; have := mul_nonneg w4 c11
    linarith
  set ga := Geometry.lerp (gridPt X Y a₀) (gridPt X Y a₁) u
  set gb := Geometry.lerp (gridPt X Y b₀) (gridPt X Y b₁) v
  -- the sum is affine in the target
  have aff (p : Point) : fa ga p+fb gb p=
      ((if σa then 1 else -1)*(-ga.1*((gridPt X Y wa).2-ga.2)+((gridPt X Y wa).1-ga.1)*ga.2)+
        (if σb then 1 else -1)*(-gb.1*((gridPt X Y wb).2-gb.2)+((gridPt X Y wb).1-gb.1)*gb.2))+
      ((if σa then 1 else -1)*((gridPt X Y wa).2-ga.2)+(if σb then 1 else -1)*((gridPt X Y wb).2-gb.2))*p.1+
      (-(if σa then 1 else -1)*((gridPt X Y wa).1-ga.1)-(if σb then 1 else -1)*((gridPt X Y wb).1-gb.1))*p.2 := by
    simp only [fa,fb,ArtGallery.det]; ring
  obtain ⟨z0,z1,z2,z3⟩ := hz
  have total : 0≤fa ga z+fb gb z := by
    rw [aff]
    apply affine_rect ltx lty z0 z1 z2 z3
    · have := atCorner x y (Or.inl rfl) (Or.inl rfl); rw [aff] at this; exact this
    · have := atCorner x' y (Or.inr rfl) (Or.inl rfl); rw [aff] at this; exact this
    · have := atCorner x y' (Or.inl rfl) (Or.inr rfl); rw [aff] at this; exact this
    · have := atCorner x' y' (Or.inr rfl) (Or.inr rfl); rw [aff] at this; exact this
  have hzR : z∈Rect (X.getD x 0) (X.getD x' 0) (Y.getD y 0) (Y.getD y' 0) := ⟨z0,z1,z2,z3⟩
  rcases le_total 0 (fa ga z) with h|h
  · left
    refine CertA.sound G okA (Geometry.mem_segment_iff_lerp.mpr ⟨u,u0,u1,rfl⟩) hzR fun e he => ?_
    rw [aA e he]; exact h
  · right
    refine CertA.sound G okB (Geometry.mem_segment_iff_lerp.mpr ⟨v,v0,v1,rfl⟩) hzR fun e he => ?_
    rw [aB e he]; show 0≤fb gb z; linarith

end

end ArtGallery.Orthogonal.BoundaryPoint.UnionCell
end
