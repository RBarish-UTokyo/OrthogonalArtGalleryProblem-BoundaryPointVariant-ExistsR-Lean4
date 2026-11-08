module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0XS1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0XHold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0XI0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0XI1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1XHold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1XI0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1XI1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1XI2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1XI3

/-! Range conditions of the other copy test of each channel of profile `InvRevGe_1_10`
(generated), for the completeness proof. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvRevGe_1_10
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Range conditions of the other copy test of channel 0. -/
theorem rangesX0 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 2 ∧ getRat args 2≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 2
    let b : ℝ := ((((1:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    X.getD 44 0=(301:ℝ)/2 ∧
    X.getD 46 0=X.getD 45 0+3/2*(1-Y.getD 1 0)/(50050/s^2) ∧
    0<ArtGallery.det (X.getD 46 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 29 0,Y.getD 36 0) ∧
    ArtGallery.det (X.getD 45 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 30 0,Y.getD 36 0)<0 ∧
    0<(1:ℝ)*(50050/s^2)+(-1:ℝ)*(Y.getD 37 0)+(1:ℝ)*(1) ∧
    0<(3:ℝ)*(Y.getD 36 0)+(-7:ℝ)*(1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 28 0,Y.getD 42 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 28 0,Y.getD 42 0) (s/320,1)<0 := by
  intro s J Q b X Y
  have Xdef : X=(grid template args false).map (fun q : ℚ => (q:ℝ)) := rfl
  have Ydef : Y=(grid template args true).map (fun q : ℚ => (q:ℝ)) := rfl
  have hs : (0:ℝ)<s := by simp only [s]; exact_mod_cast m.pos
  have hs1 : s≤(((1/65:ℚ):ℚ):ℝ) := by simp only [s]; exact_mod_cast m.upper
  have hJ' : (0:ℝ)≤J ∧ J≤1 := by simp only [J]; exact ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  have hQ' : (0:ℝ)≤Q ∧ Q≤1 := by simp only [Q]; exact ⟨by exact_mod_cast hQ.1,by exact_mod_cast hQ.2⟩
  have B : PolyBox.Box (1/65:ℚ) (4/5005:ℚ) (509/130130:ℚ) s b J := by
    refine ⟨hs,hs1,?_,?_,hJ'.1,hJ'.2,by norm_num⟩
    · simp only [b]; push_cast; nlinarith
    · simp only [b]; push_cast at hs1 ⊢; nlinarith [mul_le_mul hJ'.2 hs1 hs.le zero_le_one]
  have hin : ∀ k P d, (k,P,d)∈c0ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c0ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c0xhold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lX44 : Lift s b J (X.getD 44 0) c0xhwxL c0xhwxX44N c0xhwxX44D c0xhwxX44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c0xhwxX44cof⟩
    have lone : Lift s b J (1) c0xhwxL c0xhwxoneN c0xhwxoneD c0xhwxoneC :=
      ⟨by simp [c0xhwxoneN,c0xhwxoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhwxonecof⟩
    have hL : Ex.ev s b J c0xhwxL≠0 := by
      have k := RegCert.auto_sound c0xhwxLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0xhwxok hL (linX_ev (one:=.mul c0xhwxoneN c0xhwxoneC) (lone.eq.trans (one_mul _)) _ [(2,X.getD 44 0),(-301,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX44.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX45 : Lift s b J (X.getD 45 0) c0xhrbL c0xhrbX45N c0xhrbX45D c0xhrbX45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0xhrbX45N,c0xhrbX45D,Ex.ev,ev3,ev2,ev1]
        ring,c0xhrbX45cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0xhrbL c0xhrbX46N c0xhrbX46D c0xhrbX46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0xhrbX46N,c0xhrbX46D,Ex.ev,ev3,ev2,ev1]
        ring,c0xhrbX46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0xhrbL c0xhrbY1N c0xhrbY1D c0xhrbY1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c0xhrbY1N,c0xhrbY1D,Ex.ev,ev3,ev2,ev1]
        ring,c0xhrbY1cof⟩
    have lone : Lift s b J (1) c0xhrbL c0xhrboneN c0xhrboneD c0xhrboneC :=
      ⟨by simp [c0xhrboneN,c0xhrboneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhrbonecof⟩
    have lvD : Lift s b J (50050/s^2) c0xhrbL c0xhrbvDN c0xhrbvDD c0xhrbvDC :=
      ⟨by simp [c0xhrbvDN,c0xhrbvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhrbvDcof⟩
    have hL : Ex.ev s b J c0xhrbL≠0 := by
      have k := RegCert.auto_sound c0xhrbLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (by simp [c0xhrbvDD,Ex.ev,ev3,ev2,ev1]; positivity) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := zero_of_check c0xhrbok hL (spotX_ev lX46.eq lX45.eq lvD.eq lY1.eq (lone.eq.trans (one_mul _)))
    have hs2 : (50050:ℝ)/s^2≠0 := by positivity
    field_simp at h ⊢; linarith
  · have lX29 : Lift s b J (X.getD 29 0) c0xL1L c0xL1X29N c0xL1X29D c0xL1X29C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 29 0=((getRat xs 194 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 29]; rfl
        rw [e]; exact hr.1,c0xL1X29cof⟩
    have lX44 : Lift s b J (X.getD 44 0) c0xL1L c0xL1X44N c0xL1X44D c0xL1X44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c0xL1X44cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0xL1L c0xL1X46N c0xL1X46D c0xL1X46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0xL1X46N,c0xL1X46D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL1X46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0xL1L c0xL1Y1N c0xL1Y1D c0xL1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c0xL1Y1N,c0xL1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL1Y1cof⟩
    have lY12 : Lift s b J (Y.getD 12 0) c0xL1L c0xL1Y12N c0xL1Y12D c0xL1Y12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 12 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 12]; rfl
        rw [e]; exact hr.1,c0xL1Y12cof⟩
    have lY36 : Lift s b J (Y.getD 36 0) c0xL1L c0xL1Y36N c0xL1Y36D c0xL1Y36C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 36 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 36]; rfl
        rw [e]; exact hr.1,c0xL1Y36cof⟩
    have hL : Ex.ev s b J c0xL1L≠0 := by
      have k := RegCert.auto_sound c0xL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).2
    have h := signed_sound B c0xL1ok hL (detX_ev lX46.eq lY1.eq lX44.eq lY12.eq lX29.eq lY36.eq)
    push_cast at h; linarith
  · have lX30 : Lift s b J (X.getD 30 0) c0xL2L c0xL2X30N c0xL2X30D c0xL2X30C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : X.getD 30 0=((getRat xs 251 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 30]; rfl
        rw [e]; exact hr.1,c0xL2X30cof⟩
    have lX44 : Lift s b J (X.getD 44 0) c0xL2L c0xL2X44N c0xL2X44D c0xL2X44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c0xL2X44cof⟩
    have lX45 : Lift s b J (X.getD 45 0) c0xL2L c0xL2X45N c0xL2X45D c0xL2X45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0xL2X45N,c0xL2X45D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL2X45cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0xL2L c0xL2Y1N c0xL2Y1D c0xL2Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c0xL2Y1N,c0xL2Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL2Y1cof⟩
    have lY12 : Lift s b J (Y.getD 12 0) c0xL2L c0xL2Y12N c0xL2Y12D c0xL2Y12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 12 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 12]; rfl
        rw [e]; exact hr.1,c0xL2Y12cof⟩
    have lY36 : Lift s b J (Y.getD 36 0) c0xL2L c0xL2Y36N c0xL2Y36D c0xL2Y36C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 36 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 36]; rfl
        rw [e]; exact hr.1,c0xL2Y36cof⟩
    have hL : Ex.ev s b J c0xL2L≠0 := by
      have k := RegCert.auto_sound c0xL2Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c0xL2ok hL (detX_ev lX45.eq lY1.eq lX44.eq lY12.eq lX30.eq lY36.eq)
    push_cast at h; linarith
  · have lY37 : Lift s b J (Y.getD 37 0) c0xdeepL c0xdeepY37N c0xdeepY37D c0xdeepY37C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 37 0=((getRat xs 230 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 37]; rfl
        rw [e]; exact hr.1,c0xdeepY37cof⟩
    have lone : Lift s b J (1) c0xdeepL c0xdeeponeN c0xdeeponeD c0xdeeponeC :=
      ⟨by simp [c0xdeeponeN,c0xdeeponeD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xdeeponecof⟩
    have lvD : Lift s b J (50050/s^2) c0xdeepL c0xdeepvDN c0xdeepvDD c0xdeepvDC :=
      ⟨by simp [c0xdeepvDN,c0xdeepvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xdeepvDcof⟩
    have hL : Ex.ev s b J c0xdeepL≠0 := by
      have k := RegCert.auto_sound c0xdeepLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (by simp [c0xdeepvDD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xdeepok hL (linX_ev (one:=.mul c0xdeeponeN c0xdeeponeC) (lone.eq.trans (one_mul _)) _ [(1,50050/s^2),(-1,Y.getD 37 0),(1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lvD.eq⟩,⟨by trivial,lY37.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY36 : Lift s b J (Y.getD 36 0) c0xH43L c0xH43Y36N c0xH43Y36D c0xH43Y36C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 36 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 36]; rfl
        rw [e]; exact hr.1,c0xH43Y36cof⟩
    have lone : Lift s b J (1) c0xH43L c0xH43oneN c0xH43oneD c0xH43oneC :=
      ⟨by simp [c0xH43oneN,c0xH43oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xH43onecof⟩
    have hL : Ex.ev s b J c0xH43L≠0 := by
      have k := RegCert.auto_sound c0xH43Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2
    have h := signed_sound B c0xH43ok hL (linX_ev (one:=.mul c0xH43oneN c0xH43oneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 36 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY36.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0xCW0L c0xCW0BxN c0xCW0BxD c0xCW0BxC :=
      ⟨by simp [c0xCW0BxN,c0xCW0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xCW0L c0xCW0ByN c0xCW0ByD c0xCW0ByC :=
      ⟨by simp [c0xCW0ByN,c0xCW0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Bycof⟩
    have lWq : Lift s b J (s/320) c0xCW0L c0xCW0WqN c0xCW0WqD c0xCW0WqC :=
      ⟨by simp [c0xCW0WqN,c0xCW0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Wqcof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xCW0L c0xCW0X28N c0xCW0X28D c0xCW0X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 28 0=((getRat xs 316 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xCW0X28cof⟩
    have lY42 : Lift s b J (Y.getD 42 0) c0xCW0L c0xCW0Y42N c0xCW0Y42D c0xCW0Y42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 42 0=((getRat xs 576 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 42]; rfl
        rw [e]; exact hr.1,c0xCW0Y42cof⟩
    have lone : Lift s b J (1) c0xCW0L c0xCW0oneN c0xCW0oneD c0xCW0oneC :=
      ⟨by simp [c0xCW0oneN,c0xCW0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0onecof⟩
    have hL : Ex.ev s b J c0xCW0L≠0 := by
      have k := RegCert.auto_sound c0xCW0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [c0xCW0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xCW0ok hL (detX_ev lBx.eq lBy.eq lX28.eq lY42.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0xCW1L c0xCW1Bx15N c0xCW1Bx15D c0xCW1Bx15C :=
      ⟨by simp [c0xCW1Bx15N,c0xCW1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xCW1L c0xCW1ByN c0xCW1ByD c0xCW1ByC :=
      ⟨by simp [c0xCW1ByN,c0xCW1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Bycof⟩
    have lWq : Lift s b J (s/320) c0xCW1L c0xCW1WqN c0xCW1WqD c0xCW1WqC :=
      ⟨by simp [c0xCW1WqN,c0xCW1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Wqcof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xCW1L c0xCW1X28N c0xCW1X28D c0xCW1X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 28 0=((getRat xs 316 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xCW1X28cof⟩
    have lY42 : Lift s b J (Y.getD 42 0) c0xCW1L c0xCW1Y42N c0xCW1Y42D c0xCW1Y42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 42 0=((getRat xs 576 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 42]; rfl
        rw [e]; exact hr.1,c0xCW1Y42cof⟩
    have lone : Lift s b J (1) c0xCW1L c0xCW1oneN c0xCW1oneD c0xCW1oneC :=
      ⟨by simp [c0xCW1oneN,c0xCW1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1onecof⟩
    have hL : Ex.ev s b J c0xCW1L≠0 := by
      have k := RegCert.auto_sound c0xCW1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [c0xCW1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xCW1ok hL (detX_ev lBx15.eq lBy.eq lX28.eq lY42.eq lWq.eq lone.eq)
    push_cast at h; linarith

/-- Range conditions of the other copy test of channel 1. -/
theorem rangesX1 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 3 ∧ getRat args 3≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((10:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    0<ArtGallery.det (X.getD 51 0,Y.getD 1 0) (X.getD 15 0,Y.getD 20 0) (X.getD 11 0,Y.getD 24 0) ∧
    0<ArtGallery.det (X.getD 52 0,Y.getD 1 0) (X.getD 15 0,Y.getD 20 0) (X.getD 11 0,Y.getD 24 0) ∧
    ArtGallery.det (X.getD 51 0,Y.getD 1 0) (X.getD 15 0,Y.getD 20 0) (X.getD 12 0,Y.getD 24 0)<0 ∧
    ArtGallery.det (X.getD 52 0,Y.getD 1 0) (X.getD 15 0,Y.getD 20 0) (X.getD 12 0,Y.getD 24 0)<0 ∧
    0<(1:ℝ)*(Y.getD 21 0)+(-1:ℝ)*(1-50050/s^2) ∧
    0<(3:ℝ)*(Y.getD 23 0)+(-7:ℝ)*(1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 12 0,Y.getD 21 0) (0,1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 12 0,Y.getD 21 0) (0,1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 12 0,Y.getD 21 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 12 0,Y.getD 21 0) (s/320,1)<0 ∧
    X.getD 32 0=(0:ℝ)/1 ∧
    X.getD 33 0=s/320 ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 15 0,Y.getD 24 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 15 0,Y.getD 24 0) (s/320,1)<0 := by
  intro s J Q b X Y
  have Xdef : X=(grid template args false).map (fun q : ℚ => (q:ℝ)) := rfl
  have Ydef : Y=(grid template args true).map (fun q : ℚ => (q:ℝ)) := rfl
  have hs : (0:ℝ)<s := by simp only [s]; exact_mod_cast m.pos
  have hs1 : s≤(((1/65:ℚ):ℚ):ℝ) := by simp only [s]; exact_mod_cast m.upper
  have hJ' : (0:ℝ)≤J ∧ J≤1 := by simp only [J]; exact ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  have hQ' : (0:ℝ)≤Q ∧ Q≤1 := by simp only [Q]; exact ⟨by exact_mod_cast hQ.1,by exact_mod_cast hQ.2⟩
  have B : PolyBox.Box (1/65:ℚ) (7/715:ℚ) (1679/130130:ℚ) s b J := by
    refine ⟨hs,hs1,?_,?_,hJ'.1,hJ'.2,by norm_num⟩
    · simp only [b]; push_cast; nlinarith
    · simp only [b]; push_cast at hs1 ⊢; nlinarith [mul_le_mul hJ'.2 hs1 hs.le zero_le_one]
  have hin : ∀ k P d, (k,P,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c1ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c1xhold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lX11 : Lift s b J (X.getD 11 0) c1xUa0L c1xUa0X11N c1xUa0X11D c1xUa0X11C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : X.getD 11 0=((getRat xs 237 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 11]; rfl
        rw [e]; exact hr.1,c1xUa0X11cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUa0L c1xUa0X15N c1xUa0X15D c1xUa0X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 284 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUa0X15cof⟩
    have lX51 : Lift s b J (X.getD 51 0) c1xUa0L c1xUa0X51N c1xUa0X51D c1xUa0X51C :=
      ⟨by
        have e : X.getD 51 0=((((axisOf template false).coordsQ (getRat args 0)).getD 8 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 51]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1xUa0X51N,c1xUa0X51D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa0X51cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUa0L c1xUa0Y1N c1xUa0Y1D c1xUa0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c1xUa0Y1N,c1xUa0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa0Y1cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c1xUa0L c1xUa0Y20N c1xUa0Y20D c1xUa0Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 20 0=((getRat xs 368 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1xUa0Y20cof⟩
    have lY24 : Lift s b J (Y.getD 24 0) c1xUa0L c1xUa0Y24N c1xUa0Y24D c1xUa0Y24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 24 0=((getRat xs 365 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 24]; rfl
        rw [e]; exact hr.1,c1xUa0Y24cof⟩
    have hL : Ex.ev s b J c1xUa0L≠0 := by
      have k := RegCert.auto_sound c1xUa0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUa0ok hL (detX_ev lX51.eq lY1.eq lX15.eq lY20.eq lX11.eq lY24.eq)
    push_cast at h; linarith
  · have lX11 : Lift s b J (X.getD 11 0) c1xUa1L c1xUa1X11N c1xUa1X11D c1xUa1X11C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : X.getD 11 0=((getRat xs 237 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 11]; rfl
        rw [e]; exact hr.1,c1xUa1X11cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUa1L c1xUa1X15N c1xUa1X15D c1xUa1X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 284 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUa1X15cof⟩
    have lX52 : Lift s b J (X.getD 52 0) c1xUa1L c1xUa1X52N c1xUa1X52D c1xUa1X52C :=
      ⟨by
        have e : X.getD 52 0=((((axisOf template false).coordsQ (getRat args 0)).getD 9 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 52]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1xUa1X52N,c1xUa1X52D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa1X52cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUa1L c1xUa1Y1N c1xUa1Y1D c1xUa1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c1xUa1Y1N,c1xUa1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa1Y1cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c1xUa1L c1xUa1Y20N c1xUa1Y20D c1xUa1Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 20 0=((getRat xs 368 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1xUa1Y20cof⟩
    have lY24 : Lift s b J (Y.getD 24 0) c1xUa1L c1xUa1Y24N c1xUa1Y24D c1xUa1Y24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 24 0=((getRat xs 365 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 24]; rfl
        rw [e]; exact hr.1,c1xUa1Y24cof⟩
    have hL : Ex.ev s b J c1xUa1L≠0 := by
      have k := RegCert.auto_sound c1xUa1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUa1ok hL (detX_ev lX52.eq lY1.eq lX15.eq lY20.eq lX11.eq lY24.eq)
    push_cast at h; linarith
  · have lX12 : Lift s b J (X.getD 12 0) c1xUb0L c1xUb0X12N c1xUb0X12D c1xUb0X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 370 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xUb0X12cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUb0L c1xUb0X15N c1xUb0X15D c1xUb0X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 284 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUb0X15cof⟩
    have lX51 : Lift s b J (X.getD 51 0) c1xUb0L c1xUb0X51N c1xUb0X51D c1xUb0X51C :=
      ⟨by
        have e : X.getD 51 0=((((axisOf template false).coordsQ (getRat args 0)).getD 8 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 51]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1xUb0X51N,c1xUb0X51D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb0X51cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUb0L c1xUb0Y1N c1xUb0Y1D c1xUb0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c1xUb0Y1N,c1xUb0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb0Y1cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c1xUb0L c1xUb0Y20N c1xUb0Y20D c1xUb0Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 20 0=((getRat xs 368 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1xUb0Y20cof⟩
    have lY24 : Lift s b J (Y.getD 24 0) c1xUb0L c1xUb0Y24N c1xUb0Y24D c1xUb0Y24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 24 0=((getRat xs 365 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 24]; rfl
        rw [e]; exact hr.1,c1xUb0Y24cof⟩
    have hL : Ex.ev s b J c1xUb0L≠0 := by
      have k := RegCert.auto_sound c1xUb0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUb0ok hL (detX_ev lX51.eq lY1.eq lX15.eq lY20.eq lX12.eq lY24.eq)
    push_cast at h; linarith
  · have lX12 : Lift s b J (X.getD 12 0) c1xUb1L c1xUb1X12N c1xUb1X12D c1xUb1X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 370 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xUb1X12cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUb1L c1xUb1X15N c1xUb1X15D c1xUb1X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 284 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUb1X15cof⟩
    have lX52 : Lift s b J (X.getD 52 0) c1xUb1L c1xUb1X52N c1xUb1X52D c1xUb1X52C :=
      ⟨by
        have e : X.getD 52 0=((((axisOf template false).coordsQ (getRat args 0)).getD 9 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 52]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1xUb1X52N,c1xUb1X52D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb1X52cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUb1L c1xUb1Y1N c1xUb1Y1D c1xUb1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c1xUb1Y1N,c1xUb1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb1Y1cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c1xUb1L c1xUb1Y20N c1xUb1Y20D c1xUb1Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 20 0=((getRat xs 368 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1xUb1Y20cof⟩
    have lY24 : Lift s b J (Y.getD 24 0) c1xUb1L c1xUb1Y24N c1xUb1Y24D c1xUb1Y24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 24 0=((getRat xs 365 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 24]; rfl
        rw [e]; exact hr.1,c1xUb1Y24cof⟩
    have hL : Ex.ev s b J c1xUb1L≠0 := by
      have k := RegCert.auto_sound c1xUb1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUb1ok hL (detX_ev lX52.eq lY1.eq lX15.eq lY20.eq lX12.eq lY24.eq)
    push_cast at h; linarith
  · have lBy : Lift s b J (1-50050/s^2) c1xbLowL c1xbLowByN c1xbLowByD c1xbLowByC :=
      ⟨by simp [c1xbLowByN,c1xbLowByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xbLowBycof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xbLowL c1xbLowY21N c1xbLowY21D c1xbLowY21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 21 0=((getRat xs 286 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xbLowY21cof⟩
    have lone : Lift s b J (1) c1xbLowL c1xbLowoneN c1xbLowoneD c1xbLowoneC :=
      ⟨by simp [c1xbLowoneN,c1xbLowoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xbLowonecof⟩
    have hL : Ex.ev s b J c1xbLowL≠0 := by
      have k := RegCert.auto_sound c1xbLowLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [c1xbLowByD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xbLowok hL (linX_ev (one:=.mul c1xbLowoneN c1xbLowoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 21 0),(-1,1-50050/s^2)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY21.eq⟩,⟨by trivial,lBy.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY23 : Lift s b J (Y.getD 23 0) c1xH43uL c1xH43uY23N c1xH43uY23D c1xH43uY23C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : Y.getD 23 0=((getRat xs 278 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 23]; rfl
        rw [e]; exact hr.1,c1xH43uY23cof⟩
    have lone : Lift s b J (1) c1xH43uL c1xH43uoneN c1xH43uoneD c1xH43uoneC :=
      ⟨by simp [c1xH43uoneN,c1xH43uoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xH43uonecof⟩
    have hL : Ex.ev s b J c1xH43uL≠0 := by
      have k := RegCert.auto_sound c1xH43uLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).2
    have h := signed_sound B c1xH43uok hL (linX_ev (one:=.mul c1xH43uoneN c1xH43uoneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 23 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY23.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c1xDL0L c1xDL0BxN c1xDL0BxD c1xDL0BxC :=
      ⟨by simp [c1xDL0BxN,c1xDL0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xDL0L c1xDL0ByN c1xDL0ByD c1xDL0ByC :=
      ⟨by simp [c1xDL0ByN,c1xDL0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0Bycof⟩
    have lX12 : Lift s b J (X.getD 12 0) c1xDL0L c1xDL0X12N c1xDL0X12D c1xDL0X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 370 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDL0X12cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xDL0L c1xDL0Y21N c1xDL0Y21D c1xDL0Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 21 0=((getRat xs 286 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xDL0Y21cof⟩
    have lone : Lift s b J (1) c1xDL0L c1xDL0oneN c1xDL0oneD c1xDL0oneC :=
      ⟨by simp [c1xDL0oneN,c1xDL0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0onecof⟩
    have lzero : Lift s b J (0) c1xDL0L c1xDL0zeroN c1xDL0zeroD c1xDL0zeroC :=
      ⟨by simp [c1xDL0zeroN,c1xDL0zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0zerocof⟩
    have hL : Ex.ev s b J c1xDL0L≠0 := by
      have k := RegCert.auto_sound c1xDL0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDL0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDL0ok hL (detX_ev lBx.eq lBy.eq lX12.eq lY21.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c1xDL1L c1xDL1Bx15N c1xDL1Bx15D c1xDL1Bx15C :=
      ⟨by simp [c1xDL1Bx15N,c1xDL1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xDL1L c1xDL1ByN c1xDL1ByD c1xDL1ByC :=
      ⟨by simp [c1xDL1ByN,c1xDL1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1Bycof⟩
    have lX12 : Lift s b J (X.getD 12 0) c1xDL1L c1xDL1X12N c1xDL1X12D c1xDL1X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 370 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDL1X12cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xDL1L c1xDL1Y21N c1xDL1Y21D c1xDL1Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 21 0=((getRat xs 286 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xDL1Y21cof⟩
    have lone : Lift s b J (1) c1xDL1L c1xDL1oneN c1xDL1oneD c1xDL1oneC :=
      ⟨by simp [c1xDL1oneN,c1xDL1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1onecof⟩
    have lzero : Lift s b J (0) c1xDL1L c1xDL1zeroN c1xDL1zeroD c1xDL1zeroC :=
      ⟨by simp [c1xDL1zeroN,c1xDL1zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1zerocof⟩
    have hL : Ex.ev s b J c1xDL1L≠0 := by
      have k := RegCert.auto_sound c1xDL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDL1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDL1ok hL (detX_ev lBx15.eq lBy.eq lX12.eq lY21.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c1xDR0L c1xDR0BxN c1xDR0BxD c1xDR0BxC :=
      ⟨by simp [c1xDR0BxN,c1xDR0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xDR0L c1xDR0ByN c1xDR0ByD c1xDR0ByC :=
      ⟨by simp [c1xDR0ByN,c1xDR0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR0Bycof⟩
    have lWq : Lift s b J (s/320) c1xDR0L c1xDR0WqN c1xDR0WqD c1xDR0WqC :=
      ⟨by simp [c1xDR0WqN,c1xDR0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR0Wqcof⟩
    have lX12 : Lift s b J (X.getD 12 0) c1xDR0L c1xDR0X12N c1xDR0X12D c1xDR0X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 370 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDR0X12cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xDR0L c1xDR0Y21N c1xDR0Y21D c1xDR0Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 21 0=((getRat xs 286 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xDR0Y21cof⟩
    have lone : Lift s b J (1) c1xDR0L c1xDR0oneN c1xDR0oneD c1xDR0oneC :=
      ⟨by simp [c1xDR0oneN,c1xDR0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR0onecof⟩
    have hL : Ex.ev s b J c1xDR0L≠0 := by
      have k := RegCert.auto_sound c1xDR0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDR0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDR0ok hL (detX_ev lBx.eq lBy.eq lX12.eq lY21.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c1xDR1L c1xDR1Bx15N c1xDR1Bx15D c1xDR1Bx15C :=
      ⟨by simp [c1xDR1Bx15N,c1xDR1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xDR1L c1xDR1ByN c1xDR1ByD c1xDR1ByC :=
      ⟨by simp [c1xDR1ByN,c1xDR1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR1Bycof⟩
    have lWq : Lift s b J (s/320) c1xDR1L c1xDR1WqN c1xDR1WqD c1xDR1WqC :=
      ⟨by simp [c1xDR1WqN,c1xDR1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR1Wqcof⟩
    have lX12 : Lift s b J (X.getD 12 0) c1xDR1L c1xDR1X12N c1xDR1X12D c1xDR1X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 370 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDR1X12cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xDR1L c1xDR1Y21N c1xDR1Y21D c1xDR1Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 21 0=((getRat xs 286 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xDR1Y21cof⟩
    have lone : Lift s b J (1) c1xDR1L c1xDR1oneN c1xDR1oneD c1xDR1oneC :=
      ⟨by simp [c1xDR1oneN,c1xDR1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR1onecof⟩
    have hL : Ex.ev s b J c1xDR1L≠0 := by
      have k := RegCert.auto_sound c1xDR1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDR1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDR1ok hL (detX_ev lBx15.eq lBy.eq lX12.eq lY21.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lX32 : Lift s b J (X.getD 32 0) c1xhdlL c1xhdlX32N c1xhdlX32D c1xhdlX32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : X.getD 32 0=((getRat xs 684 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 32]; rfl
        rw [e]; exact hr.1,c1xhdlX32cof⟩
    have lone : Lift s b J (1) c1xhdlL c1xhdloneN c1xhdloneD c1xhdloneC :=
      ⟨by simp [c1xhdloneN,c1xhdloneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xhdlonecof⟩
    have hL : Ex.ev s b J c1xhdlL≠0 := by
      have k := RegCert.auto_sound c1xhdlLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1xhdlok hL (linX_ev (one:=.mul c1xhdloneN c1xhdloneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 32 0),(0,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX32.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lWq : Lift s b J (s/320) c1xhdrL c1xhdrWqN c1xhdrWqD c1xhdrWqC :=
      ⟨by simp [c1xhdrWqN,c1xhdrWqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xhdrWqcof⟩
    have lX33 : Lift s b J (X.getD 33 0) c1xhdrL c1xhdrX33N c1xhdrX33D c1xhdrX33C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 33 0=((getRat xs 830 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 33]; rfl
        rw [e]; exact hr.1,c1xhdrX33cof⟩
    have lone : Lift s b J (1) c1xhdrL c1xhdroneN c1xhdroneD c1xhdroneC :=
      ⟨by simp [c1xhdroneN,c1xhdroneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xhdronecof⟩
    have hL : Ex.ev s b J c1xhdrL≠0 := by
      have k := RegCert.auto_sound c1xhdrLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1xhdrok hL (linX_ev (one:=.mul c1xhdroneN c1xhdroneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 33 0),(-1,s/320)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX33.eq⟩,⟨by trivial,lWq.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c1xCW0L c1xCW0BxN c1xCW0BxD c1xCW0BxC :=
      ⟨by simp [c1xCW0BxN,c1xCW0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xCW0L c1xCW0ByN c1xCW0ByD c1xCW0ByC :=
      ⟨by simp [c1xCW0ByN,c1xCW0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0Bycof⟩
    have lWq : Lift s b J (s/320) c1xCW0L c1xCW0WqN c1xCW0WqD c1xCW0WqC :=
      ⟨by simp [c1xCW0WqN,c1xCW0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0Wqcof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xCW0L c1xCW0X15N c1xCW0X15D c1xCW0X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 284 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xCW0X15cof⟩
    have lY24 : Lift s b J (Y.getD 24 0) c1xCW0L c1xCW0Y24N c1xCW0Y24D c1xCW0Y24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 24 0=((getRat xs 365 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 24]; rfl
        rw [e]; exact hr.1,c1xCW0Y24cof⟩
    have lone : Lift s b J (1) c1xCW0L c1xCW0oneN c1xCW0oneD c1xCW0oneC :=
      ⟨by simp [c1xCW0oneN,c1xCW0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0onecof⟩
    have hL : Ex.ev s b J c1xCW0L≠0 := by
      have k := RegCert.auto_sound c1xCW0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c1xCW0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xCW0ok hL (detX_ev lBx.eq lBy.eq lX15.eq lY24.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c1xCW1L c1xCW1Bx15N c1xCW1Bx15D c1xCW1Bx15C :=
      ⟨by simp [c1xCW1Bx15N,c1xCW1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xCW1L c1xCW1ByN c1xCW1ByD c1xCW1ByC :=
      ⟨by simp [c1xCW1ByN,c1xCW1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1Bycof⟩
    have lWq : Lift s b J (s/320) c1xCW1L c1xCW1WqN c1xCW1WqD c1xCW1WqC :=
      ⟨by simp [c1xCW1WqN,c1xCW1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1Wqcof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xCW1L c1xCW1X15N c1xCW1X15D c1xCW1X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 284 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xCW1X15cof⟩
    have lY24 : Lift s b J (Y.getD 24 0) c1xCW1L c1xCW1Y24N c1xCW1Y24D c1xCW1Y24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 24 0=((getRat xs 365 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 24]; rfl
        rw [e]; exact hr.1,c1xCW1Y24cof⟩
    have lone : Lift s b J (1) c1xCW1L c1xCW1oneN c1xCW1oneD c1xCW1oneC :=
      ⟨by simp [c1xCW1oneN,c1xCW1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1onecof⟩
    have hL : Ex.ev s b J c1xCW1L≠0 := by
      have k := RegCert.auto_sound c1xCW1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c1xCW1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xCW1ok hL (detX_ev lBx15.eq lBy.eq lX15.eq lY24.eq lWq.eq lone.eq)
    push_cast at h; linarith

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10
end
