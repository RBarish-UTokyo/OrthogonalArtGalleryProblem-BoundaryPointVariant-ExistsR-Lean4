module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0Hold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0I0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C0I1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1Hold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1I0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200.C1I1

/-! Range conditions of the copy tests of profile `InvLe_1_200` (generated): closed forms through
branch rows (`RegChain`), lifts to a common denominator, signs on the parameter box. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvLe_1_200
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Range conditions of the copy tests of channel 0. -/
theorem ranges0 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 2 ∧ getRat args 2≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 2
    let b : ℝ := ((((1:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    X.getD 44 0=(301:ℝ)/2 ∧
    Y.getD 13 0=(1:ℝ)/1 ∧
    X.getD 46 0=X.getD 45 0+3/2*(1-Y.getD 1 0)/(50050/s^2) ∧
    0<ArtGallery.det (X.getD 46 0,Y.getD 1 0) (X.getD 44 0,Y.getD 13 0) (X.getD 29 0,Y.getD 37 0) ∧
    ArtGallery.det (X.getD 45 0,Y.getD 1 0) (X.getD 44 0,Y.getD 13 0) (X.getD 30 0,Y.getD 37 0)<0 ∧
    0<(1:ℝ)*(50050/s^2)+(-1:ℝ)*(Y.getD 38 0)+(1:ℝ)*(1) ∧
    0<(3:ℝ)*(Y.getD 37 0)+(-7:ℝ)*(1) := by
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
  have H := c0hold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have lX44 : Lift s b J (X.getD 44 0) c0hwxL c0hwxX44N c0hwxX44D c0hwxX44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c0hwxX44cof⟩
    have lone : Lift s b J (1) c0hwxL c0hwxoneN c0hwxoneD c0hwxoneC :=
      ⟨by simp [c0hwxoneN,c0hwxoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hwxonecof⟩
    have hL : Ex.ev s b J c0hwxL≠0 := by
      have k := RegCert.auto_sound c0hwxLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hwxok hL (linX_ev (one:=.mul c0hwxoneN c0hwxoneC) (lone.eq.trans (one_mul _)) _ [(2,X.getD 44 0),(-301,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX44.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY13 : Lift s b J (Y.getD 13 0) c0hwyL c0hwyY13N c0hwyY13D c0hwyY13C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 13 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 13]; rfl
        rw [e]; exact hr.1,c0hwyY13cof⟩
    have lone : Lift s b J (1) c0hwyL c0hwyoneN c0hwyoneD c0hwyoneC :=
      ⟨by simp [c0hwyoneN,c0hwyoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hwyonecof⟩
    have hL : Ex.ev s b J c0hwyL≠0 := by
      have k := RegCert.auto_sound c0hwyLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hwyok hL (linX_ev (one:=.mul c0hwyoneN c0hwyoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 13 0),(-1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY13.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX45 : Lift s b J (X.getD 45 0) c0hrbL c0hrbX45N c0hrbX45D c0hrbX45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0hrbX45N,c0hrbX45D,Ex.ev,ev3,ev2,ev1]
        ring,c0hrbX45cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0hrbL c0hrbX46N c0hrbX46D c0hrbX46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0hrbX46N,c0hrbX46D,Ex.ev,ev3,ev2,ev1]
        ring,c0hrbX46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0hrbL c0hrbY1N c0hrbY1D c0hrbY1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c0hrbY1N,c0hrbY1D,Ex.ev,ev3,ev2,ev1]
        ring,c0hrbY1cof⟩
    have lone : Lift s b J (1) c0hrbL c0hrboneN c0hrboneD c0hrboneC :=
      ⟨by simp [c0hrboneN,c0hrboneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hrbonecof⟩
    have lvD : Lift s b J (50050/s^2) c0hrbL c0hrbvDN c0hrbvDD c0hrbvDC :=
      ⟨by simp [c0hrbvDN,c0hrbvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hrbvDcof⟩
    have hL : Ex.ev s b J c0hrbL≠0 := by
      have k := RegCert.auto_sound c0hrbLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (by simp [c0hrbvDD,Ex.ev,ev3,ev2,ev1]; positivity) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := zero_of_check c0hrbok hL (spotX_ev lX46.eq lX45.eq lvD.eq lY1.eq (lone.eq.trans (one_mul _)))
    have hs2 : (50050:ℝ)/s^2≠0 := by positivity
    field_simp at h ⊢; linarith
  · have lX29 : Lift s b J (X.getD 29 0) c0L1L c0L1X29N c0L1X29D c0L1X29C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : X.getD 29 0=((getRat xs 193 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 29]; rfl
        rw [e]; exact hr.1,c0L1X29cof⟩
    have lX44 : Lift s b J (X.getD 44 0) c0L1L c0L1X44N c0L1X44D c0L1X44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c0L1X44cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0L1L c0L1X46N c0L1X46D c0L1X46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0L1X46N,c0L1X46D,Ex.ev,ev3,ev2,ev1]
        ring,c0L1X46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0L1L c0L1Y1N c0L1Y1D c0L1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c0L1Y1N,c0L1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0L1Y1cof⟩
    have lY13 : Lift s b J (Y.getD 13 0) c0L1L c0L1Y13N c0L1Y13D c0L1Y13C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 13 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 13]; rfl
        rw [e]; exact hr.1,c0L1Y13cof⟩
    have lY37 : Lift s b J (Y.getD 37 0) c0L1L c0L1Y37N c0L1Y37D c0L1Y37C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 37 0=((getRat xs 579 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 37]; rfl
        rw [e]; exact hr.1,c0L1Y37cof⟩
    have hL : Ex.ev s b J c0L1L≠0 := by
      have k := RegCert.auto_sound c0L1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2
    have h := signed_sound B c0L1ok hL (detX_ev lX46.eq lY1.eq lX44.eq lY13.eq lX29.eq lY37.eq)
    push_cast at h; linarith
  · have lX30 : Lift s b J (X.getD 30 0) c0L2L c0L2X30N c0L2X30D c0L2X30C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 30 0=((getRat xs 250 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 30]; rfl
        rw [e]; exact hr.1,c0L2X30cof⟩
    have lX44 : Lift s b J (X.getD 44 0) c0L2L c0L2X44N c0L2X44D c0L2X44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c0L2X44cof⟩
    have lX45 : Lift s b J (X.getD 45 0) c0L2L c0L2X45N c0L2X45D c0L2X45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0L2X45N,c0L2X45D,Ex.ev,ev3,ev2,ev1]
        ring,c0L2X45cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0L2L c0L2Y1N c0L2Y1D c0L2Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c0L2Y1N,c0L2Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0L2Y1cof⟩
    have lY13 : Lift s b J (Y.getD 13 0) c0L2L c0L2Y13N c0L2Y13D c0L2Y13C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 13 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 13]; rfl
        rw [e]; exact hr.1,c0L2Y13cof⟩
    have lY37 : Lift s b J (Y.getD 37 0) c0L2L c0L2Y37N c0L2Y37D c0L2Y37C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 37 0=((getRat xs 579 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 37]; rfl
        rw [e]; exact hr.1,c0L2Y37cof⟩
    have hL : Ex.ev s b J c0L2L≠0 := by
      have k := RegCert.auto_sound c0L2Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c0L2ok hL (detX_ev lX45.eq lY1.eq lX44.eq lY13.eq lX30.eq lY37.eq)
    push_cast at h; linarith
  · have lY38 : Lift s b J (Y.getD 38 0) c0deepL c0deepY38N c0deepY38D c0deepY38C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 38 0=((getRat xs 229 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 38]; rfl
        rw [e]; exact hr.1,c0deepY38cof⟩
    have lone : Lift s b J (1) c0deepL c0deeponeN c0deeponeD c0deeponeC :=
      ⟨by simp [c0deeponeN,c0deeponeD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0deeponecof⟩
    have lvD : Lift s b J (50050/s^2) c0deepL c0deepvDN c0deepvDD c0deepvDC :=
      ⟨by simp [c0deepvDN,c0deepvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0deepvDcof⟩
    have hL : Ex.ev s b J c0deepL≠0 := by
      have k := RegCert.auto_sound c0deepLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (by simp [c0deepvDD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0deepok hL (linX_ev (one:=.mul c0deeponeN c0deeponeC) (lone.eq.trans (one_mul _)) _ [(1,50050/s^2),(-1,Y.getD 38 0),(1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lvD.eq⟩,⟨by trivial,lY38.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY37 : Lift s b J (Y.getD 37 0) c0H43L c0H43Y37N c0H43Y37D c0H43Y37C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 37 0=((getRat xs 579 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 37]; rfl
        rw [e]; exact hr.1,c0H43Y37cof⟩
    have lone : Lift s b J (1) c0H43L c0H43oneN c0H43oneD c0H43oneC :=
      ⟨by simp [c0H43oneN,c0H43oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0H43onecof⟩
    have hL : Ex.ev s b J c0H43L≠0 := by
      have k := RegCert.auto_sound c0H43Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2
    have h := signed_sound B c0H43ok hL (linX_ev (one:=.mul c0H43oneN c0H43oneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 37 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY37.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith

/-- Range conditions of the copy tests of channel 1. -/
theorem ranges1 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 3 ∧ getRat args 3≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((200:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    X.getD 44 0=(301:ℝ)/2 ∧
    Y.getD 13 0=(1:ℝ)/1 ∧
    X.getD 56 0=X.getD 55 0+3/2*(1-Y.getD 1 0)/(50050/s^2) ∧
    0<ArtGallery.det (X.getD 56 0,Y.getD 1 0) (X.getD 44 0,Y.getD 13 0) (X.getD 16 0,Y.getD 19 0) ∧
    ArtGallery.det (X.getD 55 0,Y.getD 1 0) (X.getD 44 0,Y.getD 13 0) (X.getD 17 0,Y.getD 19 0)<0 ∧
    0<(1:ℝ)*(50050/s^2)+(-1:ℝ)*(Y.getD 20 0)+(1:ℝ)*(1) ∧
    0<(3:ℝ)*(Y.getD 19 0)+(-7:ℝ)*(1) := by
  intro s J Q b X Y
  have Xdef : X=(grid template args false).map (fun q : ℚ => (q:ℝ)) := rfl
  have Ydef : Y=(grid template args true).map (fun q : ℚ => (q:ℝ)) := rfl
  have hs : (0:ℝ)<s := by simp only [s]; exact_mod_cast m.pos
  have hs1 : s≤(((1/65:ℚ):ℚ):ℝ) := by simp only [s]; exact_mod_cast m.upper
  have hJ' : (0:ℝ)≤J ∧ J≤1 := by simp only [J]; exact ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  have hQ' : (0:ℝ)≤Q ∧ Q≤1 := by simp only [Q]; exact ⟨by exact_mod_cast hQ.1,by exact_mod_cast hQ.2⟩
  have B : PolyBox.Box (1/65:ℚ) (999/5005:ℚ) (26379/130130:ℚ) s b J := by
    refine ⟨hs,hs1,?_,?_,hJ'.1,hJ'.2,by norm_num⟩
    · simp only [b]; push_cast; nlinarith
    · simp only [b]; push_cast at hs1 ⊢; nlinarith [mul_le_mul hJ'.2 hs1 hs.le zero_le_one]
  have hin : ∀ k P d, (k,P,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c1ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c1hold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have lX44 : Lift s b J (X.getD 44 0) c1hwxL c1hwxX44N c1hwxX44D c1hwxX44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c1hwxX44cof⟩
    have lone : Lift s b J (1) c1hwxL c1hwxoneN c1hwxoneD c1hwxoneC :=
      ⟨by simp [c1hwxoneN,c1hwxoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hwxonecof⟩
    have hL : Ex.ev s b J c1hwxL≠0 := by
      have k := RegCert.auto_sound c1hwxLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1hwxok hL (linX_ev (one:=.mul c1hwxoneN c1hwxoneC) (lone.eq.trans (one_mul _)) _ [(2,X.getD 44 0),(-301,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX44.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY13 : Lift s b J (Y.getD 13 0) c1hwyL c1hwyY13N c1hwyY13D c1hwyY13C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 13 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 13]; rfl
        rw [e]; exact hr.1,c1hwyY13cof⟩
    have lone : Lift s b J (1) c1hwyL c1hwyoneN c1hwyoneD c1hwyoneC :=
      ⟨by simp [c1hwyoneN,c1hwyoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hwyonecof⟩
    have hL : Ex.ev s b J c1hwyL≠0 := by
      have k := RegCert.auto_sound c1hwyLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1hwyok hL (linX_ev (one:=.mul c1hwyoneN c1hwyoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 13 0),(-1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY13.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX55 : Lift s b J (X.getD 55 0) c1hrbL c1hrbX55N c1hrbX55D c1hrbX55C :=
      ⟨by
        have e : X.getD 55 0=((((axisOf template false).coordsQ (getRat args 0)).getD 12 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 55]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1hrbX55N,c1hrbX55D,Ex.ev,ev3,ev2,ev1]
        ring,c1hrbX55cof⟩
    have lX56 : Lift s b J (X.getD 56 0) c1hrbL c1hrbX56N c1hrbX56D c1hrbX56C :=
      ⟨by
        have e : X.getD 56 0=((((axisOf template false).coordsQ (getRat args 0)).getD 13 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 56]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1hrbX56N,c1hrbX56D,Ex.ev,ev3,ev2,ev1]
        ring,c1hrbX56cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1hrbL c1hrbY1N c1hrbY1D c1hrbY1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c1hrbY1N,c1hrbY1D,Ex.ev,ev3,ev2,ev1]
        ring,c1hrbY1cof⟩
    have lone : Lift s b J (1) c1hrbL c1hrboneN c1hrboneD c1hrboneC :=
      ⟨by simp [c1hrboneN,c1hrboneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hrbonecof⟩
    have lvD : Lift s b J (50050/s^2) c1hrbL c1hrbvDN c1hrbvDD c1hrbvDC :=
      ⟨by simp [c1hrbvDN,c1hrbvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hrbvDcof⟩
    have hL : Ex.ev s b J c1hrbL≠0 := by
      have k := RegCert.auto_sound c1hrbLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (by simp [c1hrbvDD,Ex.ev,ev3,ev2,ev1]; positivity) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := zero_of_check c1hrbok hL (spotX_ev lX56.eq lX55.eq lvD.eq lY1.eq (lone.eq.trans (one_mul _)))
    have hs2 : (50050:ℝ)/s^2≠0 := by positivity
    field_simp at h ⊢; linarith
  · have lX16 : Lift s b J (X.getD 16 0) c1L1L c1L1X16N c1L1X16D c1L1X16C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 16 0=((getRat xs 144 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 16]; rfl
        rw [e]; exact hr.1,c1L1X16cof⟩
    have lX44 : Lift s b J (X.getD 44 0) c1L1L c1L1X44N c1L1X44D c1L1X44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c1L1X44cof⟩
    have lX56 : Lift s b J (X.getD 56 0) c1L1L c1L1X56N c1L1X56D c1L1X56C :=
      ⟨by
        have e : X.getD 56 0=((((axisOf template false).coordsQ (getRat args 0)).getD 13 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 56]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1L1X56N,c1L1X56D,Ex.ev,ev3,ev2,ev1]
        ring,c1L1X56cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1L1L c1L1Y1N c1L1Y1D c1L1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c1L1Y1N,c1L1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1L1Y1cof⟩
    have lY13 : Lift s b J (Y.getD 13 0) c1L1L c1L1Y13N c1L1Y13D c1L1Y13C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 13 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 13]; rfl
        rw [e]; exact hr.1,c1L1Y13cof⟩
    have lY19 : Lift s b J (Y.getD 19 0) c1L1L c1L1Y19N c1L1Y19D c1L1Y19C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 19 0=((getRat xs 368 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 19]; rfl
        rw [e]; exact hr.1,c1L1Y19cof⟩
    have hL : Ex.ev s b J c1L1L≠0 := by
      have k := RegCert.auto_sound c1L1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1L1ok hL (detX_ev lX56.eq lY1.eq lX44.eq lY13.eq lX16.eq lY19.eq)
    push_cast at h; linarith
  · have lX17 : Lift s b J (X.getD 17 0) c1L2L c1L2X17N c1L2X17D c1L2X17C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : X.getD 17 0=((getRat xs 43 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 17]; rfl
        rw [e]; exact hr.1,c1L2X17cof⟩
    have lX44 : Lift s b J (X.getD 44 0) c1L2L c1L2X44N c1L2X44D c1L2X44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c1L2X44cof⟩
    have lX55 : Lift s b J (X.getD 55 0) c1L2L c1L2X55N c1L2X55D c1L2X55C :=
      ⟨by
        have e : X.getD 55 0=((((axisOf template false).coordsQ (getRat args 0)).getD 12 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 55]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1L2X55N,c1L2X55D,Ex.ev,ev3,ev2,ev1]
        ring,c1L2X55cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1L2L c1L2Y1N c1L2Y1D c1L2Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c1L2Y1N,c1L2Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1L2Y1cof⟩
    have lY13 : Lift s b J (Y.getD 13 0) c1L2L c1L2Y13N c1L2Y13D c1L2Y13C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 13 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 13]; rfl
        rw [e]; exact hr.1,c1L2Y13cof⟩
    have lY19 : Lift s b J (Y.getD 19 0) c1L2L c1L2Y19N c1L2Y19D c1L2Y19C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 19 0=((getRat xs 368 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 19]; rfl
        rw [e]; exact hr.1,c1L2Y19cof⟩
    have hL : Ex.ev s b J c1L2L≠0 := by
      have k := RegCert.auto_sound c1L2Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1L2ok hL (detX_ev lX55.eq lY1.eq lX44.eq lY13.eq lX17.eq lY19.eq)
    push_cast at h; linarith
  · have lY20 : Lift s b J (Y.getD 20 0) c1deepL c1deepY20N c1deepY20D c1deepY20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 20 0=((getRat xs 173 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1deepY20cof⟩
    have lone : Lift s b J (1) c1deepL c1deeponeN c1deeponeD c1deeponeC :=
      ⟨by simp [c1deeponeN,c1deeponeD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1deeponecof⟩
    have lvD : Lift s b J (50050/s^2) c1deepL c1deepvDN c1deepvDD c1deepvDC :=
      ⟨by simp [c1deepvDN,c1deepvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1deepvDcof⟩
    have hL : Ex.ev s b J c1deepL≠0 := by
      have k := RegCert.auto_sound c1deepLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (by simp [c1deepvDD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1deepok hL (linX_ev (one:=.mul c1deeponeN c1deeponeC) (lone.eq.trans (one_mul _)) _ [(1,50050/s^2),(-1,Y.getD 20 0),(1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lvD.eq⟩,⟨by trivial,lY20.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY19 : Lift s b J (Y.getD 19 0) c1H43L c1H43Y19N c1H43Y19D c1H43Y19C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 19 0=((getRat xs 368 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 19]; rfl
        rw [e]; exact hr.1,c1H43Y19cof⟩
    have lone : Lift s b J (1) c1H43L c1H43oneN c1H43oneD c1H43oneC :=
      ⟨by simp [c1H43oneN,c1H43oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1H43onecof⟩
    have hL : Ex.ev s b J c1H43L≠0 := by
      have k := RegCert.auto_sound c1H43Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2
    have h := signed_sound B c1H43ok hL (linX_ev (one:=.mul c1H43oneN c1H43oneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 19 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY19.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_200
end
