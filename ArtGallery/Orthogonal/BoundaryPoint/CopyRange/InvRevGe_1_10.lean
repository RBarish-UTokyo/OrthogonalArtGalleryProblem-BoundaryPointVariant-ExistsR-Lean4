module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0Hold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0I0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0I1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0I2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C0I3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1Hold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1I0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10.C1I1

/-! Range conditions of the copy tests of profile `InvRevGe_1_10` (generated): closed forms through
branch rows (`RegChain`), lifts to a common denominator, signs on the parameter box. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvRevGe_1_10
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
    Y.getD 12 0=(1:ℝ)/1 ∧
    0<ArtGallery.det (X.getD 45 0,Y.getD 1 0) (X.getD 28 0,Y.getD 38 0) (X.getD 24 0,Y.getD 42 0) ∧
    0<ArtGallery.det (X.getD 46 0,Y.getD 1 0) (X.getD 28 0,Y.getD 38 0) (X.getD 24 0,Y.getD 42 0) ∧
    ArtGallery.det (X.getD 45 0,Y.getD 1 0) (X.getD 28 0,Y.getD 38 0) (X.getD 25 0,Y.getD 42 0)<0 ∧
    ArtGallery.det (X.getD 46 0,Y.getD 1 0) (X.getD 28 0,Y.getD 38 0) (X.getD 25 0,Y.getD 42 0)<0 ∧
    0<(1:ℝ)*(Y.getD 39 0)+(-1:ℝ)*(1-50050/s^2) ∧
    0<(3:ℝ)*(Y.getD 41 0)+(-7:ℝ)*(1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 25 0,Y.getD 39 0) (0,1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 25 0,Y.getD 39 0) (0,1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 25 0,Y.getD 39 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 25 0,Y.getD 39 0) (s/320,1)<0 ∧
    X.getD 32 0=(0:ℝ)/1 ∧
    X.getD 33 0=s/320 := by
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
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lY12 : Lift s b J (Y.getD 12 0) c0hwyL c0hwyY12N c0hwyY12D c0hwyY12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 12 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 12]; rfl
        rw [e]; exact hr.1,c0hwyY12cof⟩
    have lone : Lift s b J (1) c0hwyL c0hwyoneN c0hwyoneD c0hwyoneC :=
      ⟨by simp [c0hwyoneN,c0hwyoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hwyonecof⟩
    have hL : Ex.ev s b J c0hwyL≠0 := by
      have k := RegCert.auto_sound c0hwyLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hwyok hL (linX_ev (one:=.mul c0hwyoneN c0hwyoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 12 0),(-1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY12.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX24 : Lift s b J (X.getD 24 0) c0Ua0L c0Ua0X24N c0Ua0X24D c0Ua0X24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
        have e : X.getD 24 0=((getRat xs 94 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 24]; rfl
        rw [e]; exact hr.1,c0Ua0X24cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0Ua0L c0Ua0X28N c0Ua0X28D c0Ua0X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 28 0=((getRat xs 316 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0Ua0X28cof⟩
    have lX45 : Lift s b J (X.getD 45 0) c0Ua0L c0Ua0X45N c0Ua0X45D c0Ua0X45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0Ua0X45N,c0Ua0X45D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua0X45cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0Ua0L c0Ua0Y1N c0Ua0Y1D c0Ua0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c0Ua0Y1N,c0Ua0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua0Y1cof⟩
    have lY38 : Lift s b J (Y.getD 38 0) c0Ua0L c0Ua0Y38N c0Ua0Y38D c0Ua0Y38C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 38 0=((getRat xs 579 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 38]; rfl
        rw [e]; exact hr.1,c0Ua0Y38cof⟩
    have lY42 : Lift s b J (Y.getD 42 0) c0Ua0L c0Ua0Y42N c0Ua0Y42D c0Ua0Y42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 42 0=((getRat xs 576 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 42]; rfl
        rw [e]; exact hr.1,c0Ua0Y42cof⟩
    have hL : Ex.ev s b J c0Ua0L≠0 := by
      have k := RegCert.auto_sound c0Ua0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c0Ua0ok hL (detX_ev lX45.eq lY1.eq lX28.eq lY38.eq lX24.eq lY42.eq)
    push_cast at h; linarith
  · have lX24 : Lift s b J (X.getD 24 0) c0Ua1L c0Ua1X24N c0Ua1X24D c0Ua1X24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
        have e : X.getD 24 0=((getRat xs 94 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 24]; rfl
        rw [e]; exact hr.1,c0Ua1X24cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0Ua1L c0Ua1X28N c0Ua1X28D c0Ua1X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 28 0=((getRat xs 316 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0Ua1X28cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0Ua1L c0Ua1X46N c0Ua1X46D c0Ua1X46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0Ua1X46N,c0Ua1X46D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua1X46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0Ua1L c0Ua1Y1N c0Ua1Y1D c0Ua1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c0Ua1Y1N,c0Ua1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua1Y1cof⟩
    have lY38 : Lift s b J (Y.getD 38 0) c0Ua1L c0Ua1Y38N c0Ua1Y38D c0Ua1Y38C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 38 0=((getRat xs 579 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 38]; rfl
        rw [e]; exact hr.1,c0Ua1Y38cof⟩
    have lY42 : Lift s b J (Y.getD 42 0) c0Ua1L c0Ua1Y42N c0Ua1Y42D c0Ua1Y42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 42 0=((getRat xs 576 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 42]; rfl
        rw [e]; exact hr.1,c0Ua1Y42cof⟩
    have hL : Ex.ev s b J c0Ua1L≠0 := by
      have k := RegCert.auto_sound c0Ua1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c0Ua1ok hL (detX_ev lX46.eq lY1.eq lX28.eq lY38.eq lX24.eq lY42.eq)
    push_cast at h; linarith
  · have lX25 : Lift s b J (X.getD 25 0) c0Ub0L c0Ub0X25N c0Ub0X25D c0Ub0X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 25 0=((getRat xs 581 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0Ub0X25cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0Ub0L c0Ub0X28N c0Ub0X28D c0Ub0X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 28 0=((getRat xs 316 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0Ub0X28cof⟩
    have lX45 : Lift s b J (X.getD 45 0) c0Ub0L c0Ub0X45N c0Ub0X45D c0Ub0X45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0Ub0X45N,c0Ub0X45D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub0X45cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0Ub0L c0Ub0Y1N c0Ub0Y1D c0Ub0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c0Ub0Y1N,c0Ub0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub0Y1cof⟩
    have lY38 : Lift s b J (Y.getD 38 0) c0Ub0L c0Ub0Y38N c0Ub0Y38D c0Ub0Y38C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 38 0=((getRat xs 579 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 38]; rfl
        rw [e]; exact hr.1,c0Ub0Y38cof⟩
    have lY42 : Lift s b J (Y.getD 42 0) c0Ub0L c0Ub0Y42N c0Ub0Y42D c0Ub0Y42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 42 0=((getRat xs 576 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 42]; rfl
        rw [e]; exact hr.1,c0Ub0Y42cof⟩
    have hL : Ex.ev s b J c0Ub0L≠0 := by
      have k := RegCert.auto_sound c0Ub0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c0Ub0ok hL (detX_ev lX45.eq lY1.eq lX28.eq lY38.eq lX25.eq lY42.eq)
    push_cast at h; linarith
  · have lX25 : Lift s b J (X.getD 25 0) c0Ub1L c0Ub1X25N c0Ub1X25D c0Ub1X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 25 0=((getRat xs 581 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0Ub1X25cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0Ub1L c0Ub1X28N c0Ub1X28D c0Ub1X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 28 0=((getRat xs 316 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0Ub1X28cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0Ub1L c0Ub1X46N c0Ub1X46D c0Ub1X46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c0Ub1X46N,c0Ub1X46D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub1X46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0Ub1L c0Ub1Y1N c0Ub1Y1D c0Ub1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c0Ub1Y1N,c0Ub1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub1Y1cof⟩
    have lY38 : Lift s b J (Y.getD 38 0) c0Ub1L c0Ub1Y38N c0Ub1Y38D c0Ub1Y38C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 38 0=((getRat xs 579 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 38]; rfl
        rw [e]; exact hr.1,c0Ub1Y38cof⟩
    have lY42 : Lift s b J (Y.getD 42 0) c0Ub1L c0Ub1Y42N c0Ub1Y42D c0Ub1Y42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 42 0=((getRat xs 576 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 42]; rfl
        rw [e]; exact hr.1,c0Ub1Y42cof⟩
    have hL : Ex.ev s b J c0Ub1L≠0 := by
      have k := RegCert.auto_sound c0Ub1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c0Ub1ok hL (detX_ev lX46.eq lY1.eq lX28.eq lY38.eq lX25.eq lY42.eq)
    push_cast at h; linarith
  · have lBy : Lift s b J (1-50050/s^2) c0bLowL c0bLowByN c0bLowByD c0bLowByC :=
      ⟨by simp [c0bLowByN,c0bLowByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0bLowBycof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0bLowL c0bLowY39N c0bLowY39D c0bLowY39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 39 0=((getRat xs 352 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0bLowY39cof⟩
    have lone : Lift s b J (1) c0bLowL c0bLowoneN c0bLowoneD c0bLowoneC :=
      ⟨by simp [c0bLowoneN,c0bLowoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0bLowonecof⟩
    have hL : Ex.ev s b J c0bLowL≠0 := by
      have k := RegCert.auto_sound c0bLowLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (by simp [c0bLowByD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0bLowok hL (linX_ev (one:=.mul c0bLowoneN c0bLowoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 39 0),(-1,1-50050/s^2)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY39.eq⟩,⟨by trivial,lBy.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY41 : Lift s b J (Y.getD 41 0) c0H43uL c0H43uY41N c0H43uY41D c0H43uY41C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : Y.getD 41 0=((getRat xs 310 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 41]; rfl
        rw [e]; exact hr.1,c0H43uY41cof⟩
    have lone : Lift s b J (1) c0H43uL c0H43uoneN c0H43uoneD c0H43uoneC :=
      ⟨by simp [c0H43uoneN,c0H43uoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0H43uonecof⟩
    have hL : Ex.ev s b J c0H43uL≠0 := by
      have k := RegCert.auto_sound c0H43uLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))).2
    have h := signed_sound B c0H43uok hL (linX_ev (one:=.mul c0H43uoneN c0H43uoneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 41 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY41.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0DL0L c0DL0BxN c0DL0BxD c0DL0BxC :=
      ⟨by simp [c0DL0BxN,c0DL0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DL0L c0DL0ByN c0DL0ByD c0DL0ByC :=
      ⟨by simp [c0DL0ByN,c0DL0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0Bycof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0DL0L c0DL0X25N c0DL0X25D c0DL0X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 25 0=((getRat xs 581 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0DL0X25cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0DL0L c0DL0Y39N c0DL0Y39D c0DL0Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 39 0=((getRat xs 352 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0DL0Y39cof⟩
    have lone : Lift s b J (1) c0DL0L c0DL0oneN c0DL0oneD c0DL0oneC :=
      ⟨by simp [c0DL0oneN,c0DL0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0onecof⟩
    have lzero : Lift s b J (0) c0DL0L c0DL0zeroN c0DL0zeroD c0DL0zeroC :=
      ⟨by simp [c0DL0zeroN,c0DL0zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0zerocof⟩
    have hL : Ex.ev s b J c0DL0L≠0 := by
      have k := RegCert.auto_sound c0DL0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DL0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DL0ok hL (detX_ev lBx.eq lBy.eq lX25.eq lY39.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0DL1L c0DL1Bx15N c0DL1Bx15D c0DL1Bx15C :=
      ⟨by simp [c0DL1Bx15N,c0DL1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DL1L c0DL1ByN c0DL1ByD c0DL1ByC :=
      ⟨by simp [c0DL1ByN,c0DL1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1Bycof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0DL1L c0DL1X25N c0DL1X25D c0DL1X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 25 0=((getRat xs 581 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0DL1X25cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0DL1L c0DL1Y39N c0DL1Y39D c0DL1Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 39 0=((getRat xs 352 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0DL1Y39cof⟩
    have lone : Lift s b J (1) c0DL1L c0DL1oneN c0DL1oneD c0DL1oneC :=
      ⟨by simp [c0DL1oneN,c0DL1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1onecof⟩
    have lzero : Lift s b J (0) c0DL1L c0DL1zeroN c0DL1zeroD c0DL1zeroC :=
      ⟨by simp [c0DL1zeroN,c0DL1zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1zerocof⟩
    have hL : Ex.ev s b J c0DL1L≠0 := by
      have k := RegCert.auto_sound c0DL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DL1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DL1ok hL (detX_ev lBx15.eq lBy.eq lX25.eq lY39.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0DR0L c0DR0BxN c0DR0BxD c0DR0BxC :=
      ⟨by simp [c0DR0BxN,c0DR0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DR0L c0DR0ByN c0DR0ByD c0DR0ByC :=
      ⟨by simp [c0DR0ByN,c0DR0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0Bycof⟩
    have lWq : Lift s b J (s/320) c0DR0L c0DR0WqN c0DR0WqD c0DR0WqC :=
      ⟨by simp [c0DR0WqN,c0DR0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0Wqcof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0DR0L c0DR0X25N c0DR0X25D c0DR0X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 25 0=((getRat xs 581 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0DR0X25cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0DR0L c0DR0Y39N c0DR0Y39D c0DR0Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 39 0=((getRat xs 352 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0DR0Y39cof⟩
    have lone : Lift s b J (1) c0DR0L c0DR0oneN c0DR0oneD c0DR0oneC :=
      ⟨by simp [c0DR0oneN,c0DR0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0onecof⟩
    have hL : Ex.ev s b J c0DR0L≠0 := by
      have k := RegCert.auto_sound c0DR0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DR0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DR0ok hL (detX_ev lBx.eq lBy.eq lX25.eq lY39.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0DR1L c0DR1Bx15N c0DR1Bx15D c0DR1Bx15C :=
      ⟨by simp [c0DR1Bx15N,c0DR1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DR1L c0DR1ByN c0DR1ByD c0DR1ByC :=
      ⟨by simp [c0DR1ByN,c0DR1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1Bycof⟩
    have lWq : Lift s b J (s/320) c0DR1L c0DR1WqN c0DR1WqD c0DR1WqC :=
      ⟨by simp [c0DR1WqN,c0DR1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1Wqcof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0DR1L c0DR1X25N c0DR1X25D c0DR1X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 25 0=((getRat xs 581 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0DR1X25cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0DR1L c0DR1Y39N c0DR1Y39D c0DR1Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 39 0=((getRat xs 352 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0DR1Y39cof⟩
    have lone : Lift s b J (1) c0DR1L c0DR1oneN c0DR1oneD c0DR1oneC :=
      ⟨by simp [c0DR1oneN,c0DR1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1onecof⟩
    have hL : Ex.ev s b J c0DR1L≠0 := by
      have k := RegCert.auto_sound c0DR1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DR1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DR1ok hL (detX_ev lBx15.eq lBy.eq lX25.eq lY39.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lX32 : Lift s b J (X.getD 32 0) c0hdlL c0hdlX32N c0hdlX32D c0hdlX32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 32 0=((getRat xs 684 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 32]; rfl
        rw [e]; exact hr.1,c0hdlX32cof⟩
    have lone : Lift s b J (1) c0hdlL c0hdloneN c0hdloneD c0hdloneC :=
      ⟨by simp [c0hdloneN,c0hdloneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hdlonecof⟩
    have hL : Ex.ev s b J c0hdlL≠0 := by
      have k := RegCert.auto_sound c0hdlLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hdlok hL (linX_ev (one:=.mul c0hdloneN c0hdloneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 32 0),(0,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX32.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lWq : Lift s b J (s/320) c0hdrL c0hdrWqN c0hdrWqD c0hdrWqC :=
      ⟨by simp [c0hdrWqN,c0hdrWqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hdrWqcof⟩
    have lX33 : Lift s b J (X.getD 33 0) c0hdrL c0hdrX33N c0hdrX33D c0hdrX33C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 33 0=((getRat xs 830 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 33]; rfl
        rw [e]; exact hr.1,c0hdrX33cof⟩
    have lone : Lift s b J (1) c0hdrL c0hdroneN c0hdroneD c0hdroneC :=
      ⟨by simp [c0hdroneN,c0hdroneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hdronecof⟩
    have hL : Ex.ev s b J c0hdrL≠0 := by
      have k := RegCert.auto_sound c0hdrLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hdrok hL (linX_ev (one:=.mul c0hdroneN c0hdroneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 33 0),(-1,s/320)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX33.eq⟩,⟨by trivial,lWq.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith

/-- Range conditions of the copy tests of channel 1. -/
theorem ranges1 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 3 ∧ getRat args 3≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((10:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    X.getD 44 0=(301:ℝ)/2 ∧
    Y.getD 12 0=(1:ℝ)/1 ∧
    X.getD 52 0=X.getD 51 0+3/2*(1-Y.getD 1 0)/(50050/s^2) ∧
    0<ArtGallery.det (X.getD 52 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 16 0,Y.getD 18 0) ∧
    ArtGallery.det (X.getD 51 0,Y.getD 1 0) (X.getD 44 0,Y.getD 12 0) (X.getD 17 0,Y.getD 18 0)<0 ∧
    0<(1:ℝ)*(50050/s^2)+(-1:ℝ)*(Y.getD 19 0)+(1:ℝ)*(1) ∧
    0<(3:ℝ)*(Y.getD 18 0)+(-7:ℝ)*(1) := by
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
  · have lY12 : Lift s b J (Y.getD 12 0) c1hwyL c1hwyY12N c1hwyY12D c1hwyY12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 12 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 12]; rfl
        rw [e]; exact hr.1,c1hwyY12cof⟩
    have lone : Lift s b J (1) c1hwyL c1hwyoneN c1hwyoneD c1hwyoneC :=
      ⟨by simp [c1hwyoneN,c1hwyoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hwyonecof⟩
    have hL : Ex.ev s b J c1hwyL≠0 := by
      have k := RegCert.auto_sound c1hwyLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1hwyok hL (linX_ev (one:=.mul c1hwyoneN c1hwyoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 12 0),(-1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY12.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX51 : Lift s b J (X.getD 51 0) c1hrbL c1hrbX51N c1hrbX51D c1hrbX51C :=
      ⟨by
        have e : X.getD 51 0=((((axisOf template false).coordsQ (getRat args 0)).getD 8 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 51]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1hrbX51N,c1hrbX51D,Ex.ev,ev3,ev2,ev1]
        ring,c1hrbX51cof⟩
    have lX52 : Lift s b J (X.getD 52 0) c1hrbL c1hrbX52N c1hrbX52D c1hrbX52C :=
      ⟨by
        have e : X.getD 52 0=((((axisOf template false).coordsQ (getRat args 0)).getD 9 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 52]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1hrbX52N,c1hrbX52D,Ex.ev,ev3,ev2,ev1]
        ring,c1hrbX52cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1hrbL c1hrbY1N c1hrbY1D c1hrbY1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c1hrbY1N,c1hrbY1D,Ex.ev,ev3,ev2,ev1]
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
    have h := zero_of_check c1hrbok hL (spotX_ev lX52.eq lX51.eq lvD.eq lY1.eq (lone.eq.trans (one_mul _)))
    have hs2 : (50050:ℝ)/s^2≠0 := by positivity
    field_simp at h ⊢; linarith
  · have lX16 : Lift s b J (X.getD 16 0) c1L1L c1L1X16N c1L1X16D c1L1X16C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 16 0=((getRat xs 145 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 16]; rfl
        rw [e]; exact hr.1,c1L1X16cof⟩
    have lX44 : Lift s b J (X.getD 44 0) c1L1L c1L1X44N c1L1X44D c1L1X44C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 44 0=((getRat xs 826 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 44]; rfl
        rw [e]; exact hr.1,c1L1X44cof⟩
    have lX52 : Lift s b J (X.getD 52 0) c1L1L c1L1X52N c1L1X52D c1L1X52C :=
      ⟨by
        have e : X.getD 52 0=((((axisOf template false).coordsQ (getRat args 0)).getD 9 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 52]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1L1X52N,c1L1X52D,Ex.ev,ev3,ev2,ev1]
        ring,c1L1X52cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1L1L c1L1Y1N c1L1Y1D c1L1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c1L1Y1N,c1L1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1L1Y1cof⟩
    have lY12 : Lift s b J (Y.getD 12 0) c1L1L c1L1Y12N c1L1Y12D c1L1Y12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 12 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 12]; rfl
        rw [e]; exact hr.1,c1L1Y12cof⟩
    have lY18 : Lift s b J (Y.getD 18 0) c1L1L c1L1Y18N c1L1Y18D c1L1Y18C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 18 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 18]; rfl
        rw [e]; exact hr.1,c1L1Y18cof⟩
    have hL : Ex.ev s b J c1L1L≠0 := by
      have k := RegCert.auto_sound c1L1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1L1ok hL (detX_ev lX52.eq lY1.eq lX44.eq lY12.eq lX16.eq lY18.eq)
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
    have lX51 : Lift s b J (X.getD 51 0) c1L2L c1L2X51N c1L2X51D c1L2X51C :=
      ⟨by
        have e : X.getD 51 0=((((axisOf template false).coordsQ (getRat args 0)).getD 8 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 51]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.xAxis,Gap.valR,evalR,c1L2X51N,c1L2X51D,Ex.ev,ev3,ev2,ev1]
        ring,c1L2X51cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1L2L c1L2Y1N c1L2Y1D c1L2Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvRevGe.yAxis,Gap.valR,evalR,c1L2Y1N,c1L2Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1L2Y1cof⟩
    have lY12 : Lift s b J (Y.getD 12 0) c1L2L c1L2Y12N c1L2Y12D c1L2Y12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 12 0=((getRat xs 812 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 12]; rfl
        rw [e]; exact hr.1,c1L2Y12cof⟩
    have lY18 : Lift s b J (Y.getD 18 0) c1L2L c1L2Y18N c1L2Y18D c1L2Y18C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 18 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 18]; rfl
        rw [e]; exact hr.1,c1L2Y18cof⟩
    have hL : Ex.ev s b J c1L2L≠0 := by
      have k := RegCert.auto_sound c1L2Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1L2ok hL (detX_ev lX51.eq lY1.eq lX44.eq lY12.eq lX17.eq lY18.eq)
    push_cast at h; linarith
  · have lY19 : Lift s b J (Y.getD 19 0) c1deepL c1deepY19N c1deepY19D c1deepY19C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 19 0=((getRat xs 174 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 19]; rfl
        rw [e]; exact hr.1,c1deepY19cof⟩
    have lone : Lift s b J (1) c1deepL c1deeponeN c1deeponeD c1deeponeC :=
      ⟨by simp [c1deeponeN,c1deeponeD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1deeponecof⟩
    have lvD : Lift s b J (50050/s^2) c1deepL c1deepvDN c1deepvDD c1deepvDC :=
      ⟨by simp [c1deepvDN,c1deepvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1deepvDcof⟩
    have hL : Ex.ev s b J c1deepL≠0 := by
      have k := RegCert.auto_sound c1deepLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (by simp [c1deepvDD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1deepok hL (linX_ev (one:=.mul c1deeponeN c1deeponeC) (lone.eq.trans (one_mul _)) _ [(1,50050/s^2),(-1,Y.getD 19 0),(1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lvD.eq⟩,⟨by trivial,lY19.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY18 : Lift s b J (Y.getD 18 0) c1H43L c1H43Y18N c1H43Y18D c1H43Y18C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 18 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 18]; rfl
        rw [e]; exact hr.1,c1H43Y18cof⟩
    have lone : Lift s b J (1) c1H43L c1H43oneN c1H43oneD c1H43oneC :=
      ⟨by simp [c1H43oneN,c1H43oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1H43onecof⟩
    have hL : Ex.ev s b J c1H43L≠0 := by
      have k := RegCert.auto_sound c1H43Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2
    have h := signed_sound B c1H43ok hL (linX_ev (one:=.mul c1H43oneN c1H43oneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 18 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY18.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvRevGe_1_10
end
