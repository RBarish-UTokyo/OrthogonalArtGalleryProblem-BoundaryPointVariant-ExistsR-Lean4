module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0Hold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0I0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0I1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0I2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C0I3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1Hold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1I0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1I1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1I2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C1I3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2S6
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2Hold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2I0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000.C2I1

/-! Range conditions of the copy tests of profile `Lower_10_40_1000` (generated): closed forms through
branch rows (`RegChain`), lifts to a common denominator, signs on the parameter box. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Lower_10_40_1000
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
    let b : ℝ := ((((10:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    Y.getD 20 0=(1:ℝ)/1 ∧
    0<ArtGallery.det (X.getD 63 0,Y.getD 6 0) (X.getD 46 0,Y.getD 67 0) (X.getD 42 0,Y.getD 71 0) ∧
    0<ArtGallery.det (X.getD 64 0,Y.getD 6 0) (X.getD 46 0,Y.getD 67 0) (X.getD 42 0,Y.getD 71 0) ∧
    ArtGallery.det (X.getD 63 0,Y.getD 6 0) (X.getD 46 0,Y.getD 67 0) (X.getD 43 0,Y.getD 71 0)<0 ∧
    ArtGallery.det (X.getD 64 0,Y.getD 6 0) (X.getD 46 0,Y.getD 67 0) (X.getD 43 0,Y.getD 71 0)<0 ∧
    0<(1:ℝ)*(Y.getD 68 0)+(-1:ℝ)*(1-50050/s^2) ∧
    0<(3:ℝ)*(Y.getD 70 0)+(-7:ℝ)*(1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 43 0,Y.getD 68 0) (0,1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 43 0,Y.getD 68 0) (0,1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 43 0,Y.getD 68 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 43 0,Y.getD 68 0) (s/320,1)<0 ∧
    X.getD 50 0=(0:ℝ)/1 ∧
    X.getD 51 0=s/320 := by
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
  have hin : ∀ k P d, (k,P,d)∈c0ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c0ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c0hold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lY20 : Lift s b J (Y.getD 20 0) c0hwyL c0hwyY20N c0hwyY20D c0hwyY20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1197 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c0hwyY20cof⟩
    have lone : Lift s b J (1) c0hwyL c0hwyoneN c0hwyoneD c0hwyoneC :=
      ⟨by simp [c0hwyoneN,c0hwyoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hwyonecof⟩
    have hL : Ex.ev s b J c0hwyL≠0 := by
      have k := RegCert.auto_sound c0hwyLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hwyok hL (linX_ev (one:=.mul c0hwyoneN c0hwyoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 20 0),(-1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY20.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX42 : Lift s b J (X.getD 42 0) c0Ua0L c0Ua0X42N c0Ua0X42D c0Ua0X42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
        have e : X.getD 42 0=((getRat xs 148 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 42]; rfl
        rw [e]; exact hr.1,c0Ua0X42cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0Ua0L c0Ua0X46N c0Ua0X46D c0Ua0X46C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 46 0=((getRat xs 455 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e]; exact hr.1,c0Ua0X46cof⟩
    have lX63 : Lift s b J (X.getD 63 0) c0Ua0L c0Ua0X63N c0Ua0X63D c0Ua0X63C :=
      ⟨by
        have e : X.getD 63 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 63]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c0Ua0X63N,c0Ua0X63D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua0X63cof⟩
    have lY6 : Lift s b J (Y.getD 6 0) c0Ua0L c0Ua0Y6N c0Ua0Y6D c0Ua0Y6C :=
      ⟨by
        have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 6]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c0Ua0Y6N,c0Ua0Y6D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua0Y6cof⟩
    have lY67 : Lift s b J (Y.getD 67 0) c0Ua0L c0Ua0Y67N c0Ua0Y67D c0Ua0Y67C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 67 0=((getRat xs 967 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 67]; rfl
        rw [e]; exact hr.1,c0Ua0Y67cof⟩
    have lY71 : Lift s b J (Y.getD 71 0) c0Ua0L c0Ua0Y71N c0Ua0Y71D c0Ua0Y71C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 71 0=((getRat xs 964 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 71]; rfl
        rw [e]; exact hr.1,c0Ua0Y71cof⟩
    have hL : Ex.ev s b J c0Ua0L≠0 := by
      have k := RegCert.auto_sound c0Ua0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c0Ua0ok hL (detX_ev lX63.eq lY6.eq lX46.eq lY67.eq lX42.eq lY71.eq)
    push_cast at h; linarith
  · have lX42 : Lift s b J (X.getD 42 0) c0Ua1L c0Ua1X42N c0Ua1X42D c0Ua1X42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
        have e : X.getD 42 0=((getRat xs 148 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 42]; rfl
        rw [e]; exact hr.1,c0Ua1X42cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0Ua1L c0Ua1X46N c0Ua1X46D c0Ua1X46C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 46 0=((getRat xs 455 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e]; exact hr.1,c0Ua1X46cof⟩
    have lX64 : Lift s b J (X.getD 64 0) c0Ua1L c0Ua1X64N c0Ua1X64D c0Ua1X64C :=
      ⟨by
        have e : X.getD 64 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 64]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c0Ua1X64N,c0Ua1X64D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua1X64cof⟩
    have lY6 : Lift s b J (Y.getD 6 0) c0Ua1L c0Ua1Y6N c0Ua1Y6D c0Ua1Y6C :=
      ⟨by
        have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 6]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c0Ua1Y6N,c0Ua1Y6D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ua1Y6cof⟩
    have lY67 : Lift s b J (Y.getD 67 0) c0Ua1L c0Ua1Y67N c0Ua1Y67D c0Ua1Y67C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 67 0=((getRat xs 967 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 67]; rfl
        rw [e]; exact hr.1,c0Ua1Y67cof⟩
    have lY71 : Lift s b J (Y.getD 71 0) c0Ua1L c0Ua1Y71N c0Ua1Y71D c0Ua1Y71C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 71 0=((getRat xs 964 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 71]; rfl
        rw [e]; exact hr.1,c0Ua1Y71cof⟩
    have hL : Ex.ev s b J c0Ua1L≠0 := by
      have k := RegCert.auto_sound c0Ua1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c0Ua1ok hL (detX_ev lX64.eq lY6.eq lX46.eq lY67.eq lX42.eq lY71.eq)
    push_cast at h; linarith
  · have lX43 : Lift s b J (X.getD 43 0) c0Ub0L c0Ub0X43N c0Ub0X43D c0Ub0X43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 43 0=((getRat xs 969 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 43]; rfl
        rw [e]; exact hr.1,c0Ub0X43cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0Ub0L c0Ub0X46N c0Ub0X46D c0Ub0X46C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 46 0=((getRat xs 455 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e]; exact hr.1,c0Ub0X46cof⟩
    have lX63 : Lift s b J (X.getD 63 0) c0Ub0L c0Ub0X63N c0Ub0X63D c0Ub0X63C :=
      ⟨by
        have e : X.getD 63 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 63]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c0Ub0X63N,c0Ub0X63D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub0X63cof⟩
    have lY6 : Lift s b J (Y.getD 6 0) c0Ub0L c0Ub0Y6N c0Ub0Y6D c0Ub0Y6C :=
      ⟨by
        have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 6]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c0Ub0Y6N,c0Ub0Y6D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub0Y6cof⟩
    have lY67 : Lift s b J (Y.getD 67 0) c0Ub0L c0Ub0Y67N c0Ub0Y67D c0Ub0Y67C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 67 0=((getRat xs 967 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 67]; rfl
        rw [e]; exact hr.1,c0Ub0Y67cof⟩
    have lY71 : Lift s b J (Y.getD 71 0) c0Ub0L c0Ub0Y71N c0Ub0Y71D c0Ub0Y71C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 71 0=((getRat xs 964 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 71]; rfl
        rw [e]; exact hr.1,c0Ub0Y71cof⟩
    have hL : Ex.ev s b J c0Ub0L≠0 := by
      have k := RegCert.auto_sound c0Ub0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c0Ub0ok hL (detX_ev lX63.eq lY6.eq lX46.eq lY67.eq lX43.eq lY71.eq)
    push_cast at h; linarith
  · have lX43 : Lift s b J (X.getD 43 0) c0Ub1L c0Ub1X43N c0Ub1X43D c0Ub1X43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 43 0=((getRat xs 969 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 43]; rfl
        rw [e]; exact hr.1,c0Ub1X43cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0Ub1L c0Ub1X46N c0Ub1X46D c0Ub1X46C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 46 0=((getRat xs 455 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e]; exact hr.1,c0Ub1X46cof⟩
    have lX64 : Lift s b J (X.getD 64 0) c0Ub1L c0Ub1X64N c0Ub1X64D c0Ub1X64C :=
      ⟨by
        have e : X.getD 64 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 64]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c0Ub1X64N,c0Ub1X64D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub1X64cof⟩
    have lY6 : Lift s b J (Y.getD 6 0) c0Ub1L c0Ub1Y6N c0Ub1Y6D c0Ub1Y6C :=
      ⟨by
        have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 6]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c0Ub1Y6N,c0Ub1Y6D,Ex.ev,ev3,ev2,ev1]
        ring,c0Ub1Y6cof⟩
    have lY67 : Lift s b J (Y.getD 67 0) c0Ub1L c0Ub1Y67N c0Ub1Y67D c0Ub1Y67C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 67 0=((getRat xs 967 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 67]; rfl
        rw [e]; exact hr.1,c0Ub1Y67cof⟩
    have lY71 : Lift s b J (Y.getD 71 0) c0Ub1L c0Ub1Y71N c0Ub1Y71D c0Ub1Y71C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 71 0=((getRat xs 964 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 71]; rfl
        rw [e]; exact hr.1,c0Ub1Y71cof⟩
    have hL : Ex.ev s b J c0Ub1L≠0 := by
      have k := RegCert.auto_sound c0Ub1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c0Ub1ok hL (detX_ev lX64.eq lY6.eq lX46.eq lY67.eq lX43.eq lY71.eq)
    push_cast at h; linarith
  · have lBy : Lift s b J (1-50050/s^2) c0bLowL c0bLowByN c0bLowByD c0bLowByC :=
      ⟨by simp [c0bLowByN,c0bLowByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0bLowBycof⟩
    have lY68 : Lift s b J (Y.getD 68 0) c0bLowL c0bLowY68N c0bLowY68D c0bLowY68C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 68 0=((getRat xs 506 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 68]; rfl
        rw [e]; exact hr.1,c0bLowY68cof⟩
    have lone : Lift s b J (1) c0bLowL c0bLowoneN c0bLowoneD c0bLowoneC :=
      ⟨by simp [c0bLowoneN,c0bLowoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0bLowonecof⟩
    have hL : Ex.ev s b J c0bLowL≠0 := by
      have k := RegCert.auto_sound c0bLowLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (by simp [c0bLowByD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0bLowok hL (linX_ev (one:=.mul c0bLowoneN c0bLowoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 68 0),(-1,1-50050/s^2)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY68.eq⟩,⟨by trivial,lBy.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY70 : Lift s b J (Y.getD 70 0) c0H43uL c0H43uY70N c0H43uY70D c0H43uY70C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : Y.getD 70 0=((getRat xs 449 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 70]; rfl
        rw [e]; exact hr.1,c0H43uY70cof⟩
    have lone : Lift s b J (1) c0H43uL c0H43uoneN c0H43uoneD c0H43uoneC :=
      ⟨by simp [c0H43uoneN,c0H43uoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0H43uonecof⟩
    have hL : Ex.ev s b J c0H43uL≠0 := by
      have k := RegCert.auto_sound c0H43uLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))).2
    have h := signed_sound B c0H43uok hL (linX_ev (one:=.mul c0H43uoneN c0H43uoneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 70 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY70.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0DL0L c0DL0BxN c0DL0BxD c0DL0BxC :=
      ⟨by simp [c0DL0BxN,c0DL0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DL0L c0DL0ByN c0DL0ByD c0DL0ByC :=
      ⟨by simp [c0DL0ByN,c0DL0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0Bycof⟩
    have lX43 : Lift s b J (X.getD 43 0) c0DL0L c0DL0X43N c0DL0X43D c0DL0X43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 43 0=((getRat xs 969 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 43]; rfl
        rw [e]; exact hr.1,c0DL0X43cof⟩
    have lY68 : Lift s b J (Y.getD 68 0) c0DL0L c0DL0Y68N c0DL0Y68D c0DL0Y68C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 68 0=((getRat xs 506 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 68]; rfl
        rw [e]; exact hr.1,c0DL0Y68cof⟩
    have lone : Lift s b J (1) c0DL0L c0DL0oneN c0DL0oneD c0DL0oneC :=
      ⟨by simp [c0DL0oneN,c0DL0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0onecof⟩
    have lzero : Lift s b J (0) c0DL0L c0DL0zeroN c0DL0zeroD c0DL0zeroC :=
      ⟨by simp [c0DL0zeroN,c0DL0zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL0zerocof⟩
    have hL : Ex.ev s b J c0DL0L≠0 := by
      have k := RegCert.auto_sound c0DL0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DL0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DL0ok hL (detX_ev lBx.eq lBy.eq lX43.eq lY68.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0DL1L c0DL1Bx15N c0DL1Bx15D c0DL1Bx15C :=
      ⟨by simp [c0DL1Bx15N,c0DL1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DL1L c0DL1ByN c0DL1ByD c0DL1ByC :=
      ⟨by simp [c0DL1ByN,c0DL1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1Bycof⟩
    have lX43 : Lift s b J (X.getD 43 0) c0DL1L c0DL1X43N c0DL1X43D c0DL1X43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 43 0=((getRat xs 969 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 43]; rfl
        rw [e]; exact hr.1,c0DL1X43cof⟩
    have lY68 : Lift s b J (Y.getD 68 0) c0DL1L c0DL1Y68N c0DL1Y68D c0DL1Y68C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 68 0=((getRat xs 506 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 68]; rfl
        rw [e]; exact hr.1,c0DL1Y68cof⟩
    have lone : Lift s b J (1) c0DL1L c0DL1oneN c0DL1oneD c0DL1oneC :=
      ⟨by simp [c0DL1oneN,c0DL1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1onecof⟩
    have lzero : Lift s b J (0) c0DL1L c0DL1zeroN c0DL1zeroD c0DL1zeroC :=
      ⟨by simp [c0DL1zeroN,c0DL1zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DL1zerocof⟩
    have hL : Ex.ev s b J c0DL1L≠0 := by
      have k := RegCert.auto_sound c0DL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DL1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DL1ok hL (detX_ev lBx15.eq lBy.eq lX43.eq lY68.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0DR0L c0DR0BxN c0DR0BxD c0DR0BxC :=
      ⟨by simp [c0DR0BxN,c0DR0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DR0L c0DR0ByN c0DR0ByD c0DR0ByC :=
      ⟨by simp [c0DR0ByN,c0DR0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0Bycof⟩
    have lWq : Lift s b J (s/320) c0DR0L c0DR0WqN c0DR0WqD c0DR0WqC :=
      ⟨by simp [c0DR0WqN,c0DR0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0Wqcof⟩
    have lX43 : Lift s b J (X.getD 43 0) c0DR0L c0DR0X43N c0DR0X43D c0DR0X43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 43 0=((getRat xs 969 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 43]; rfl
        rw [e]; exact hr.1,c0DR0X43cof⟩
    have lY68 : Lift s b J (Y.getD 68 0) c0DR0L c0DR0Y68N c0DR0Y68D c0DR0Y68C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 68 0=((getRat xs 506 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 68]; rfl
        rw [e]; exact hr.1,c0DR0Y68cof⟩
    have lone : Lift s b J (1) c0DR0L c0DR0oneN c0DR0oneD c0DR0oneC :=
      ⟨by simp [c0DR0oneN,c0DR0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR0onecof⟩
    have hL : Ex.ev s b J c0DR0L≠0 := by
      have k := RegCert.auto_sound c0DR0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DR0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DR0ok hL (detX_ev lBx.eq lBy.eq lX43.eq lY68.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0DR1L c0DR1Bx15N c0DR1Bx15D c0DR1Bx15C :=
      ⟨by simp [c0DR1Bx15N,c0DR1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0DR1L c0DR1ByN c0DR1ByD c0DR1ByC :=
      ⟨by simp [c0DR1ByN,c0DR1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1Bycof⟩
    have lWq : Lift s b J (s/320) c0DR1L c0DR1WqN c0DR1WqD c0DR1WqC :=
      ⟨by simp [c0DR1WqN,c0DR1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1Wqcof⟩
    have lX43 : Lift s b J (X.getD 43 0) c0DR1L c0DR1X43N c0DR1X43D c0DR1X43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 43 0=((getRat xs 969 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 43]; rfl
        rw [e]; exact hr.1,c0DR1X43cof⟩
    have lY68 : Lift s b J (Y.getD 68 0) c0DR1L c0DR1Y68N c0DR1Y68D c0DR1Y68C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 68 0=((getRat xs 506 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 68]; rfl
        rw [e]; exact hr.1,c0DR1Y68cof⟩
    have lone : Lift s b J (1) c0DR1L c0DR1oneN c0DR1oneD c0DR1oneC :=
      ⟨by simp [c0DR1oneN,c0DR1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0DR1onecof⟩
    have hL : Ex.ev s b J c0DR1L≠0 := by
      have k := RegCert.auto_sound c0DR1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c0DR1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0DR1ok hL (detX_ev lBx15.eq lBy.eq lX43.eq lY68.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lX50 : Lift s b J (X.getD 50 0) c0hdlL c0hdlX50N c0hdlX50D c0hdlX50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 50 0=((getRat xs 1070 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 50]; rfl
        rw [e]; exact hr.1,c0hdlX50cof⟩
    have lone : Lift s b J (1) c0hdlL c0hdloneN c0hdloneD c0hdloneC :=
      ⟨by simp [c0hdloneN,c0hdloneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hdlonecof⟩
    have hL : Ex.ev s b J c0hdlL≠0 := by
      have k := RegCert.auto_sound c0hdlLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hdlok hL (linX_ev (one:=.mul c0hdloneN c0hdloneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 50 0),(0,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX50.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lWq : Lift s b J (s/320) c0hdrL c0hdrWqN c0hdrWqD c0hdrWqC :=
      ⟨by simp [c0hdrWqN,c0hdrWqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hdrWqcof⟩
    have lX51 : Lift s b J (X.getD 51 0) c0hdrL c0hdrX51N c0hdrX51D c0hdrX51C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 51 0=((getRat xs 1216 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 51]; rfl
        rw [e]; exact hr.1,c0hdrX51cof⟩
    have lone : Lift s b J (1) c0hdrL c0hdroneN c0hdroneD c0hdroneC :=
      ⟨by simp [c0hdroneN,c0hdroneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0hdronecof⟩
    have hL : Ex.ev s b J c0hdrL≠0 := by
      have k := RegCert.auto_sound c0hdrLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0hdrok hL (linX_ev (one:=.mul c0hdroneN c0hdroneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 51 0),(-1,s/320)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX51.eq⟩,⟨by trivial,lWq.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith

/-- Range conditions of the copy tests of channel 1. -/
theorem ranges1 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 3 ∧ getRat args 3≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((40:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    Y.getD 20 0=(1:ℝ)/1 ∧
    0<ArtGallery.det (X.getD 67 0,Y.getD 4 0) (X.getD 34 0,Y.getD 49 0) (X.getD 30 0,Y.getD 53 0) ∧
    0<ArtGallery.det (X.getD 68 0,Y.getD 4 0) (X.getD 34 0,Y.getD 49 0) (X.getD 30 0,Y.getD 53 0) ∧
    ArtGallery.det (X.getD 67 0,Y.getD 4 0) (X.getD 34 0,Y.getD 49 0) (X.getD 31 0,Y.getD 53 0)<0 ∧
    ArtGallery.det (X.getD 68 0,Y.getD 4 0) (X.getD 34 0,Y.getD 49 0) (X.getD 31 0,Y.getD 53 0)<0 ∧
    0<(1:ℝ)*(Y.getD 50 0)+(-1:ℝ)*(1-50050/s^2) ∧
    0<(3:ℝ)*(Y.getD 52 0)+(-7:ℝ)*(1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 31 0,Y.getD 50 0) (0,1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 31 0,Y.getD 50 0) (0,1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 31 0,Y.getD 50 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 31 0,Y.getD 50 0) (s/320,1)<0 ∧
    X.getD 50 0=(0:ℝ)/1 ∧
    X.getD 51 0=s/320 := by
  intro s J Q b X Y
  have Xdef : X=(grid template args false).map (fun q : ℚ => (q:ℝ)) := rfl
  have Ydef : Y=(grid template args true).map (fun q : ℚ => (q:ℝ)) := rfl
  have hs : (0:ℝ)<s := by simp only [s]; exact_mod_cast m.pos
  have hs1 : s≤(((1/65:ℚ):ℚ):ℝ) := by simp only [s]; exact_mod_cast m.upper
  have hJ' : (0:ℝ)≤J ∧ J≤1 := by simp only [J]; exact ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  have hQ' : (0:ℝ)≤Q ∧ Q≤1 := by simp only [Q]; exact ⟨by exact_mod_cast hQ.1,by exact_mod_cast hQ.2⟩
  have B : PolyBox.Box (1/65:ℚ) (199/5005:ℚ) (797/18590:ℚ) s b J := by
    refine ⟨hs,hs1,?_,?_,hJ'.1,hJ'.2,by norm_num⟩
    · simp only [b]; push_cast; nlinarith
    · simp only [b]; push_cast at hs1 ⊢; nlinarith [mul_le_mul hJ'.2 hs1 hs.le zero_le_one]
  have hin : ∀ k P d, (k,P,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c1ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c1hold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lY20 : Lift s b J (Y.getD 20 0) c1hwyL c1hwyY20N c1hwyY20D c1hwyY20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1197 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1hwyY20cof⟩
    have lone : Lift s b J (1) c1hwyL c1hwyoneN c1hwyoneD c1hwyoneC :=
      ⟨by simp [c1hwyoneN,c1hwyoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hwyonecof⟩
    have hL : Ex.ev s b J c1hwyL≠0 := by
      have k := RegCert.auto_sound c1hwyLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1hwyok hL (linX_ev (one:=.mul c1hwyoneN c1hwyoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 20 0),(-1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY20.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX30 : Lift s b J (X.getD 30 0) c1Ua0L c1Ua0X30N c1Ua0X30D c1Ua0X30C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
        have e : X.getD 30 0=((getRat xs 129 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 30]; rfl
        rw [e]; exact hr.1,c1Ua0X30cof⟩
    have lX34 : Lift s b J (X.getD 34 0) c1Ua0L c1Ua0X34N c1Ua0X34D c1Ua0X34C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 34 0=((getRat xs 424 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 34]; rfl
        rw [e]; exact hr.1,c1Ua0X34cof⟩
    have lX67 : Lift s b J (X.getD 67 0) c1Ua0L c1Ua0X67N c1Ua0X67D c1Ua0X67C :=
      ⟨by
        have e : X.getD 67 0=((((axisOf template false).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 67]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c1Ua0X67N,c1Ua0X67D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ua0X67cof⟩
    have lY4 : Lift s b J (Y.getD 4 0) c1Ua0L c1Ua0Y4N c1Ua0Y4D c1Ua0Y4C :=
      ⟨by
        have e : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 4]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c1Ua0Y4N,c1Ua0Y4D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ua0Y4cof⟩
    have lY49 : Lift s b J (Y.getD 49 0) c1Ua0L c1Ua0Y49N c1Ua0Y49D c1Ua0Y49C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 49 0=((getRat xs 747 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 49]; rfl
        rw [e]; exact hr.1,c1Ua0Y49cof⟩
    have lY53 : Lift s b J (Y.getD 53 0) c1Ua0L c1Ua0Y53N c1Ua0Y53D c1Ua0Y53C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 53 0=((getRat xs 744 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 53]; rfl
        rw [e]; exact hr.1,c1Ua0Y53cof⟩
    have hL : Ex.ev s b J c1Ua0L≠0 := by
      have k := RegCert.auto_sound c1Ua0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1Ua0ok hL (detX_ev lX67.eq lY4.eq lX34.eq lY49.eq lX30.eq lY53.eq)
    push_cast at h; linarith
  · have lX30 : Lift s b J (X.getD 30 0) c1Ua1L c1Ua1X30N c1Ua1X30D c1Ua1X30C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
        have e : X.getD 30 0=((getRat xs 129 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 30]; rfl
        rw [e]; exact hr.1,c1Ua1X30cof⟩
    have lX34 : Lift s b J (X.getD 34 0) c1Ua1L c1Ua1X34N c1Ua1X34D c1Ua1X34C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 34 0=((getRat xs 424 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 34]; rfl
        rw [e]; exact hr.1,c1Ua1X34cof⟩
    have lX68 : Lift s b J (X.getD 68 0) c1Ua1L c1Ua1X68N c1Ua1X68D c1Ua1X68C :=
      ⟨by
        have e : X.getD 68 0=((((axisOf template false).coordsQ (getRat args 0)).getD 7 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 68]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c1Ua1X68N,c1Ua1X68D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ua1X68cof⟩
    have lY4 : Lift s b J (Y.getD 4 0) c1Ua1L c1Ua1Y4N c1Ua1Y4D c1Ua1Y4C :=
      ⟨by
        have e : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 4]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c1Ua1Y4N,c1Ua1Y4D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ua1Y4cof⟩
    have lY49 : Lift s b J (Y.getD 49 0) c1Ua1L c1Ua1Y49N c1Ua1Y49D c1Ua1Y49C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 49 0=((getRat xs 747 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 49]; rfl
        rw [e]; exact hr.1,c1Ua1Y49cof⟩
    have lY53 : Lift s b J (Y.getD 53 0) c1Ua1L c1Ua1Y53N c1Ua1Y53D c1Ua1Y53C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 53 0=((getRat xs 744 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 53]; rfl
        rw [e]; exact hr.1,c1Ua1Y53cof⟩
    have hL : Ex.ev s b J c1Ua1L≠0 := by
      have k := RegCert.auto_sound c1Ua1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1Ua1ok hL (detX_ev lX68.eq lY4.eq lX34.eq lY49.eq lX30.eq lY53.eq)
    push_cast at h; linarith
  · have lX31 : Lift s b J (X.getD 31 0) c1Ub0L c1Ub0X31N c1Ub0X31D c1Ub0X31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 31 0=((getRat xs 749 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 31]; rfl
        rw [e]; exact hr.1,c1Ub0X31cof⟩
    have lX34 : Lift s b J (X.getD 34 0) c1Ub0L c1Ub0X34N c1Ub0X34D c1Ub0X34C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 34 0=((getRat xs 424 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 34]; rfl
        rw [e]; exact hr.1,c1Ub0X34cof⟩
    have lX67 : Lift s b J (X.getD 67 0) c1Ub0L c1Ub0X67N c1Ub0X67D c1Ub0X67C :=
      ⟨by
        have e : X.getD 67 0=((((axisOf template false).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 67]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c1Ub0X67N,c1Ub0X67D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ub0X67cof⟩
    have lY4 : Lift s b J (Y.getD 4 0) c1Ub0L c1Ub0Y4N c1Ub0Y4D c1Ub0Y4C :=
      ⟨by
        have e : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 4]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c1Ub0Y4N,c1Ub0Y4D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ub0Y4cof⟩
    have lY49 : Lift s b J (Y.getD 49 0) c1Ub0L c1Ub0Y49N c1Ub0Y49D c1Ub0Y49C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 49 0=((getRat xs 747 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 49]; rfl
        rw [e]; exact hr.1,c1Ub0Y49cof⟩
    have lY53 : Lift s b J (Y.getD 53 0) c1Ub0L c1Ub0Y53N c1Ub0Y53D c1Ub0Y53C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 53 0=((getRat xs 744 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 53]; rfl
        rw [e]; exact hr.1,c1Ub0Y53cof⟩
    have hL : Ex.ev s b J c1Ub0L≠0 := by
      have k := RegCert.auto_sound c1Ub0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c1Ub0ok hL (detX_ev lX67.eq lY4.eq lX34.eq lY49.eq lX31.eq lY53.eq)
    push_cast at h; linarith
  · have lX31 : Lift s b J (X.getD 31 0) c1Ub1L c1Ub1X31N c1Ub1X31D c1Ub1X31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 31 0=((getRat xs 749 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 31]; rfl
        rw [e]; exact hr.1,c1Ub1X31cof⟩
    have lX34 : Lift s b J (X.getD 34 0) c1Ub1L c1Ub1X34N c1Ub1X34D c1Ub1X34C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 34 0=((getRat xs 424 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 34]; rfl
        rw [e]; exact hr.1,c1Ub1X34cof⟩
    have lX68 : Lift s b J (X.getD 68 0) c1Ub1L c1Ub1X68N c1Ub1X68D c1Ub1X68C :=
      ⟨by
        have e : X.getD 68 0=((((axisOf template false).coordsQ (getRat args 0)).getD 7 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 68]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c1Ub1X68N,c1Ub1X68D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ub1X68cof⟩
    have lY4 : Lift s b J (Y.getD 4 0) c1Ub1L c1Ub1Y4N c1Ub1Y4D c1Ub1Y4C :=
      ⟨by
        have e : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 4]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c1Ub1Y4N,c1Ub1Y4D,Ex.ev,ev3,ev2,ev1]
        ring,c1Ub1Y4cof⟩
    have lY49 : Lift s b J (Y.getD 49 0) c1Ub1L c1Ub1Y49N c1Ub1Y49D c1Ub1Y49C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 49 0=((getRat xs 747 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 49]; rfl
        rw [e]; exact hr.1,c1Ub1Y49cof⟩
    have lY53 : Lift s b J (Y.getD 53 0) c1Ub1L c1Ub1Y53N c1Ub1Y53D c1Ub1Y53C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 53 0=((getRat xs 744 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 53]; rfl
        rw [e]; exact hr.1,c1Ub1Y53cof⟩
    have hL : Ex.ev s b J c1Ub1L≠0 := by
      have k := RegCert.auto_sound c1Ub1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2)
    have h := signed_sound B c1Ub1ok hL (detX_ev lX68.eq lY4.eq lX34.eq lY49.eq lX31.eq lY53.eq)
    push_cast at h; linarith
  · have lBy : Lift s b J (1-50050/s^2) c1bLowL c1bLowByN c1bLowByD c1bLowByC :=
      ⟨by simp [c1bLowByN,c1bLowByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1bLowBycof⟩
    have lY50 : Lift s b J (Y.getD 50 0) c1bLowL c1bLowY50N c1bLowY50D c1bLowY50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 50 0=((getRat xs 493 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 50]; rfl
        rw [e]; exact hr.1,c1bLowY50cof⟩
    have lone : Lift s b J (1) c1bLowL c1bLowoneN c1bLowoneD c1bLowoneC :=
      ⟨by simp [c1bLowoneN,c1bLowoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1bLowonecof⟩
    have hL : Ex.ev s b J c1bLowL≠0 := by
      have k := RegCert.auto_sound c1bLowLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (by simp [c1bLowByD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1bLowok hL (linX_ev (one:=.mul c1bLowoneN c1bLowoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 50 0),(-1,1-50050/s^2)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY50.eq⟩,⟨by trivial,lBy.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY52 : Lift s b J (Y.getD 52 0) c1H43uL c1H43uY52N c1H43uY52D c1H43uY52C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : Y.getD 52 0=((getRat xs 418 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 52]; rfl
        rw [e]; exact hr.1,c1H43uY52cof⟩
    have lone : Lift s b J (1) c1H43uL c1H43uoneN c1H43uoneD c1H43uoneC :=
      ⟨by simp [c1H43uoneN,c1H43uoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1H43uonecof⟩
    have hL : Ex.ev s b J c1H43uL≠0 := by
      have k := RegCert.auto_sound c1H43uLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))).2
    have h := signed_sound B c1H43uok hL (linX_ev (one:=.mul c1H43uoneN c1H43uoneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 52 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY52.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c1DL0L c1DL0BxN c1DL0BxD c1DL0BxC :=
      ⟨by simp [c1DL0BxN,c1DL0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c1DL0L c1DL0ByN c1DL0ByD c1DL0ByC :=
      ⟨by simp [c1DL0ByN,c1DL0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL0Bycof⟩
    have lX31 : Lift s b J (X.getD 31 0) c1DL0L c1DL0X31N c1DL0X31D c1DL0X31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 31 0=((getRat xs 749 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 31]; rfl
        rw [e]; exact hr.1,c1DL0X31cof⟩
    have lY50 : Lift s b J (Y.getD 50 0) c1DL0L c1DL0Y50N c1DL0Y50D c1DL0Y50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 50 0=((getRat xs 493 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 50]; rfl
        rw [e]; exact hr.1,c1DL0Y50cof⟩
    have lone : Lift s b J (1) c1DL0L c1DL0oneN c1DL0oneD c1DL0oneC :=
      ⟨by simp [c1DL0oneN,c1DL0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL0onecof⟩
    have lzero : Lift s b J (0) c1DL0L c1DL0zeroN c1DL0zeroD c1DL0zeroC :=
      ⟨by simp [c1DL0zeroN,c1DL0zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL0zerocof⟩
    have hL : Ex.ev s b J c1DL0L≠0 := by
      have k := RegCert.auto_sound c1DL0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c1DL0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1DL0ok hL (detX_ev lBx.eq lBy.eq lX31.eq lY50.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c1DL1L c1DL1Bx15N c1DL1Bx15D c1DL1Bx15C :=
      ⟨by simp [c1DL1Bx15N,c1DL1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c1DL1L c1DL1ByN c1DL1ByD c1DL1ByC :=
      ⟨by simp [c1DL1ByN,c1DL1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL1Bycof⟩
    have lX31 : Lift s b J (X.getD 31 0) c1DL1L c1DL1X31N c1DL1X31D c1DL1X31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 31 0=((getRat xs 749 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 31]; rfl
        rw [e]; exact hr.1,c1DL1X31cof⟩
    have lY50 : Lift s b J (Y.getD 50 0) c1DL1L c1DL1Y50N c1DL1Y50D c1DL1Y50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 50 0=((getRat xs 493 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 50]; rfl
        rw [e]; exact hr.1,c1DL1Y50cof⟩
    have lone : Lift s b J (1) c1DL1L c1DL1oneN c1DL1oneD c1DL1oneC :=
      ⟨by simp [c1DL1oneN,c1DL1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL1onecof⟩
    have lzero : Lift s b J (0) c1DL1L c1DL1zeroN c1DL1zeroD c1DL1zeroC :=
      ⟨by simp [c1DL1zeroN,c1DL1zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DL1zerocof⟩
    have hL : Ex.ev s b J c1DL1L≠0 := by
      have k := RegCert.auto_sound c1DL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c1DL1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1DL1ok hL (detX_ev lBx15.eq lBy.eq lX31.eq lY50.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c1DR0L c1DR0BxN c1DR0BxD c1DR0BxC :=
      ⟨by simp [c1DR0BxN,c1DR0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c1DR0L c1DR0ByN c1DR0ByD c1DR0ByC :=
      ⟨by simp [c1DR0ByN,c1DR0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR0Bycof⟩
    have lWq : Lift s b J (s/320) c1DR0L c1DR0WqN c1DR0WqD c1DR0WqC :=
      ⟨by simp [c1DR0WqN,c1DR0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR0Wqcof⟩
    have lX31 : Lift s b J (X.getD 31 0) c1DR0L c1DR0X31N c1DR0X31D c1DR0X31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 31 0=((getRat xs 749 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 31]; rfl
        rw [e]; exact hr.1,c1DR0X31cof⟩
    have lY50 : Lift s b J (Y.getD 50 0) c1DR0L c1DR0Y50N c1DR0Y50D c1DR0Y50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 50 0=((getRat xs 493 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 50]; rfl
        rw [e]; exact hr.1,c1DR0Y50cof⟩
    have lone : Lift s b J (1) c1DR0L c1DR0oneN c1DR0oneD c1DR0oneC :=
      ⟨by simp [c1DR0oneN,c1DR0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR0onecof⟩
    have hL : Ex.ev s b J c1DR0L≠0 := by
      have k := RegCert.auto_sound c1DR0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c1DR0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1DR0ok hL (detX_ev lBx.eq lBy.eq lX31.eq lY50.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c1DR1L c1DR1Bx15N c1DR1Bx15D c1DR1Bx15C :=
      ⟨by simp [c1DR1Bx15N,c1DR1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c1DR1L c1DR1ByN c1DR1ByD c1DR1ByC :=
      ⟨by simp [c1DR1ByN,c1DR1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR1Bycof⟩
    have lWq : Lift s b J (s/320) c1DR1L c1DR1WqN c1DR1WqD c1DR1WqC :=
      ⟨by simp [c1DR1WqN,c1DR1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR1Wqcof⟩
    have lX31 : Lift s b J (X.getD 31 0) c1DR1L c1DR1X31N c1DR1X31D c1DR1X31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : X.getD 31 0=((getRat xs 749 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 31]; rfl
        rw [e]; exact hr.1,c1DR1X31cof⟩
    have lY50 : Lift s b J (Y.getD 50 0) c1DR1L c1DR1Y50N c1DR1Y50D c1DR1Y50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 50 0=((getRat xs 493 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 50]; rfl
        rw [e]; exact hr.1,c1DR1Y50cof⟩
    have lone : Lift s b J (1) c1DR1L c1DR1oneN c1DR1oneD c1DR1oneC :=
      ⟨by simp [c1DR1oneN,c1DR1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1DR1onecof⟩
    have hL : Ex.ev s b J c1DR1L≠0 := by
      have k := RegCert.auto_sound c1DR1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2) (by simp [c1DR1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1DR1ok hL (detX_ev lBx15.eq lBy.eq lX31.eq lY50.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lX50 : Lift s b J (X.getD 50 0) c1hdlL c1hdlX50N c1hdlX50D c1hdlX50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 50 0=((getRat xs 1070 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 50]; rfl
        rw [e]; exact hr.1,c1hdlX50cof⟩
    have lone : Lift s b J (1) c1hdlL c1hdloneN c1hdloneD c1hdloneC :=
      ⟨by simp [c1hdloneN,c1hdloneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hdlonecof⟩
    have hL : Ex.ev s b J c1hdlL≠0 := by
      have k := RegCert.auto_sound c1hdlLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1hdlok hL (linX_ev (one:=.mul c1hdloneN c1hdloneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 50 0),(0,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX50.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lWq : Lift s b J (s/320) c1hdrL c1hdrWqN c1hdrWqD c1hdrWqC :=
      ⟨by simp [c1hdrWqN,c1hdrWqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hdrWqcof⟩
    have lX51 : Lift s b J (X.getD 51 0) c1hdrL c1hdrX51N c1hdrX51D c1hdrX51C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 51 0=((getRat xs 1216 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 51]; rfl
        rw [e]; exact hr.1,c1hdrX51cof⟩
    have lone : Lift s b J (1) c1hdrL c1hdroneN c1hdroneD c1hdroneC :=
      ⟨by simp [c1hdroneN,c1hdroneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1hdronecof⟩
    have hL : Ex.ev s b J c1hdrL≠0 := by
      have k := RegCert.auto_sound c1hdrLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1hdrok hL (linX_ev (one:=.mul c1hdroneN c1hdroneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 51 0),(-1,s/320)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX51.eq⟩,⟨by trivial,lWq.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith

/-- Range conditions of the copy tests of channel 2. -/
theorem ranges2 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 4 ∧ getRat args 4≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 4
    let b : ℝ := ((((1000:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    X.getD 61 0=(301:ℝ)/2 ∧
    Y.getD 20 0=(1:ℝ)/1 ∧
    X.getD 72 0=X.getD 71 0+3/2*(1-Y.getD 2 0)/(50050/s^2) ∧
    0<ArtGallery.det (X.getD 72 0,Y.getD 2 0) (X.getD 61 0,Y.getD 20 0) (X.getD 21 0,Y.getD 29 0) ∧
    ArtGallery.det (X.getD 71 0,Y.getD 2 0) (X.getD 61 0,Y.getD 20 0) (X.getD 22 0,Y.getD 29 0)<0 ∧
    0<(1:ℝ)*(50050/s^2)+(-1:ℝ)*(Y.getD 30 0)+(1:ℝ)*(1) ∧
    0<(3:ℝ)*(Y.getD 29 0)+(-7:ℝ)*(1) := by
  intro s J Q b X Y
  have Xdef : X=(grid template args false).map (fun q : ℚ => (q:ℝ)) := rfl
  have Ydef : Y=(grid template args true).map (fun q : ℚ => (q:ℝ)) := rfl
  have hs : (0:ℝ)<s := by simp only [s]; exact_mod_cast m.pos
  have hs1 : s≤(((1/65:ℚ):ℚ):ℝ) := by simp only [s]; exact_mod_cast m.upper
  have hJ' : (0:ℝ)≤J ∧ J≤1 := by simp only [J]; exact ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  have hQ' : (0:ℝ)≤Q ∧ Q≤1 := by simp only [Q]; exact ⟨by exact_mod_cast hQ.1,by exact_mod_cast hQ.2⟩
  have B : PolyBox.Box (1/65:ℚ) (4999/5005:ℚ) (130379/130130:ℚ) s b J := by
    refine ⟨hs,hs1,?_,?_,hJ'.1,hJ'.2,by norm_num⟩
    · simp only [b]; push_cast; nlinarith
    · simp only [b]; push_cast at hs1 ⊢; nlinarith [mul_le_mul hJ'.2 hs1 hs.le zero_le_one]
  have hin : ∀ k P d, (k,P,d)∈c2ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c2ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c2hold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have lX61 : Lift s b J (X.getD 61 0) c2hwxL c2hwxX61N c2hwxX61D c2hwxX61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1212 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c2hwxX61cof⟩
    have lone : Lift s b J (1) c2hwxL c2hwxoneN c2hwxoneD c2hwxoneC :=
      ⟨by simp [c2hwxoneN,c2hwxoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2hwxonecof⟩
    have hL : Ex.ev s b J c2hwxL≠0 := by
      have k := RegCert.auto_sound c2hwxLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c2hwxok hL (linX_ev (one:=.mul c2hwxoneN c2hwxoneC) (lone.eq.trans (one_mul _)) _ [(2,X.getD 61 0),(-301,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX61.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY20 : Lift s b J (Y.getD 20 0) c2hwyL c2hwyY20N c2hwyY20D c2hwyY20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1197 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c2hwyY20cof⟩
    have lone : Lift s b J (1) c2hwyL c2hwyoneN c2hwyoneD c2hwyoneC :=
      ⟨by simp [c2hwyoneN,c2hwyoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2hwyonecof⟩
    have hL : Ex.ev s b J c2hwyL≠0 := by
      have k := RegCert.auto_sound c2hwyLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c2hwyok hL (linX_ev (one:=.mul c2hwyoneN c2hwyoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 20 0),(-1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY20.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX71 : Lift s b J (X.getD 71 0) c2hrbL c2hrbX71N c2hrbX71D c2hrbX71C :=
      ⟨by
        have e : X.getD 71 0=((((axisOf template false).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 71]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c2hrbX71N,c2hrbX71D,Ex.ev,ev3,ev2,ev1]
        ring,c2hrbX71cof⟩
    have lX72 : Lift s b J (X.getD 72 0) c2hrbL c2hrbX72N c2hrbX72D c2hrbX72C :=
      ⟨by
        have e : X.getD 72 0=((((axisOf template false).coordsQ (getRat args 0)).getD 11 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 72]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c2hrbX72N,c2hrbX72D,Ex.ev,ev3,ev2,ev1]
        ring,c2hrbX72cof⟩
    have lY2 : Lift s b J (Y.getD 2 0) c2hrbL c2hrbY2N c2hrbY2D c2hrbY2C :=
      ⟨by
        have e : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 2]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c2hrbY2N,c2hrbY2D,Ex.ev,ev3,ev2,ev1]
        ring,c2hrbY2cof⟩
    have lone : Lift s b J (1) c2hrbL c2hrboneN c2hrboneD c2hrboneC :=
      ⟨by simp [c2hrboneN,c2hrboneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2hrbonecof⟩
    have lvD : Lift s b J (50050/s^2) c2hrbL c2hrbvDN c2hrbvDD c2hrbvDC :=
      ⟨by simp [c2hrbvDN,c2hrbvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2hrbvDcof⟩
    have hL : Ex.ev s b J c2hrbL≠0 := by
      have k := RegCert.auto_sound c2hrbLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (by simp [c2hrbvDD,Ex.ev,ev3,ev2,ev1]; positivity) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := zero_of_check c2hrbok hL (spotX_ev lX72.eq lX71.eq lvD.eq lY2.eq (lone.eq.trans (one_mul _)))
    have hs2 : (50050:ℝ)/s^2≠0 := by positivity
    field_simp at h ⊢; linarith
  · have lX21 : Lift s b J (X.getD 21 0) c2L1L c2L1X21N c2L1X21D c2L1X21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 21 0=((getRat xs 191 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 21]; rfl
        rw [e]; exact hr.1,c2L1X21cof⟩
    have lX61 : Lift s b J (X.getD 61 0) c2L1L c2L1X61N c2L1X61D c2L1X61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1212 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c2L1X61cof⟩
    have lX72 : Lift s b J (X.getD 72 0) c2L1L c2L1X72N c2L1X72D c2L1X72C :=
      ⟨by
        have e : X.getD 72 0=((((axisOf template false).coordsQ (getRat args 0)).getD 11 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 72]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c2L1X72N,c2L1X72D,Ex.ev,ev3,ev2,ev1]
        ring,c2L1X72cof⟩
    have lY2 : Lift s b J (Y.getD 2 0) c2L1L c2L1Y2N c2L1Y2D c2L1Y2C :=
      ⟨by
        have e : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 2]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c2L1Y2N,c2L1Y2D,Ex.ev,ev3,ev2,ev1]
        ring,c2L1Y2cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c2L1L c2L1Y20N c2L1Y20D c2L1Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1197 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c2L1Y20cof⟩
    have lY29 : Lift s b J (Y.getD 29 0) c2L1L c2L1Y29N c2L1Y29D c2L1Y29C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 29 0=((getRat xs 525 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 29]; rfl
        rw [e]; exact hr.1,c2L1Y29cof⟩
    have hL : Ex.ev s b J c2L1L≠0 := by
      have k := RegCert.auto_sound c2L1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2
    have h := signed_sound B c2L1ok hL (detX_ev lX72.eq lY2.eq lX61.eq lY20.eq lX21.eq lY29.eq)
    push_cast at h; linarith
  · have lX22 : Lift s b J (X.getD 22 0) c2L2L c2L2X22N c2L2X22D c2L2X22C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : X.getD 22 0=((getRat xs 35 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 22]; rfl
        rw [e]; exact hr.1,c2L2X22cof⟩
    have lX61 : Lift s b J (X.getD 61 0) c2L2L c2L2X61N c2L2X61D c2L2X61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1212 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c2L2X61cof⟩
    have lX71 : Lift s b J (X.getD 71 0) c2L2L c2L2X71N c2L2X71D c2L2X71C :=
      ⟨by
        have e : X.getD 71 0=((((axisOf template false).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 71]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.xAxis,Gap.valR,evalR,c2L2X71N,c2L2X71D,Ex.ev,ev3,ev2,ev1]
        ring,c2L2X71cof⟩
    have lY2 : Lift s b J (Y.getD 2 0) c2L2L c2L2Y2N c2L2Y2D c2L2Y2C :=
      ⟨by
        have e : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 2]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Lower.yAxis,Gap.valR,evalR,c2L2Y2N,c2L2Y2D,Ex.ev,ev3,ev2,ev1]
        ring,c2L2Y2cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c2L2L c2L2Y20N c2L2Y20D c2L2Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1197 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c2L2Y20cof⟩
    have lY29 : Lift s b J (Y.getD 29 0) c2L2L c2L2Y29N c2L2Y29D c2L2Y29C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 29 0=((getRat xs 525 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 29]; rfl
        rw [e]; exact hr.1,c2L2Y29cof⟩
    have hL : Ex.ev s b J c2L2L≠0 := by
      have k := RegCert.auto_sound c2L2Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c2L2ok hL (detX_ev lX71.eq lY2.eq lX61.eq lY20.eq lX22.eq lY29.eq)
    push_cast at h; linarith
  · have lY30 : Lift s b J (Y.getD 30 0) c2deepL c2deepY30N c2deepY30D c2deepY30C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 30 0=((getRat xs 220 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 30]; rfl
        rw [e]; exact hr.1,c2deepY30cof⟩
    have lone : Lift s b J (1) c2deepL c2deeponeN c2deeponeD c2deeponeC :=
      ⟨by simp [c2deeponeN,c2deeponeD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2deeponecof⟩
    have lvD : Lift s b J (50050/s^2) c2deepL c2deepvDN c2deepvDD c2deepvDC :=
      ⟨by simp [c2deepvDN,c2deepvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2deepvDcof⟩
    have hL : Ex.ev s b J c2deepL≠0 := by
      have k := RegCert.auto_sound c2deepLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (by simp [c2deepvDD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2deepok hL (linX_ev (one:=.mul c2deeponeN c2deeponeC) (lone.eq.trans (one_mul _)) _ [(1,50050/s^2),(-1,Y.getD 30 0),(1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lvD.eq⟩,⟨by trivial,lY30.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY29 : Lift s b J (Y.getD 29 0) c2H43L c2H43Y29N c2H43Y29D c2H43Y29C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 29 0=((getRat xs 525 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 29]; rfl
        rw [e]; exact hr.1,c2H43Y29cof⟩
    have lone : Lift s b J (1) c2H43L c2H43oneN c2H43oneD c2H43oneC :=
      ⟨by simp [c2H43oneN,c2H43oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2H43onecof⟩
    have hL : Ex.ev s b J c2H43L≠0 := by
      have k := RegCert.auto_sound c2H43Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2
    have h := signed_sound B c2H43ok hL (linX_ev (one:=.mul c2H43oneN c2H43oneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 29 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY29.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_10_40_1000
end
