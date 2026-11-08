module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XS1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XHold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XI0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XI1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XI2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C0XI3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C1XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C1XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C1XHold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C1XI0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C1XI1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C1XI2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360.C1XI3

/-! Range conditions of the other copy test of each channel of profile `InvLe_1_360`
(generated), for the completeness proof. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvLe_1_360
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
    0<ArtGallery.det (X.getD 45 0,Y.getD 1 0) (X.getD 28 0,Y.getD 39 0) (X.getD 24 0,Y.getD 43 0) ∧
    0<ArtGallery.det (X.getD 46 0,Y.getD 1 0) (X.getD 28 0,Y.getD 39 0) (X.getD 24 0,Y.getD 43 0) ∧
    ArtGallery.det (X.getD 45 0,Y.getD 1 0) (X.getD 28 0,Y.getD 39 0) (X.getD 25 0,Y.getD 43 0)<0 ∧
    ArtGallery.det (X.getD 46 0,Y.getD 1 0) (X.getD 28 0,Y.getD 39 0) (X.getD 25 0,Y.getD 43 0)<0 ∧
    0<(1:ℝ)*(Y.getD 40 0)+(-1:ℝ)*(1-50050/s^2) ∧
    0<(3:ℝ)*(Y.getD 42 0)+(-7:ℝ)*(1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 25 0,Y.getD 40 0) (0,1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 25 0,Y.getD 40 0) (0,1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 25 0,Y.getD 40 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 25 0,Y.getD 40 0) (s/320,1)<0 ∧
    X.getD 32 0=(0:ℝ)/1 ∧
    X.getD 33 0=s/320 ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 28 0,Y.getD 43 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 28 0,Y.getD 43 0) (s/320,1)<0 := by
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
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lX24 : Lift s b J (X.getD 24 0) c0xUa0L c0xUa0X24N c0xUa0X24D c0xUa0X24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : X.getD 24 0=((getRat xs 93 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 24]; rfl
        rw [e]; exact hr.1,c0xUa0X24cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xUa0L c0xUa0X28N c0xUa0X28D c0xUa0X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 28 0=((getRat xs 315 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xUa0X28cof⟩
    have lX45 : Lift s b J (X.getD 45 0) c0xUa0L c0xUa0X45N c0xUa0X45D c0xUa0X45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0xUa0X45N,c0xUa0X45D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUa0X45cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0xUa0L c0xUa0Y1N c0xUa0Y1D c0xUa0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c0xUa0Y1N,c0xUa0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUa0Y1cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0xUa0L c0xUa0Y39N c0xUa0Y39D c0xUa0Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 39 0=((getRat xs 578 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0xUa0Y39cof⟩
    have lY43 : Lift s b J (Y.getD 43 0) c0xUa0L c0xUa0Y43N c0xUa0Y43D c0xUa0Y43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 43 0=((getRat xs 575 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 43]; rfl
        rw [e]; exact hr.1,c0xUa0Y43cof⟩
    have hL : Ex.ev s b J c0xUa0L≠0 := by
      have k := RegCert.auto_sound c0xUa0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c0xUa0ok hL (detX_ev lX45.eq lY1.eq lX28.eq lY39.eq lX24.eq lY43.eq)
    push_cast at h; linarith
  · have lX24 : Lift s b J (X.getD 24 0) c0xUa1L c0xUa1X24N c0xUa1X24D c0xUa1X24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : X.getD 24 0=((getRat xs 93 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 24]; rfl
        rw [e]; exact hr.1,c0xUa1X24cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xUa1L c0xUa1X28N c0xUa1X28D c0xUa1X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 28 0=((getRat xs 315 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xUa1X28cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0xUa1L c0xUa1X46N c0xUa1X46D c0xUa1X46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0xUa1X46N,c0xUa1X46D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUa1X46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0xUa1L c0xUa1Y1N c0xUa1Y1D c0xUa1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c0xUa1Y1N,c0xUa1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUa1Y1cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0xUa1L c0xUa1Y39N c0xUa1Y39D c0xUa1Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 39 0=((getRat xs 578 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0xUa1Y39cof⟩
    have lY43 : Lift s b J (Y.getD 43 0) c0xUa1L c0xUa1Y43N c0xUa1Y43D c0xUa1Y43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 43 0=((getRat xs 575 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 43]; rfl
        rw [e]; exact hr.1,c0xUa1Y43cof⟩
    have hL : Ex.ev s b J c0xUa1L≠0 := by
      have k := RegCert.auto_sound c0xUa1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c0xUa1ok hL (detX_ev lX46.eq lY1.eq lX28.eq lY39.eq lX24.eq lY43.eq)
    push_cast at h; linarith
  · have lX25 : Lift s b J (X.getD 25 0) c0xUb0L c0xUb0X25N c0xUb0X25D c0xUb0X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 25 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0xUb0X25cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xUb0L c0xUb0X28N c0xUb0X28D c0xUb0X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 28 0=((getRat xs 315 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xUb0X28cof⟩
    have lX45 : Lift s b J (X.getD 45 0) c0xUb0L c0xUb0X45N c0xUb0X45D c0xUb0X45C :=
      ⟨by
        have e : X.getD 45 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 45]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0xUb0X45N,c0xUb0X45D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUb0X45cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0xUb0L c0xUb0Y1N c0xUb0Y1D c0xUb0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c0xUb0Y1N,c0xUb0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUb0Y1cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0xUb0L c0xUb0Y39N c0xUb0Y39D c0xUb0Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 39 0=((getRat xs 578 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0xUb0Y39cof⟩
    have lY43 : Lift s b J (Y.getD 43 0) c0xUb0L c0xUb0Y43N c0xUb0Y43D c0xUb0Y43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 43 0=((getRat xs 575 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 43]; rfl
        rw [e]; exact hr.1,c0xUb0Y43cof⟩
    have hL : Ex.ev s b J c0xUb0L≠0 := by
      have k := RegCert.auto_sound c0xUb0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2)
    have h := signed_sound B c0xUb0ok hL (detX_ev lX45.eq lY1.eq lX28.eq lY39.eq lX25.eq lY43.eq)
    push_cast at h; linarith
  · have lX25 : Lift s b J (X.getD 25 0) c0xUb1L c0xUb1X25N c0xUb1X25D c0xUb1X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 25 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0xUb1X25cof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xUb1L c0xUb1X28N c0xUb1X28D c0xUb1X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 28 0=((getRat xs 315 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xUb1X28cof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0xUb1L c0xUb1X46N c0xUb1X46D c0xUb1X46C :=
      ⟨by
        have e : X.getD 46 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c0xUb1X46N,c0xUb1X46D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUb1X46cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c0xUb1L c0xUb1Y1N c0xUb1Y1D c0xUb1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c0xUb1Y1N,c0xUb1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c0xUb1Y1cof⟩
    have lY39 : Lift s b J (Y.getD 39 0) c0xUb1L c0xUb1Y39N c0xUb1Y39D c0xUb1Y39C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 39 0=((getRat xs 578 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 39]; rfl
        rw [e]; exact hr.1,c0xUb1Y39cof⟩
    have lY43 : Lift s b J (Y.getD 43 0) c0xUb1L c0xUb1Y43N c0xUb1Y43D c0xUb1Y43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 43 0=((getRat xs 575 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 43]; rfl
        rw [e]; exact hr.1,c0xUb1Y43cof⟩
    have hL : Ex.ev s b J c0xUb1L≠0 := by
      have k := RegCert.auto_sound c0xUb1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2)
    have h := signed_sound B c0xUb1ok hL (detX_ev lX46.eq lY1.eq lX28.eq lY39.eq lX25.eq lY43.eq)
    push_cast at h; linarith
  · have lBy : Lift s b J (1-50050/s^2) c0xbLowL c0xbLowByN c0xbLowByD c0xbLowByC :=
      ⟨by simp [c0xbLowByN,c0xbLowByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xbLowBycof⟩
    have lY40 : Lift s b J (Y.getD 40 0) c0xbLowL c0xbLowY40N c0xbLowY40D c0xbLowY40C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 40 0=((getRat xs 351 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 40]; rfl
        rw [e]; exact hr.1,c0xbLowY40cof⟩
    have lone : Lift s b J (1) c0xbLowL c0xbLowoneN c0xbLowoneD c0xbLowoneC :=
      ⟨by simp [c0xbLowoneN,c0xbLowoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xbLowonecof⟩
    have hL : Ex.ev s b J c0xbLowL≠0 := by
      have k := RegCert.auto_sound c0xbLowLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [c0xbLowByD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xbLowok hL (linX_ev (one:=.mul c0xbLowoneN c0xbLowoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 40 0),(-1,1-50050/s^2)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY40.eq⟩,⟨by trivial,lBy.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY42 : Lift s b J (Y.getD 42 0) c0xH43uL c0xH43uY42N c0xH43uY42D c0xH43uY42C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : Y.getD 42 0=((getRat xs 309 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 42]; rfl
        rw [e]; exact hr.1,c0xH43uY42cof⟩
    have lone : Lift s b J (1) c0xH43uL c0xH43uoneN c0xH43uoneD c0xH43uoneC :=
      ⟨by simp [c0xH43uoneN,c0xH43uoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xH43uonecof⟩
    have hL : Ex.ev s b J c0xH43uL≠0 := by
      have k := RegCert.auto_sound c0xH43uLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).2
    have h := signed_sound B c0xH43uok hL (linX_ev (one:=.mul c0xH43uoneN c0xH43uoneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 42 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY42.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0xDL0L c0xDL0BxN c0xDL0BxD c0xDL0BxC :=
      ⟨by simp [c0xDL0BxN,c0xDL0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xDL0L c0xDL0ByN c0xDL0ByD c0xDL0ByC :=
      ⟨by simp [c0xDL0ByN,c0xDL0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL0Bycof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0xDL0L c0xDL0X25N c0xDL0X25D c0xDL0X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 25 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0xDL0X25cof⟩
    have lY40 : Lift s b J (Y.getD 40 0) c0xDL0L c0xDL0Y40N c0xDL0Y40D c0xDL0Y40C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 40 0=((getRat xs 351 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 40]; rfl
        rw [e]; exact hr.1,c0xDL0Y40cof⟩
    have lone : Lift s b J (1) c0xDL0L c0xDL0oneN c0xDL0oneD c0xDL0oneC :=
      ⟨by simp [c0xDL0oneN,c0xDL0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL0onecof⟩
    have lzero : Lift s b J (0) c0xDL0L c0xDL0zeroN c0xDL0zeroD c0xDL0zeroC :=
      ⟨by simp [c0xDL0zeroN,c0xDL0zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL0zerocof⟩
    have hL : Ex.ev s b J c0xDL0L≠0 := by
      have k := RegCert.auto_sound c0xDL0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c0xDL0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xDL0ok hL (detX_ev lBx.eq lBy.eq lX25.eq lY40.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0xDL1L c0xDL1Bx15N c0xDL1Bx15D c0xDL1Bx15C :=
      ⟨by simp [c0xDL1Bx15N,c0xDL1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xDL1L c0xDL1ByN c0xDL1ByD c0xDL1ByC :=
      ⟨by simp [c0xDL1ByN,c0xDL1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL1Bycof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0xDL1L c0xDL1X25N c0xDL1X25D c0xDL1X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 25 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0xDL1X25cof⟩
    have lY40 : Lift s b J (Y.getD 40 0) c0xDL1L c0xDL1Y40N c0xDL1Y40D c0xDL1Y40C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 40 0=((getRat xs 351 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 40]; rfl
        rw [e]; exact hr.1,c0xDL1Y40cof⟩
    have lone : Lift s b J (1) c0xDL1L c0xDL1oneN c0xDL1oneD c0xDL1oneC :=
      ⟨by simp [c0xDL1oneN,c0xDL1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL1onecof⟩
    have lzero : Lift s b J (0) c0xDL1L c0xDL1zeroN c0xDL1zeroD c0xDL1zeroC :=
      ⟨by simp [c0xDL1zeroN,c0xDL1zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDL1zerocof⟩
    have hL : Ex.ev s b J c0xDL1L≠0 := by
      have k := RegCert.auto_sound c0xDL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c0xDL1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xDL1ok hL (detX_ev lBx15.eq lBy.eq lX25.eq lY40.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0xDR0L c0xDR0BxN c0xDR0BxD c0xDR0BxC :=
      ⟨by simp [c0xDR0BxN,c0xDR0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xDR0L c0xDR0ByN c0xDR0ByD c0xDR0ByC :=
      ⟨by simp [c0xDR0ByN,c0xDR0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR0Bycof⟩
    have lWq : Lift s b J (s/320) c0xDR0L c0xDR0WqN c0xDR0WqD c0xDR0WqC :=
      ⟨by simp [c0xDR0WqN,c0xDR0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR0Wqcof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0xDR0L c0xDR0X25N c0xDR0X25D c0xDR0X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 25 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0xDR0X25cof⟩
    have lY40 : Lift s b J (Y.getD 40 0) c0xDR0L c0xDR0Y40N c0xDR0Y40D c0xDR0Y40C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 40 0=((getRat xs 351 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 40]; rfl
        rw [e]; exact hr.1,c0xDR0Y40cof⟩
    have lone : Lift s b J (1) c0xDR0L c0xDR0oneN c0xDR0oneD c0xDR0oneC :=
      ⟨by simp [c0xDR0oneN,c0xDR0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR0onecof⟩
    have hL : Ex.ev s b J c0xDR0L≠0 := by
      have k := RegCert.auto_sound c0xDR0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c0xDR0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xDR0ok hL (detX_ev lBx.eq lBy.eq lX25.eq lY40.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0xDR1L c0xDR1Bx15N c0xDR1Bx15D c0xDR1Bx15C :=
      ⟨by simp [c0xDR1Bx15N,c0xDR1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xDR1L c0xDR1ByN c0xDR1ByD c0xDR1ByC :=
      ⟨by simp [c0xDR1ByN,c0xDR1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR1Bycof⟩
    have lWq : Lift s b J (s/320) c0xDR1L c0xDR1WqN c0xDR1WqD c0xDR1WqC :=
      ⟨by simp [c0xDR1WqN,c0xDR1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR1Wqcof⟩
    have lX25 : Lift s b J (X.getD 25 0) c0xDR1L c0xDR1X25N c0xDR1X25D c0xDR1X25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 25 0=((getRat xs 580 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 25]; rfl
        rw [e]; exact hr.1,c0xDR1X25cof⟩
    have lY40 : Lift s b J (Y.getD 40 0) c0xDR1L c0xDR1Y40N c0xDR1Y40D c0xDR1Y40C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 40 0=((getRat xs 351 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 40]; rfl
        rw [e]; exact hr.1,c0xDR1Y40cof⟩
    have lone : Lift s b J (1) c0xDR1L c0xDR1oneN c0xDR1oneD c0xDR1oneC :=
      ⟨by simp [c0xDR1oneN,c0xDR1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xDR1onecof⟩
    have hL : Ex.ev s b J c0xDR1L≠0 := by
      have k := RegCert.auto_sound c0xDR1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c0xDR1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xDR1ok hL (detX_ev lBx15.eq lBy.eq lX25.eq lY40.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lX32 : Lift s b J (X.getD 32 0) c0xhdlL c0xhdlX32N c0xhdlX32D c0xhdlX32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : X.getD 32 0=((getRat xs 684 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 32]; rfl
        rw [e]; exact hr.1,c0xhdlX32cof⟩
    have lone : Lift s b J (1) c0xhdlL c0xhdloneN c0xhdloneD c0xhdloneC :=
      ⟨by simp [c0xhdloneN,c0xhdloneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhdlonecof⟩
    have hL : Ex.ev s b J c0xhdlL≠0 := by
      have k := RegCert.auto_sound c0xhdlLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0xhdlok hL (linX_ev (one:=.mul c0xhdloneN c0xhdloneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 32 0),(0,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX32.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lWq : Lift s b J (s/320) c0xhdrL c0xhdrWqN c0xhdrWqD c0xhdrWqC :=
      ⟨by simp [c0xhdrWqN,c0xhdrWqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhdrWqcof⟩
    have lX33 : Lift s b J (X.getD 33 0) c0xhdrL c0xhdrX33N c0xhdrX33D c0xhdrX33C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 33 0=((getRat xs 830 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 33]; rfl
        rw [e]; exact hr.1,c0xhdrX33cof⟩
    have lone : Lift s b J (1) c0xhdrL c0xhdroneN c0xhdroneD c0xhdroneC :=
      ⟨by simp [c0xhdroneN,c0xhdroneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhdronecof⟩
    have hL : Ex.ev s b J c0xhdrL≠0 := by
      have k := RegCert.auto_sound c0xhdrLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0xhdrok hL (linX_ev (one:=.mul c0xhdroneN c0xhdroneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 33 0),(-1,s/320)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX33.eq⟩,⟨by trivial,lWq.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0xCW0L c0xCW0BxN c0xCW0BxD c0xCW0BxC :=
      ⟨by simp [c0xCW0BxN,c0xCW0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xCW0L c0xCW0ByN c0xCW0ByD c0xCW0ByC :=
      ⟨by simp [c0xCW0ByN,c0xCW0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Bycof⟩
    have lWq : Lift s b J (s/320) c0xCW0L c0xCW0WqN c0xCW0WqD c0xCW0WqC :=
      ⟨by simp [c0xCW0WqN,c0xCW0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Wqcof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xCW0L c0xCW0X28N c0xCW0X28D c0xCW0X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 28 0=((getRat xs 315 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xCW0X28cof⟩
    have lY43 : Lift s b J (Y.getD 43 0) c0xCW0L c0xCW0Y43N c0xCW0Y43D c0xCW0Y43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 43 0=((getRat xs 575 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 43]; rfl
        rw [e]; exact hr.1,c0xCW0Y43cof⟩
    have lone : Lift s b J (1) c0xCW0L c0xCW0oneN c0xCW0oneD c0xCW0oneC :=
      ⟨by simp [c0xCW0oneN,c0xCW0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0onecof⟩
    have hL : Ex.ev s b J c0xCW0L≠0 := by
      have k := RegCert.auto_sound c0xCW0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c0xCW0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xCW0ok hL (detX_ev lBx.eq lBy.eq lX28.eq lY43.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0xCW1L c0xCW1Bx15N c0xCW1Bx15D c0xCW1Bx15C :=
      ⟨by simp [c0xCW1Bx15N,c0xCW1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xCW1L c0xCW1ByN c0xCW1ByD c0xCW1ByC :=
      ⟨by simp [c0xCW1ByN,c0xCW1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Bycof⟩
    have lWq : Lift s b J (s/320) c0xCW1L c0xCW1WqN c0xCW1WqD c0xCW1WqC :=
      ⟨by simp [c0xCW1WqN,c0xCW1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Wqcof⟩
    have lX28 : Lift s b J (X.getD 28 0) c0xCW1L c0xCW1X28N c0xCW1X28D c0xCW1X28C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 28 0=((getRat xs 315 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 28]; rfl
        rw [e]; exact hr.1,c0xCW1X28cof⟩
    have lY43 : Lift s b J (Y.getD 43 0) c0xCW1L c0xCW1Y43N c0xCW1Y43D c0xCW1Y43C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 43 0=((getRat xs 575 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 43]; rfl
        rw [e]; exact hr.1,c0xCW1Y43cof⟩
    have lone : Lift s b J (1) c0xCW1L c0xCW1oneN c0xCW1oneD c0xCW1oneC :=
      ⟨by simp [c0xCW1oneN,c0xCW1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1onecof⟩
    have hL : Ex.ev s b J c0xCW1L≠0 := by
      have k := RegCert.auto_sound c0xCW1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c0xCW1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xCW1ok hL (detX_ev lBx15.eq lBy.eq lX28.eq lY43.eq lWq.eq lone.eq)
    push_cast at h; linarith

/-- Range conditions of the other copy test of channel 1. -/
theorem rangesX1 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 3 ∧ getRat args 3≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((360:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    0<ArtGallery.det (X.getD 55 0,Y.getD 1 0) (X.getD 15 0,Y.getD 21 0) (X.getD 11 0,Y.getD 25 0) ∧
    0<ArtGallery.det (X.getD 56 0,Y.getD 1 0) (X.getD 15 0,Y.getD 21 0) (X.getD 11 0,Y.getD 25 0) ∧
    ArtGallery.det (X.getD 55 0,Y.getD 1 0) (X.getD 15 0,Y.getD 21 0) (X.getD 12 0,Y.getD 25 0)<0 ∧
    ArtGallery.det (X.getD 56 0,Y.getD 1 0) (X.getD 15 0,Y.getD 21 0) (X.getD 12 0,Y.getD 25 0)<0 ∧
    0<(1:ℝ)*(Y.getD 22 0)+(-1:ℝ)*(1-50050/s^2) ∧
    0<(3:ℝ)*(Y.getD 24 0)+(-7:ℝ)*(1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 12 0,Y.getD 22 0) (0,1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 12 0,Y.getD 22 0) (0,1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 12 0,Y.getD 22 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 12 0,Y.getD 22 0) (s/320,1)<0 ∧
    X.getD 32 0=(0:ℝ)/1 ∧
    X.getD 33 0=s/320 ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 15 0,Y.getD 25 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 15 0,Y.getD 25 0) (s/320,1)<0 := by
  intro s J Q b X Y
  have Xdef : X=(grid template args false).map (fun q : ℚ => (q:ℝ)) := rfl
  have Ydef : Y=(grid template args true).map (fun q : ℚ => (q:ℝ)) := rfl
  have hs : (0:ℝ)<s := by simp only [s]; exact_mod_cast m.pos
  have hs1 : s≤(((1/65:ℚ):ℚ):ℝ) := by simp only [s]; exact_mod_cast m.upper
  have hJ' : (0:ℝ)≤J ∧ J≤1 := by simp only [J]; exact ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  have hQ' : (0:ℝ)≤Q ∧ Q≤1 := by simp only [Q]; exact ⟨by exact_mod_cast hQ.1,by exact_mod_cast hQ.2⟩
  have B : PolyBox.Box (1/65:ℚ) (257/715:ℚ) (4289/11830:ℚ) s b J := by
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
        have e : X.getD 11 0=((getRat xs 236 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 11]; rfl
        rw [e]; exact hr.1,c1xUa0X11cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUa0L c1xUa0X15N c1xUa0X15D c1xUa0X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 283 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUa0X15cof⟩
    have lX55 : Lift s b J (X.getD 55 0) c1xUa0L c1xUa0X55N c1xUa0X55D c1xUa0X55C :=
      ⟨by
        have e : X.getD 55 0=((((axisOf template false).coordsQ (getRat args 0)).getD 12 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 55]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1xUa0X55N,c1xUa0X55D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa0X55cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUa0L c1xUa0Y1N c1xUa0Y1D c1xUa0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c1xUa0Y1N,c1xUa0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa0Y1cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xUa0L c1xUa0Y21N c1xUa0Y21D c1xUa0Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 21 0=((getRat xs 367 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xUa0Y21cof⟩
    have lY25 : Lift s b J (Y.getD 25 0) c1xUa0L c1xUa0Y25N c1xUa0Y25D c1xUa0Y25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 25 0=((getRat xs 364 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 25]; rfl
        rw [e]; exact hr.1,c1xUa0Y25cof⟩
    have hL : Ex.ev s b J c1xUa0L≠0 := by
      have k := RegCert.auto_sound c1xUa0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUa0ok hL (detX_ev lX55.eq lY1.eq lX15.eq lY21.eq lX11.eq lY25.eq)
    push_cast at h; linarith
  · have lX11 : Lift s b J (X.getD 11 0) c1xUa1L c1xUa1X11N c1xUa1X11D c1xUa1X11C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : X.getD 11 0=((getRat xs 236 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 11]; rfl
        rw [e]; exact hr.1,c1xUa1X11cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUa1L c1xUa1X15N c1xUa1X15D c1xUa1X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 283 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUa1X15cof⟩
    have lX56 : Lift s b J (X.getD 56 0) c1xUa1L c1xUa1X56N c1xUa1X56D c1xUa1X56C :=
      ⟨by
        have e : X.getD 56 0=((((axisOf template false).coordsQ (getRat args 0)).getD 13 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 56]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1xUa1X56N,c1xUa1X56D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa1X56cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUa1L c1xUa1Y1N c1xUa1Y1D c1xUa1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c1xUa1Y1N,c1xUa1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUa1Y1cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xUa1L c1xUa1Y21N c1xUa1Y21D c1xUa1Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 21 0=((getRat xs 367 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xUa1Y21cof⟩
    have lY25 : Lift s b J (Y.getD 25 0) c1xUa1L c1xUa1Y25N c1xUa1Y25D c1xUa1Y25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 25 0=((getRat xs 364 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 25]; rfl
        rw [e]; exact hr.1,c1xUa1Y25cof⟩
    have hL : Ex.ev s b J c1xUa1L≠0 := by
      have k := RegCert.auto_sound c1xUa1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUa1ok hL (detX_ev lX56.eq lY1.eq lX15.eq lY21.eq lX11.eq lY25.eq)
    push_cast at h; linarith
  · have lX12 : Lift s b J (X.getD 12 0) c1xUb0L c1xUb0X12N c1xUb0X12D c1xUb0X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xUb0X12cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUb0L c1xUb0X15N c1xUb0X15D c1xUb0X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 283 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUb0X15cof⟩
    have lX55 : Lift s b J (X.getD 55 0) c1xUb0L c1xUb0X55N c1xUb0X55D c1xUb0X55C :=
      ⟨by
        have e : X.getD 55 0=((((axisOf template false).coordsQ (getRat args 0)).getD 12 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 55]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1xUb0X55N,c1xUb0X55D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb0X55cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUb0L c1xUb0Y1N c1xUb0Y1D c1xUb0Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c1xUb0Y1N,c1xUb0Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb0Y1cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xUb0L c1xUb0Y21N c1xUb0Y21D c1xUb0Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 21 0=((getRat xs 367 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xUb0Y21cof⟩
    have lY25 : Lift s b J (Y.getD 25 0) c1xUb0L c1xUb0Y25N c1xUb0Y25D c1xUb0Y25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 25 0=((getRat xs 364 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 25]; rfl
        rw [e]; exact hr.1,c1xUb0Y25cof⟩
    have hL : Ex.ev s b J c1xUb0L≠0 := by
      have k := RegCert.auto_sound c1xUb0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUb0ok hL (detX_ev lX55.eq lY1.eq lX15.eq lY21.eq lX12.eq lY25.eq)
    push_cast at h; linarith
  · have lX12 : Lift s b J (X.getD 12 0) c1xUb1L c1xUb1X12N c1xUb1X12D c1xUb1X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xUb1X12cof⟩
    have lX15 : Lift s b J (X.getD 15 0) c1xUb1L c1xUb1X15N c1xUb1X15D c1xUb1X15C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 15 0=((getRat xs 283 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xUb1X15cof⟩
    have lX56 : Lift s b J (X.getD 56 0) c1xUb1L c1xUb1X56N c1xUb1X56D c1xUb1X56C :=
      ⟨by
        have e : X.getD 56 0=((((axisOf template false).coordsQ (getRat args 0)).getD 13 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 56]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.xAxis,Gap.valR,evalR,c1xUb1X56N,c1xUb1X56D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb1X56cof⟩
    have lY1 : Lift s b J (Y.getD 1 0) c1xUb1L c1xUb1Y1N c1xUb1Y1D c1xUb1Y1C :=
      ⟨by
        have e : Y.getD 1 0=((((axisOf template true).coordsQ (getRat args 0)).getD 1 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 1]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.InvLe.yAxis,Gap.valR,evalR,c1xUb1Y1N,c1xUb1Y1D,Ex.ev,ev3,ev2,ev1]
        ring,c1xUb1Y1cof⟩
    have lY21 : Lift s b J (Y.getD 21 0) c1xUb1L c1xUb1Y21N c1xUb1Y21D c1xUb1Y21C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 21 0=((getRat xs 367 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 21]; rfl
        rw [e]; exact hr.1,c1xUb1Y21cof⟩
    have lY25 : Lift s b J (Y.getD 25 0) c1xUb1L c1xUb1Y25N c1xUb1Y25D c1xUb1Y25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 25 0=((getRat xs 364 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 25]; rfl
        rw [e]; exact hr.1,c1xUb1Y25cof⟩
    have hL : Ex.ev s b J c1xUb1L≠0 := by
      have k := RegCert.auto_sound c1xUb1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := signed_sound B c1xUb1ok hL (detX_ev lX56.eq lY1.eq lX15.eq lY21.eq lX12.eq lY25.eq)
    push_cast at h; linarith
  · have lBy : Lift s b J (1-50050/s^2) c1xbLowL c1xbLowByN c1xbLowByD c1xbLowByC :=
      ⟨by simp [c1xbLowByN,c1xbLowByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xbLowBycof⟩
    have lY22 : Lift s b J (Y.getD 22 0) c1xbLowL c1xbLowY22N c1xbLowY22D c1xbLowY22C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 22 0=((getRat xs 285 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 22]; rfl
        rw [e]; exact hr.1,c1xbLowY22cof⟩
    have lone : Lift s b J (1) c1xbLowL c1xbLowoneN c1xbLowoneD c1xbLowoneC :=
      ⟨by simp [c1xbLowoneN,c1xbLowoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xbLowonecof⟩
    have hL : Ex.ev s b J c1xbLowL≠0 := by
      have k := RegCert.auto_sound c1xbLowLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [c1xbLowByD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xbLowok hL (linX_ev (one:=.mul c1xbLowoneN c1xbLowoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 22 0),(-1,1-50050/s^2)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY22.eq⟩,⟨by trivial,lBy.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY24 : Lift s b J (Y.getD 24 0) c1xH43uL c1xH43uY24N c1xH43uY24D c1xH43uY24C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : Y.getD 24 0=((getRat xs 277 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 24]; rfl
        rw [e]; exact hr.1,c1xH43uY24cof⟩
    have lone : Lift s b J (1) c1xH43uL c1xH43uoneN c1xH43uoneD c1xH43uoneC :=
      ⟨by simp [c1xH43uoneN,c1xH43uoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xH43uonecof⟩
    have hL : Ex.ev s b J c1xH43uL≠0 := by
      have k := RegCert.auto_sound c1xH43uLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).2
    have h := signed_sound B c1xH43uok hL (linX_ev (one:=.mul c1xH43uoneN c1xH43uoneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 24 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY24.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c1xDL0L c1xDL0BxN c1xDL0BxD c1xDL0BxC :=
      ⟨by simp [c1xDL0BxN,c1xDL0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xDL0L c1xDL0ByN c1xDL0ByD c1xDL0ByC :=
      ⟨by simp [c1xDL0ByN,c1xDL0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0Bycof⟩
    have lX12 : Lift s b J (X.getD 12 0) c1xDL0L c1xDL0X12N c1xDL0X12D c1xDL0X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDL0X12cof⟩
    have lY22 : Lift s b J (Y.getD 22 0) c1xDL0L c1xDL0Y22N c1xDL0Y22D c1xDL0Y22C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 22 0=((getRat xs 285 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 22]; rfl
        rw [e]; exact hr.1,c1xDL0Y22cof⟩
    have lone : Lift s b J (1) c1xDL0L c1xDL0oneN c1xDL0oneD c1xDL0oneC :=
      ⟨by simp [c1xDL0oneN,c1xDL0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0onecof⟩
    have lzero : Lift s b J (0) c1xDL0L c1xDL0zeroN c1xDL0zeroD c1xDL0zeroC :=
      ⟨by simp [c1xDL0zeroN,c1xDL0zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL0zerocof⟩
    have hL : Ex.ev s b J c1xDL0L≠0 := by
      have k := RegCert.auto_sound c1xDL0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDL0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDL0ok hL (detX_ev lBx.eq lBy.eq lX12.eq lY22.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c1xDL1L c1xDL1Bx15N c1xDL1Bx15D c1xDL1Bx15C :=
      ⟨by simp [c1xDL1Bx15N,c1xDL1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xDL1L c1xDL1ByN c1xDL1ByD c1xDL1ByC :=
      ⟨by simp [c1xDL1ByN,c1xDL1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1Bycof⟩
    have lX12 : Lift s b J (X.getD 12 0) c1xDL1L c1xDL1X12N c1xDL1X12D c1xDL1X12C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 12 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDL1X12cof⟩
    have lY22 : Lift s b J (Y.getD 22 0) c1xDL1L c1xDL1Y22N c1xDL1Y22D c1xDL1Y22C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 22 0=((getRat xs 285 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 22]; rfl
        rw [e]; exact hr.1,c1xDL1Y22cof⟩
    have lone : Lift s b J (1) c1xDL1L c1xDL1oneN c1xDL1oneD c1xDL1oneC :=
      ⟨by simp [c1xDL1oneN,c1xDL1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1onecof⟩
    have lzero : Lift s b J (0) c1xDL1L c1xDL1zeroN c1xDL1zeroD c1xDL1zeroC :=
      ⟨by simp [c1xDL1zeroN,c1xDL1zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDL1zerocof⟩
    have hL : Ex.ev s b J c1xDL1L≠0 := by
      have k := RegCert.auto_sound c1xDL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDL1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDL1ok hL (detX_ev lBx15.eq lBy.eq lX12.eq lY22.eq lzero.eq lone.eq)
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
        have e : X.getD 12 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDR0X12cof⟩
    have lY22 : Lift s b J (Y.getD 22 0) c1xDR0L c1xDR0Y22N c1xDR0Y22D c1xDR0Y22C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 22 0=((getRat xs 285 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 22]; rfl
        rw [e]; exact hr.1,c1xDR0Y22cof⟩
    have lone : Lift s b J (1) c1xDR0L c1xDR0oneN c1xDR0oneD c1xDR0oneC :=
      ⟨by simp [c1xDR0oneN,c1xDR0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR0onecof⟩
    have hL : Ex.ev s b J c1xDR0L≠0 := by
      have k := RegCert.auto_sound c1xDR0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDR0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDR0ok hL (detX_ev lBx.eq lBy.eq lX12.eq lY22.eq lWq.eq lone.eq)
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
        have e : X.getD 12 0=((getRat xs 369 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 12]; rfl
        rw [e]; exact hr.1,c1xDR1X12cof⟩
    have lY22 : Lift s b J (Y.getD 22 0) c1xDR1L c1xDR1Y22N c1xDR1Y22D c1xDR1Y22C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 22 0=((getRat xs 285 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 22]; rfl
        rw [e]; exact hr.1,c1xDR1Y22cof⟩
    have lone : Lift s b J (1) c1xDR1L c1xDR1oneN c1xDR1oneD c1xDR1oneC :=
      ⟨by simp [c1xDR1oneN,c1xDR1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xDR1onecof⟩
    have hL : Ex.ev s b J c1xDR1L≠0 := by
      have k := RegCert.auto_sound c1xDR1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c1xDR1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xDR1ok hL (detX_ev lBx15.eq lBy.eq lX12.eq lY22.eq lWq.eq lone.eq)
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
        have e : X.getD 15 0=((getRat xs 283 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xCW0X15cof⟩
    have lY25 : Lift s b J (Y.getD 25 0) c1xCW0L c1xCW0Y25N c1xCW0Y25D c1xCW0Y25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 25 0=((getRat xs 364 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 25]; rfl
        rw [e]; exact hr.1,c1xCW0Y25cof⟩
    have lone : Lift s b J (1) c1xCW0L c1xCW0oneN c1xCW0oneD c1xCW0oneC :=
      ⟨by simp [c1xCW0oneN,c1xCW0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0onecof⟩
    have hL : Ex.ev s b J c1xCW0L≠0 := by
      have k := RegCert.auto_sound c1xCW0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c1xCW0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xCW0ok hL (detX_ev lBx.eq lBy.eq lX15.eq lY25.eq lWq.eq lone.eq)
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
        have e : X.getD 15 0=((getRat xs 283 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 15]; rfl
        rw [e]; exact hr.1,c1xCW1X15cof⟩
    have lY25 : Lift s b J (Y.getD 25 0) c1xCW1L c1xCW1Y25N c1xCW1Y25D c1xCW1Y25C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 25 0=((getRat xs 364 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 25]; rfl
        rw [e]; exact hr.1,c1xCW1Y25cof⟩
    have lone : Lift s b J (1) c1xCW1L c1xCW1oneN c1xCW1oneD c1xCW1oneC :=
      ⟨by simp [c1xCW1oneN,c1xCW1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1onecof⟩
    have hL : Ex.ev s b J c1xCW1L≠0 := by
      have k := RegCert.auto_sound c1xCW1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c1xCW1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xCW1ok hL (detX_ev lBx15.eq lBy.eq lX15.eq lY25.eq lWq.eq lone.eq)
    push_cast at h; linarith

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_360
end
