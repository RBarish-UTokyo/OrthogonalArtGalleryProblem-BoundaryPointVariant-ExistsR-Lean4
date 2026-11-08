module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C0XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C0XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C0XS1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C0XHold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C0XI0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C0XI1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XS1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XHold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XI0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C1XI1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C2XDefs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C2XS0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C2XHold
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C2XI0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C2XI1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C2XI2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520.C2XI3

/-! Range conditions of the other copy test of each channel of profile `Shifted_40_200_520`
(generated), for the completeness proof. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Shifted_40_200_520
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
    let b : ℝ := ((((40:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    X.getD 61 0=(301:ℝ)/2 ∧
    X.getD 64 0=X.getD 63 0+3/2*(1-Y.getD 6 0)/(50050/s^2) ∧
    0<ArtGallery.det (X.getD 64 0,Y.getD 6 0) (X.getD 61 0,Y.getD 20 0) (X.getD 47 0,Y.getD 65 0) ∧
    ArtGallery.det (X.getD 63 0,Y.getD 6 0) (X.getD 61 0,Y.getD 20 0) (X.getD 48 0,Y.getD 65 0)<0 ∧
    0<(1:ℝ)*(50050/s^2)+(-1:ℝ)*(Y.getD 66 0)+(1:ℝ)*(1) ∧
    0<(3:ℝ)*(Y.getD 65 0)+(-7:ℝ)*(1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 46 0,Y.getD 71 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 46 0,Y.getD 71 0) (s/320,1)<0 := by
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
  have hin : ∀ k P d, (k,P,d)∈c0ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c0ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c0xhold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lX61 : Lift s b J (X.getD 61 0) c0xhwxL c0xhwxX61N c0xhwxX61D c0xhwxX61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1213 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c0xhwxX61cof⟩
    have lone : Lift s b J (1) c0xhwxL c0xhwxoneN c0xhwxoneD c0xhwxoneC :=
      ⟨by simp [c0xhwxoneN,c0xhwxoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhwxonecof⟩
    have hL : Ex.ev s b J c0xhwxL≠0 := by
      have k := RegCert.auto_sound c0xhwxLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c0xhwxok hL (linX_ev (one:=.mul c0xhwxoneN c0xhwxoneC) (lone.eq.trans (one_mul _)) _ [(2,X.getD 61 0),(-301,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX61.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX63 : Lift s b J (X.getD 63 0) c0xhrbL c0xhrbX63N c0xhrbX63D c0xhrbX63C :=
      ⟨by
        have e : X.getD 63 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 63]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c0xhrbX63N,c0xhrbX63D,Ex.ev,ev3,ev2,ev1]
        ring,c0xhrbX63cof⟩
    have lX64 : Lift s b J (X.getD 64 0) c0xhrbL c0xhrbX64N c0xhrbX64D c0xhrbX64C :=
      ⟨by
        have e : X.getD 64 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 64]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c0xhrbX64N,c0xhrbX64D,Ex.ev,ev3,ev2,ev1]
        ring,c0xhrbX64cof⟩
    have lY6 : Lift s b J (Y.getD 6 0) c0xhrbL c0xhrbY6N c0xhrbY6D c0xhrbY6C :=
      ⟨by
        have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 6]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c0xhrbY6N,c0xhrbY6D,Ex.ev,ev3,ev2,ev1]
        ring,c0xhrbY6cof⟩
    have lone : Lift s b J (1) c0xhrbL c0xhrboneN c0xhrboneD c0xhrboneC :=
      ⟨by simp [c0xhrboneN,c0xhrboneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhrbonecof⟩
    have lvD : Lift s b J (50050/s^2) c0xhrbL c0xhrbvDN c0xhrbvDD c0xhrbvDC :=
      ⟨by simp [c0xhrbvDN,c0xhrbvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xhrbvDcof⟩
    have hL : Ex.ev s b J c0xhrbL≠0 := by
      have k := RegCert.auto_sound c0xhrbLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (by simp [c0xhrbvDD,Ex.ev,ev3,ev2,ev1]; positivity) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := zero_of_check c0xhrbok hL (spotX_ev lX64.eq lX63.eq lvD.eq lY6.eq (lone.eq.trans (one_mul _)))
    have hs2 : (50050:ℝ)/s^2≠0 := by positivity
    field_simp at h ⊢; linarith
  · have lX47 : Lift s b J (X.getD 47 0) c0xL1L c0xL1X47N c0xL1X47D c0xL1X47C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 47 0=((getRat xs 287 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 47]; rfl
        rw [e]; exact hr.1,c0xL1X47cof⟩
    have lX61 : Lift s b J (X.getD 61 0) c0xL1L c0xL1X61N c0xL1X61D c0xL1X61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1213 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c0xL1X61cof⟩
    have lX64 : Lift s b J (X.getD 64 0) c0xL1L c0xL1X64N c0xL1X64D c0xL1X64C :=
      ⟨by
        have e : X.getD 64 0=((((axisOf template false).coordsQ (getRat args 0)).getD 3 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 64]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c0xL1X64N,c0xL1X64D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL1X64cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c0xL1L c0xL1Y20N c0xL1Y20D c0xL1Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1198 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c0xL1Y20cof⟩
    have lY6 : Lift s b J (Y.getD 6 0) c0xL1L c0xL1Y6N c0xL1Y6D c0xL1Y6C :=
      ⟨by
        have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 6]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c0xL1Y6N,c0xL1Y6D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL1Y6cof⟩
    have lY65 : Lift s b J (Y.getD 65 0) c0xL1L c0xL1Y65N c0xL1Y65D c0xL1Y65C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 65 0=((getRat xs 968 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 65]; rfl
        rw [e]; exact hr.1,c0xL1Y65cof⟩
    have hL : Ex.ev s b J c0xL1L≠0 := by
      have k := RegCert.auto_sound c0xL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).2
    have h := signed_sound B c0xL1ok hL (detX_ev lX64.eq lY6.eq lX61.eq lY20.eq lX47.eq lY65.eq)
    push_cast at h; linarith
  · have lX48 : Lift s b J (X.getD 48 0) c0xL2L c0xL2X48N c0xL2X48D c0xL2X48C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : X.getD 48 0=((getRat xs 347 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 48]; rfl
        rw [e]; exact hr.1,c0xL2X48cof⟩
    have lX61 : Lift s b J (X.getD 61 0) c0xL2L c0xL2X61N c0xL2X61D c0xL2X61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1213 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c0xL2X61cof⟩
    have lX63 : Lift s b J (X.getD 63 0) c0xL2L c0xL2X63N c0xL2X63D c0xL2X63C :=
      ⟨by
        have e : X.getD 63 0=((((axisOf template false).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 63]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c0xL2X63N,c0xL2X63D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL2X63cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c0xL2L c0xL2Y20N c0xL2Y20D c0xL2Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1198 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c0xL2Y20cof⟩
    have lY6 : Lift s b J (Y.getD 6 0) c0xL2L c0xL2Y6N c0xL2Y6D c0xL2Y6C :=
      ⟨by
        have e : Y.getD 6 0=((((axisOf template true).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 6]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c0xL2Y6N,c0xL2Y6D,Ex.ev,ev3,ev2,ev1]
        ring,c0xL2Y6cof⟩
    have lY65 : Lift s b J (Y.getD 65 0) c0xL2L c0xL2Y65N c0xL2Y65D c0xL2Y65C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 65 0=((getRat xs 968 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 65]; rfl
        rw [e]; exact hr.1,c0xL2Y65cof⟩
    have hL : Ex.ev s b J c0xL2L≠0 := by
      have k := RegCert.auto_sound c0xL2Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2
    have h := signed_sound B c0xL2ok hL (detX_ev lX63.eq lY6.eq lX61.eq lY20.eq lX48.eq lY65.eq)
    push_cast at h; linarith
  · have lY66 : Lift s b J (Y.getD 66 0) c0xdeepL c0xdeepY66N c0xdeepY66D c0xdeepY66C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : Y.getD 66 0=((getRat xs 321 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 66]; rfl
        rw [e]; exact hr.1,c0xdeepY66cof⟩
    have lone : Lift s b J (1) c0xdeepL c0xdeeponeN c0xdeeponeD c0xdeeponeC :=
      ⟨by simp [c0xdeeponeN,c0xdeeponeD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xdeeponecof⟩
    have lvD : Lift s b J (50050/s^2) c0xdeepL c0xdeepvDN c0xdeepvDD c0xdeepvDC :=
      ⟨by simp [c0xdeepvDN,c0xdeepvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xdeepvDcof⟩
    have hL : Ex.ev s b J c0xdeepL≠0 := by
      have k := RegCert.auto_sound c0xdeepLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2 (by simp [c0xdeepvDD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xdeepok hL (linX_ev (one:=.mul c0xdeeponeN c0xdeeponeC) (lone.eq.trans (one_mul _)) _ [(1,50050/s^2),(-1,Y.getD 66 0),(1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lvD.eq⟩,⟨by trivial,lY66.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY65 : Lift s b J (Y.getD 65 0) c0xH43L c0xH43Y65N c0xH43Y65D c0xH43Y65C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 65 0=((getRat xs 968 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 65]; rfl
        rw [e]; exact hr.1,c0xH43Y65cof⟩
    have lone : Lift s b J (1) c0xH43L c0xH43oneN c0xH43oneD c0xH43oneC :=
      ⟨by simp [c0xH43oneN,c0xH43oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xH43onecof⟩
    have hL : Ex.ev s b J c0xH43L≠0 := by
      have k := RegCert.auto_sound c0xH43Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2
    have h := signed_sound B c0xH43ok hL (linX_ev (one:=.mul c0xH43oneN c0xH43oneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 65 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY65.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c0xCW0L c0xCW0BxN c0xCW0BxD c0xCW0BxC :=
      ⟨by simp [c0xCW0BxN,c0xCW0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xCW0L c0xCW0ByN c0xCW0ByD c0xCW0ByC :=
      ⟨by simp [c0xCW0ByN,c0xCW0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Bycof⟩
    have lWq : Lift s b J (s/320) c0xCW0L c0xCW0WqN c0xCW0WqD c0xCW0WqC :=
      ⟨by simp [c0xCW0WqN,c0xCW0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0Wqcof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0xCW0L c0xCW0X46N c0xCW0X46D c0xCW0X46C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 46 0=((getRat xs 455 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e]; exact hr.1,c0xCW0X46cof⟩
    have lY71 : Lift s b J (Y.getD 71 0) c0xCW0L c0xCW0Y71N c0xCW0Y71D c0xCW0Y71C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 71 0=((getRat xs 964 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 71]; rfl
        rw [e]; exact hr.1,c0xCW0Y71cof⟩
    have lone : Lift s b J (1) c0xCW0L c0xCW0oneN c0xCW0oneD c0xCW0oneC :=
      ⟨by simp [c0xCW0oneN,c0xCW0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW0onecof⟩
    have hL : Ex.ev s b J c0xCW0L≠0 := by
      have k := RegCert.auto_sound c0xCW0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [c0xCW0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xCW0ok hL (detX_ev lBx.eq lBy.eq lX46.eq lY71.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c0xCW1L c0xCW1Bx15N c0xCW1Bx15D c0xCW1Bx15C :=
      ⟨by simp [c0xCW1Bx15N,c0xCW1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c0xCW1L c0xCW1ByN c0xCW1ByD c0xCW1ByC :=
      ⟨by simp [c0xCW1ByN,c0xCW1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Bycof⟩
    have lWq : Lift s b J (s/320) c0xCW1L c0xCW1WqN c0xCW1WqD c0xCW1WqC :=
      ⟨by simp [c0xCW1WqN,c0xCW1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1Wqcof⟩
    have lX46 : Lift s b J (X.getD 46 0) c0xCW1L c0xCW1X46N c0xCW1X46D c0xCW1X46C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 46 0=((getRat xs 455 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 46]; rfl
        rw [e]; exact hr.1,c0xCW1X46cof⟩
    have lY71 : Lift s b J (Y.getD 71 0) c0xCW1L c0xCW1Y71N c0xCW1Y71D c0xCW1Y71C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 71 0=((getRat xs 964 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 71]; rfl
        rw [e]; exact hr.1,c0xCW1Y71cof⟩
    have lone : Lift s b J (1) c0xCW1L c0xCW1oneN c0xCW1oneD c0xCW1oneC :=
      ⟨by simp [c0xCW1oneN,c0xCW1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c0xCW1onecof⟩
    have hL : Ex.ev s b J c0xCW1L≠0 := by
      have k := RegCert.auto_sound c0xCW1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [c0xCW1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c0xCW1ok hL (detX_ev lBx15.eq lBy.eq lX46.eq lY71.eq lWq.eq lone.eq)
    push_cast at h; linarith

/-- Range conditions of the other copy test of channel 1. -/
theorem rangesX1 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 3 ∧ getRat args 3≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((200:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    X.getD 61 0=(301:ℝ)/2 ∧
    X.getD 68 0=X.getD 67 0+3/2*(1-Y.getD 4 0)/(50050/s^2) ∧
    0<ArtGallery.det (X.getD 68 0,Y.getD 4 0) (X.getD 61 0,Y.getD 20 0) (X.getD 34 0,Y.getD 47 0) ∧
    ArtGallery.det (X.getD 67 0,Y.getD 4 0) (X.getD 61 0,Y.getD 20 0) (X.getD 35 0,Y.getD 47 0)<0 ∧
    0<(1:ℝ)*(50050/s^2)+(-1:ℝ)*(Y.getD 48 0)+(1:ℝ)*(1) ∧
    0<(3:ℝ)*(Y.getD 47 0)+(-7:ℝ)*(1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 33 0,Y.getD 53 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 33 0,Y.getD 53 0) (s/320,1)<0 := by
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
  have H := c1xhold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lX61 : Lift s b J (X.getD 61 0) c1xhwxL c1xhwxX61N c1xhwxX61D c1xhwxX61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1213 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c1xhwxX61cof⟩
    have lone : Lift s b J (1) c1xhwxL c1xhwxoneN c1xhwxoneD c1xhwxoneC :=
      ⟨by simp [c1xhwxoneN,c1xhwxoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xhwxonecof⟩
    have hL : Ex.ev s b J c1xhwxL≠0 := by
      have k := RegCert.auto_sound c1xhwxLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c1xhwxok hL (linX_ev (one:=.mul c1xhwxoneN c1xhwxoneC) (lone.eq.trans (one_mul _)) _ [(2,X.getD 61 0),(-301,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX61.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lX67 : Lift s b J (X.getD 67 0) c1xhrbL c1xhrbX67N c1xhrbX67D c1xhrbX67C :=
      ⟨by
        have e : X.getD 67 0=((((axisOf template false).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 67]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c1xhrbX67N,c1xhrbX67D,Ex.ev,ev3,ev2,ev1]
        ring,c1xhrbX67cof⟩
    have lX68 : Lift s b J (X.getD 68 0) c1xhrbL c1xhrbX68N c1xhrbX68D c1xhrbX68C :=
      ⟨by
        have e : X.getD 68 0=((((axisOf template false).coordsQ (getRat args 0)).getD 7 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 68]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c1xhrbX68N,c1xhrbX68D,Ex.ev,ev3,ev2,ev1]
        ring,c1xhrbX68cof⟩
    have lY4 : Lift s b J (Y.getD 4 0) c1xhrbL c1xhrbY4N c1xhrbY4D c1xhrbY4C :=
      ⟨by
        have e : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 4]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c1xhrbY4N,c1xhrbY4D,Ex.ev,ev3,ev2,ev1]
        ring,c1xhrbY4cof⟩
    have lone : Lift s b J (1) c1xhrbL c1xhrboneN c1xhrboneD c1xhrboneC :=
      ⟨by simp [c1xhrboneN,c1xhrboneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xhrbonecof⟩
    have lvD : Lift s b J (50050/s^2) c1xhrbL c1xhrbvDN c1xhrbvDD c1xhrbvDC :=
      ⟨by simp [c1xhrbvDN,c1xhrbvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xhrbvDcof⟩
    have hL : Ex.ev s b J c1xhrbL≠0 := by
      have k := RegCert.auto_sound c1xhrbLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (by simp [c1xhrbvDD,Ex.ev,ev3,ev2,ev1]; positivity) (by simp [Ex.ev,ev3,ev2,ev1]))
    have h := zero_of_check c1xhrbok hL (spotX_ev lX68.eq lX67.eq lvD.eq lY4.eq (lone.eq.trans (one_mul _)))
    have hs2 : (50050:ℝ)/s^2≠0 := by positivity
    field_simp at h ⊢; linarith
  · have lX34 : Lift s b J (X.getD 34 0) c1xL1L c1xL1X34N c1xL1X34D c1xL1X34C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 34 0=((getRat xs 239 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 34]; rfl
        rw [e]; exact hr.1,c1xL1X34cof⟩
    have lX61 : Lift s b J (X.getD 61 0) c1xL1L c1xL1X61N c1xL1X61D c1xL1X61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1213 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c1xL1X61cof⟩
    have lX68 : Lift s b J (X.getD 68 0) c1xL1L c1xL1X68N c1xL1X68D c1xL1X68C :=
      ⟨by
        have e : X.getD 68 0=((((axisOf template false).coordsQ (getRat args 0)).getD 7 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 68]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c1xL1X68N,c1xL1X68D,Ex.ev,ev3,ev2,ev1]
        ring,c1xL1X68cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c1xL1L c1xL1Y20N c1xL1Y20D c1xL1Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1198 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1xL1Y20cof⟩
    have lY4 : Lift s b J (Y.getD 4 0) c1xL1L c1xL1Y4N c1xL1Y4D c1xL1Y4C :=
      ⟨by
        have e : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 4]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c1xL1Y4N,c1xL1Y4D,Ex.ev,ev3,ev2,ev1]
        ring,c1xL1Y4cof⟩
    have lY47 : Lift s b J (Y.getD 47 0) c1xL1L c1xL1Y47N c1xL1Y47D c1xL1Y47C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 47 0=((getRat xs 748 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 47]; rfl
        rw [e]; exact hr.1,c1xL1Y47cof⟩
    have hL : Ex.ev s b J c1xL1L≠0 := by
      have k := RegCert.auto_sound c1xL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2
    have h := signed_sound B c1xL1ok hL (detX_ev lX68.eq lY4.eq lX61.eq lY20.eq lX34.eq lY47.eq)
    push_cast at h; linarith
  · have lX35 : Lift s b J (X.getD 35 0) c1xL2L c1xL2X35N c1xL2X35D c1xL2X35C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : X.getD 35 0=((getRat xs 77 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 35]; rfl
        rw [e]; exact hr.1,c1xL2X35cof⟩
    have lX61 : Lift s b J (X.getD 61 0) c1xL2L c1xL2X61N c1xL2X61D c1xL2X61C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 61 0=((getRat xs 1213 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 61]; rfl
        rw [e]; exact hr.1,c1xL2X61cof⟩
    have lX67 : Lift s b J (X.getD 67 0) c1xL2L c1xL2X67N c1xL2X67D c1xL2X67C :=
      ⟨by
        have e : X.getD 67 0=((((axisOf template false).coordsQ (getRat args 0)).getD 6 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 67]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c1xL2X67N,c1xL2X67D,Ex.ev,ev3,ev2,ev1]
        ring,c1xL2X67cof⟩
    have lY20 : Lift s b J (Y.getD 20 0) c1xL2L c1xL2Y20N c1xL2Y20D c1xL2Y20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : Y.getD 20 0=((getRat xs 1198 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 20]; rfl
        rw [e]; exact hr.1,c1xL2Y20cof⟩
    have lY4 : Lift s b J (Y.getD 4 0) c1xL2L c1xL2Y4N c1xL2Y4D c1xL2Y4C :=
      ⟨by
        have e : Y.getD 4 0=((((axisOf template true).coordsQ (getRat args 0)).getD 4 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 4]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c1xL2Y4N,c1xL2Y4D,Ex.ev,ev3,ev2,ev1]
        ring,c1xL2Y4cof⟩
    have lY47 : Lift s b J (Y.getD 47 0) c1xL2L c1xL2Y47N c1xL2Y47D c1xL2Y47C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 47 0=((getRat xs 748 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 47]; rfl
        rw [e]; exact hr.1,c1xL2Y47cof⟩
    have hL : Ex.ev s b J c1xL2L≠0 := by
      have k := RegCert.auto_sound c1xL2Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).2
    have h := signed_sound B c1xL2ok hL (detX_ev lX67.eq lY4.eq lX61.eq lY20.eq lX35.eq lY47.eq)
    push_cast at h; linarith
  · have lY48 : Lift s b J (Y.getD 48 0) c1xdeepL c1xdeepY48N c1xdeepY48D c1xdeepY48C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 48 0=((getRat xs 268 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 48]; rfl
        rw [e]; exact hr.1,c1xdeepY48cof⟩
    have lone : Lift s b J (1) c1xdeepL c1xdeeponeN c1xdeeponeD c1xdeeponeC :=
      ⟨by simp [c1xdeeponeN,c1xdeeponeD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xdeeponecof⟩
    have lvD : Lift s b J (50050/s^2) c1xdeepL c1xdeepvDN c1xdeepvDD c1xdeepvDC :=
      ⟨by simp [c1xdeepvDN,c1xdeepvDD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xdeepvDcof⟩
    have hL : Ex.ev s b J c1xdeepL≠0 := by
      have k := RegCert.auto_sound c1xdeepLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [c1xdeepvDD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xdeepok hL (linX_ev (one:=.mul c1xdeeponeN c1xdeeponeC) (lone.eq.trans (one_mul _)) _ [(1,50050/s^2),(-1,Y.getD 48 0),(1,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lvD.eq⟩,⟨by trivial,lY48.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY47 : Lift s b J (Y.getD 47 0) c1xH43L c1xH43Y47N c1xH43Y47D c1xH43Y47C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : Y.getD 47 0=((getRat xs 748 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 47]; rfl
        rw [e]; exact hr.1,c1xH43Y47cof⟩
    have lone : Lift s b J (1) c1xH43L c1xH43oneN c1xH43oneD c1xH43oneC :=
      ⟨by simp [c1xH43oneN,c1xH43oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xH43onecof⟩
    have hL : Ex.ev s b J c1xH43L≠0 := by
      have k := RegCert.auto_sound c1xH43Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2
    have h := signed_sound B c1xH43ok hL (linX_ev (one:=.mul c1xH43oneN c1xH43oneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 47 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY47.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c1xCW0L c1xCW0BxN c1xCW0BxD c1xCW0BxC :=
      ⟨by simp [c1xCW0BxN,c1xCW0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xCW0L c1xCW0ByN c1xCW0ByD c1xCW0ByC :=
      ⟨by simp [c1xCW0ByN,c1xCW0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0Bycof⟩
    have lWq : Lift s b J (s/320) c1xCW0L c1xCW0WqN c1xCW0WqD c1xCW0WqC :=
      ⟨by simp [c1xCW0WqN,c1xCW0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0Wqcof⟩
    have lX33 : Lift s b J (X.getD 33 0) c1xCW0L c1xCW0X33N c1xCW0X33D c1xCW0X33C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 33 0=((getRat xs 424 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 33]; rfl
        rw [e]; exact hr.1,c1xCW0X33cof⟩
    have lY53 : Lift s b J (Y.getD 53 0) c1xCW0L c1xCW0Y53N c1xCW0Y53D c1xCW0Y53C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 53 0=((getRat xs 744 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 53]; rfl
        rw [e]; exact hr.1,c1xCW0Y53cof⟩
    have lone : Lift s b J (1) c1xCW0L c1xCW0oneN c1xCW0oneD c1xCW0oneC :=
      ⟨by simp [c1xCW0oneN,c1xCW0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW0onecof⟩
    have hL : Ex.ev s b J c1xCW0L≠0 := by
      have k := RegCert.auto_sound c1xCW0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [c1xCW0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xCW0ok hL (detX_ev lBx.eq lBy.eq lX33.eq lY53.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c1xCW1L c1xCW1Bx15N c1xCW1Bx15D c1xCW1Bx15C :=
      ⟨by simp [c1xCW1Bx15N,c1xCW1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c1xCW1L c1xCW1ByN c1xCW1ByD c1xCW1ByC :=
      ⟨by simp [c1xCW1ByN,c1xCW1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1Bycof⟩
    have lWq : Lift s b J (s/320) c1xCW1L c1xCW1WqN c1xCW1WqD c1xCW1WqC :=
      ⟨by simp [c1xCW1WqN,c1xCW1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1Wqcof⟩
    have lX33 : Lift s b J (X.getD 33 0) c1xCW1L c1xCW1X33N c1xCW1X33D c1xCW1X33C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : X.getD 33 0=((getRat xs 424 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 33]; rfl
        rw [e]; exact hr.1,c1xCW1X33cof⟩
    have lY53 : Lift s b J (Y.getD 53 0) c1xCW1L c1xCW1Y53N c1xCW1Y53D c1xCW1Y53C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 53 0=((getRat xs 744 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 53]; rfl
        rw [e]; exact hr.1,c1xCW1Y53cof⟩
    have lone : Lift s b J (1) c1xCW1L c1xCW1oneN c1xCW1oneD c1xCW1oneC :=
      ⟨by simp [c1xCW1oneN,c1xCW1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c1xCW1onecof⟩
    have hL : Ex.ev s b J c1xCW1L≠0 := by
      have k := RegCert.auto_sound c1xCW1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2) (by simp [c1xCW1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c1xCW1ok hL (detX_ev lBx15.eq lBy.eq lX33.eq lY53.eq lWq.eq lone.eq)
    push_cast at h; linarith

/-- Range conditions of the other copy test of channel 2. -/
theorem rangesX2 {args xs : List ℚ} (m : Model args xs rows boxes cache)
    (run : xs=execRat args [] (template.corridor.baseRows++template.corridor.rest))
    (hJ : 0≤getRat args 1 ∧ getRat args 1≤1) (hQ : 0≤getRat args 4 ∧ getRat args 4≤1) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 4
    let b : ℝ := ((((520:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let X := (grid template args false).map (fun q : ℚ => (q:ℝ))
    let Y := (grid template args true).map (fun q : ℚ => (q:ℝ))
    0<ArtGallery.det (X.getD 71 0,Y.getD 2 0) (X.getD 20 0,Y.getD 31 0) (X.getD 16 0,Y.getD 35 0) ∧
    0<ArtGallery.det (X.getD 72 0,Y.getD 2 0) (X.getD 20 0,Y.getD 31 0) (X.getD 16 0,Y.getD 35 0) ∧
    ArtGallery.det (X.getD 71 0,Y.getD 2 0) (X.getD 20 0,Y.getD 31 0) (X.getD 17 0,Y.getD 35 0)<0 ∧
    ArtGallery.det (X.getD 72 0,Y.getD 2 0) (X.getD 20 0,Y.getD 31 0) (X.getD 17 0,Y.getD 35 0)<0 ∧
    0<(1:ℝ)*(Y.getD 32 0)+(-1:ℝ)*(1-50050/s^2) ∧
    0<(3:ℝ)*(Y.getD 34 0)+(-7:ℝ)*(1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 17 0,Y.getD 32 0) (0,1) ∧
    0<ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 17 0,Y.getD 32 0) (0,1) ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 17 0,Y.getD 32 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 17 0,Y.getD 32 0) (s/320,1)<0 ∧
    X.getD 50 0=(0:ℝ)/1 ∧
    X.getD 51 0=s/320 ∧
    ArtGallery.det (s/320+b*(50050/s^2),1-50050/s^2) (X.getD 20 0,Y.getD 35 0) (s/320,1)<0 ∧
    ArtGallery.det (s/320+b*(50050/s^2)+3/2,1-50050/s^2) (X.getD 20 0,Y.getD 35 0) (s/320,1)<0 := by
  intro s J Q b X Y
  have Xdef : X=(grid template args false).map (fun q : ℚ => (q:ℝ)) := rfl
  have Ydef : Y=(grid template args true).map (fun q : ℚ => (q:ℝ)) := rfl
  have hs : (0:ℝ)<s := by simp only [s]; exact_mod_cast m.pos
  have hs1 : s≤(((1/65:ℚ):ℚ):ℝ) := by simp only [s]; exact_mod_cast m.upper
  have hJ' : (0:ℝ)≤J ∧ J≤1 := by simp only [J]; exact ⟨by exact_mod_cast hJ.1,by exact_mod_cast hJ.2⟩
  have hQ' : (0:ℝ)≤Q ∧ Q≤1 := by simp only [Q]; exact ⟨by exact_mod_cast hQ.1,by exact_mod_cast hQ.2⟩
  have B : PolyBox.Box (1/65:ℚ) (2599/5005:ℚ) (67979/130130:ℚ) s b J := by
    refine ⟨hs,hs1,?_,?_,hJ'.1,hJ'.2,by norm_num⟩
    · simp only [b]; push_cast; nlinarith
    · simp only [b]; push_cast at hs1 ⊢; nlinarith [mul_le_mul hJ'.2 hs1 hs.le zero_le_one]
  have hin : ∀ k P d, (k,P,d)∈c2ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c2ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have H := c2xhold m hin B
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have lX16 : Lift s b J (X.getD 16 0) c2xUa0L c2xUa0X16N c2xUa0X16D c2xUa0X16C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : X.getD 16 0=((getRat xs 329 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 16]; rfl
        rw [e]; exact hr.1,c2xUa0X16cof⟩
    have lX20 : Lift s b J (X.getD 20 0) c2xUa0L c2xUa0X20N c2xUa0X20D c2xUa0X20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 20 0=((getRat xs 393 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 20]; rfl
        rw [e]; exact hr.1,c2xUa0X20cof⟩
    have lX71 : Lift s b J (X.getD 71 0) c2xUa0L c2xUa0X71N c2xUa0X71D c2xUa0X71C :=
      ⟨by
        have e : X.getD 71 0=((((axisOf template false).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 71]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c2xUa0X71N,c2xUa0X71D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUa0X71cof⟩
    have lY2 : Lift s b J (Y.getD 2 0) c2xUa0L c2xUa0Y2N c2xUa0Y2D c2xUa0Y2C :=
      ⟨by
        have e : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 2]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c2xUa0Y2N,c2xUa0Y2D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUa0Y2cof⟩
    have lY31 : Lift s b J (Y.getD 31 0) c2xUa0L c2xUa0Y31N c2xUa0Y31D c2xUa0Y31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 31 0=((getRat xs 524 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 31]; rfl
        rw [e]; exact hr.1,c2xUa0Y31cof⟩
    have lY35 : Lift s b J (Y.getD 35 0) c2xUa0L c2xUa0Y35N c2xUa0Y35D c2xUa0Y35C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 35 0=((getRat xs 521 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 35]; rfl
        rw [e]; exact hr.1,c2xUa0Y35cof⟩
    have hL : Ex.ev s b J c2xUa0L≠0 := by
      have k := RegCert.auto_sound c2xUa0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2)
    have h := signed_sound B c2xUa0ok hL (detX_ev lX71.eq lY2.eq lX20.eq lY31.eq lX16.eq lY35.eq)
    push_cast at h; linarith
  · have lX16 : Lift s b J (X.getD 16 0) c2xUa1L c2xUa1X16N c2xUa1X16D c2xUa1X16C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
        have e : X.getD 16 0=((getRat xs 329 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 16]; rfl
        rw [e]; exact hr.1,c2xUa1X16cof⟩
    have lX20 : Lift s b J (X.getD 20 0) c2xUa1L c2xUa1X20N c2xUa1X20D c2xUa1X20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 20 0=((getRat xs 393 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 20]; rfl
        rw [e]; exact hr.1,c2xUa1X20cof⟩
    have lX72 : Lift s b J (X.getD 72 0) c2xUa1L c2xUa1X72N c2xUa1X72D c2xUa1X72C :=
      ⟨by
        have e : X.getD 72 0=((((axisOf template false).coordsQ (getRat args 0)).getD 11 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 72]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c2xUa1X72N,c2xUa1X72D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUa1X72cof⟩
    have lY2 : Lift s b J (Y.getD 2 0) c2xUa1L c2xUa1Y2N c2xUa1Y2D c2xUa1Y2C :=
      ⟨by
        have e : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 2]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c2xUa1Y2N,c2xUa1Y2D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUa1Y2cof⟩
    have lY31 : Lift s b J (Y.getD 31 0) c2xUa1L c2xUa1Y31N c2xUa1Y31D c2xUa1Y31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 31 0=((getRat xs 524 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 31]; rfl
        rw [e]; exact hr.1,c2xUa1Y31cof⟩
    have lY35 : Lift s b J (Y.getD 35 0) c2xUa1L c2xUa1Y35N c2xUa1Y35D c2xUa1Y35C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 35 0=((getRat xs 521 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 35]; rfl
        rw [e]; exact hr.1,c2xUa1Y35cof⟩
    have hL : Ex.ev s b J c2xUa1L≠0 := by
      have k := RegCert.auto_sound c2xUa1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2)
    have h := signed_sound B c2xUa1ok hL (detX_ev lX72.eq lY2.eq lX20.eq lY31.eq lX16.eq lY35.eq)
    push_cast at h; linarith
  · have lX17 : Lift s b J (X.getD 17 0) c2xUb0L c2xUb0X17N c2xUb0X17D c2xUb0X17C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 17 0=((getRat xs 526 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 17]; rfl
        rw [e]; exact hr.1,c2xUb0X17cof⟩
    have lX20 : Lift s b J (X.getD 20 0) c2xUb0L c2xUb0X20N c2xUb0X20D c2xUb0X20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 20 0=((getRat xs 393 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 20]; rfl
        rw [e]; exact hr.1,c2xUb0X20cof⟩
    have lX71 : Lift s b J (X.getD 71 0) c2xUb0L c2xUb0X71N c2xUb0X71D c2xUb0X71C :=
      ⟨by
        have e : X.getD 71 0=((((axisOf template false).coordsQ (getRat args 0)).getD 10 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 71]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c2xUb0X71N,c2xUb0X71D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUb0X71cof⟩
    have lY2 : Lift s b J (Y.getD 2 0) c2xUb0L c2xUb0Y2N c2xUb0Y2D c2xUb0Y2C :=
      ⟨by
        have e : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 2]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c2xUb0Y2N,c2xUb0Y2D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUb0Y2cof⟩
    have lY31 : Lift s b J (Y.getD 31 0) c2xUb0L c2xUb0Y31N c2xUb0Y31D c2xUb0Y31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 31 0=((getRat xs 524 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 31]; rfl
        rw [e]; exact hr.1,c2xUb0Y31cof⟩
    have lY35 : Lift s b J (Y.getD 35 0) c2xUb0L c2xUb0Y35N c2xUb0Y35D c2xUb0Y35C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 35 0=((getRat xs 521 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 35]; rfl
        rw [e]; exact hr.1,c2xUb0Y35cof⟩
    have hL : Ex.ev s b J c2xUb0L≠0 := by
      have k := RegCert.auto_sound c2xUb0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2)
    have h := signed_sound B c2xUb0ok hL (detX_ev lX71.eq lY2.eq lX20.eq lY31.eq lX17.eq lY35.eq)
    push_cast at h; linarith
  · have lX17 : Lift s b J (X.getD 17 0) c2xUb1L c2xUb1X17N c2xUb1X17D c2xUb1X17C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 17 0=((getRat xs 526 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 17]; rfl
        rw [e]; exact hr.1,c2xUb1X17cof⟩
    have lX20 : Lift s b J (X.getD 20 0) c2xUb1L c2xUb1X20N c2xUb1X20D c2xUb1X20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 20 0=((getRat xs 393 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 20]; rfl
        rw [e]; exact hr.1,c2xUb1X20cof⟩
    have lX72 : Lift s b J (X.getD 72 0) c2xUb1L c2xUb1X72N c2xUb1X72D c2xUb1X72C :=
      ⟨by
        have e : X.getD 72 0=((((axisOf template false).coordsQ (getRat args 0)).getD 11 0 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 72]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.xAxis,Gap.valR,evalR,c2xUb1X72N,c2xUb1X72D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUb1X72cof⟩
    have lY2 : Lift s b J (Y.getD 2 0) c2xUb1L c2xUb1Y2N c2xUb1Y2D c2xUb1Y2C :=
      ⟨by
        have e : Y.getD 2 0=((((axisOf template true).coordsQ (getRat args 0)).getD 2 0 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 2]; rfl
        rw [e,level_cast,level_eq _ _ _ (by decide)]
        simp [axisOf,template,RoomFamily.Shifted.yAxis,Gap.valR,evalR,c2xUb1Y2N,c2xUb1Y2D,Ex.ev,ev3,ev2,ev1]
        ring,c2xUb1Y2cof⟩
    have lY31 : Lift s b J (Y.getD 31 0) c2xUb1L c2xUb1Y31N c2xUb1Y31D c2xUb1Y31C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        have e : Y.getD 31 0=((getRat xs 524 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 31]; rfl
        rw [e]; exact hr.1,c2xUb1Y31cof⟩
    have lY35 : Lift s b J (Y.getD 35 0) c2xUb1L c2xUb1Y35N c2xUb1Y35D c2xUb1Y35C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 35 0=((getRat xs 521 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 35]; rfl
        rw [e]; exact hr.1,c2xUb1Y35cof⟩
    have hL : Ex.ev s b J c2xUb1L≠0 := by
      have k := RegCert.auto_sound c2xUb1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2)
    have h := signed_sound B c2xUb1ok hL (detX_ev lX72.eq lY2.eq lX20.eq lY31.eq lX17.eq lY35.eq)
    push_cast at h; linarith
  · have lBy : Lift s b J (1-50050/s^2) c2xbLowL c2xbLowByN c2xbLowByD c2xbLowByC :=
      ⟨by simp [c2xbLowByN,c2xbLowByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xbLowBycof⟩
    have lY32 : Lift s b J (Y.getD 32 0) c2xbLowL c2xbLowY32N c2xbLowY32D c2xbLowY32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 32 0=((getRat xs 395 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 32]; rfl
        rw [e]; exact hr.1,c2xbLowY32cof⟩
    have lone : Lift s b J (1) c2xbLowL c2xbLowoneN c2xbLowoneD c2xbLowoneC :=
      ⟨by simp [c2xbLowoneN,c2xbLowoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xbLowonecof⟩
    have hL : Ex.ev s b J c2xbLowL≠0 := by
      have k := RegCert.auto_sound c2xbLowLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (by simp [c2xbLowByD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2xbLowok hL (linX_ev (one:=.mul c2xbLowoneN c2xbLowoneC) (lone.eq.trans (one_mul _)) _ [(1,Y.getD 32 0),(-1,1-50050/s^2)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY32.eq⟩,⟨by trivial,lBy.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lY34 : Lift s b J (Y.getD 34 0) c2xH43uL c2xH43uY34N c2xH43uY34D c2xH43uY34C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
        have e : Y.getD 34 0=((getRat xs 387 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 34]; rfl
        rw [e]; exact hr.1,c2xH43uY34cof⟩
    have lone : Lift s b J (1) c2xH43uL c2xH43uoneN c2xH43uoneD c2xH43uoneC :=
      ⟨by simp [c2xH43uoneN,c2xH43uoneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xH43uonecof⟩
    have hL : Ex.ev s b J c2xH43uL≠0 := by
      have k := RegCert.auto_sound c2xH43uLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))).2
    have h := signed_sound B c2xH43uok hL (linX_ev (one:=.mul c2xH43uoneN c2xH43uoneC) (lone.eq.trans (one_mul _)) _ [(3,Y.getD 34 0),(-7,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lY34.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c2xDL0L c2xDL0BxN c2xDL0BxD c2xDL0BxC :=
      ⟨by simp [c2xDL0BxN,c2xDL0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c2xDL0L c2xDL0ByN c2xDL0ByD c2xDL0ByC :=
      ⟨by simp [c2xDL0ByN,c2xDL0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL0Bycof⟩
    have lX17 : Lift s b J (X.getD 17 0) c2xDL0L c2xDL0X17N c2xDL0X17D c2xDL0X17C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 17 0=((getRat xs 526 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 17]; rfl
        rw [e]; exact hr.1,c2xDL0X17cof⟩
    have lY32 : Lift s b J (Y.getD 32 0) c2xDL0L c2xDL0Y32N c2xDL0Y32D c2xDL0Y32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 32 0=((getRat xs 395 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 32]; rfl
        rw [e]; exact hr.1,c2xDL0Y32cof⟩
    have lone : Lift s b J (1) c2xDL0L c2xDL0oneN c2xDL0oneD c2xDL0oneC :=
      ⟨by simp [c2xDL0oneN,c2xDL0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL0onecof⟩
    have lzero : Lift s b J (0) c2xDL0L c2xDL0zeroN c2xDL0zeroD c2xDL0zeroC :=
      ⟨by simp [c2xDL0zeroN,c2xDL0zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL0zerocof⟩
    have hL : Ex.ev s b J c2xDL0L≠0 := by
      have k := RegCert.auto_sound c2xDL0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c2xDL0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2xDL0ok hL (detX_ev lBx.eq lBy.eq lX17.eq lY32.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c2xDL1L c2xDL1Bx15N c2xDL1Bx15D c2xDL1Bx15C :=
      ⟨by simp [c2xDL1Bx15N,c2xDL1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c2xDL1L c2xDL1ByN c2xDL1ByD c2xDL1ByC :=
      ⟨by simp [c2xDL1ByN,c2xDL1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL1Bycof⟩
    have lX17 : Lift s b J (X.getD 17 0) c2xDL1L c2xDL1X17N c2xDL1X17D c2xDL1X17C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 17 0=((getRat xs 526 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 17]; rfl
        rw [e]; exact hr.1,c2xDL1X17cof⟩
    have lY32 : Lift s b J (Y.getD 32 0) c2xDL1L c2xDL1Y32N c2xDL1Y32D c2xDL1Y32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 32 0=((getRat xs 395 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 32]; rfl
        rw [e]; exact hr.1,c2xDL1Y32cof⟩
    have lone : Lift s b J (1) c2xDL1L c2xDL1oneN c2xDL1oneD c2xDL1oneC :=
      ⟨by simp [c2xDL1oneN,c2xDL1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL1onecof⟩
    have lzero : Lift s b J (0) c2xDL1L c2xDL1zeroN c2xDL1zeroD c2xDL1zeroC :=
      ⟨by simp [c2xDL1zeroN,c2xDL1zeroD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDL1zerocof⟩
    have hL : Ex.ev s b J c2xDL1L≠0 := by
      have k := RegCert.auto_sound c2xDL1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c2xDL1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2xDL1ok hL (detX_ev lBx15.eq lBy.eq lX17.eq lY32.eq lzero.eq lone.eq)
    push_cast at h; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c2xDR0L c2xDR0BxN c2xDR0BxD c2xDR0BxC :=
      ⟨by simp [c2xDR0BxN,c2xDR0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c2xDR0L c2xDR0ByN c2xDR0ByD c2xDR0ByC :=
      ⟨by simp [c2xDR0ByN,c2xDR0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR0Bycof⟩
    have lWq : Lift s b J (s/320) c2xDR0L c2xDR0WqN c2xDR0WqD c2xDR0WqC :=
      ⟨by simp [c2xDR0WqN,c2xDR0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR0Wqcof⟩
    have lX17 : Lift s b J (X.getD 17 0) c2xDR0L c2xDR0X17N c2xDR0X17D c2xDR0X17C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 17 0=((getRat xs 526 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 17]; rfl
        rw [e]; exact hr.1,c2xDR0X17cof⟩
    have lY32 : Lift s b J (Y.getD 32 0) c2xDR0L c2xDR0Y32N c2xDR0Y32D c2xDR0Y32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 32 0=((getRat xs 395 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 32]; rfl
        rw [e]; exact hr.1,c2xDR0Y32cof⟩
    have lone : Lift s b J (1) c2xDR0L c2xDR0oneN c2xDR0oneD c2xDR0oneC :=
      ⟨by simp [c2xDR0oneN,c2xDR0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR0onecof⟩
    have hL : Ex.ev s b J c2xDR0L≠0 := by
      have k := RegCert.auto_sound c2xDR0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c2xDR0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2xDR0ok hL (detX_ev lBx.eq lBy.eq lX17.eq lY32.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c2xDR1L c2xDR1Bx15N c2xDR1Bx15D c2xDR1Bx15C :=
      ⟨by simp [c2xDR1Bx15N,c2xDR1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c2xDR1L c2xDR1ByN c2xDR1ByD c2xDR1ByC :=
      ⟨by simp [c2xDR1ByN,c2xDR1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR1Bycof⟩
    have lWq : Lift s b J (s/320) c2xDR1L c2xDR1WqN c2xDR1WqD c2xDR1WqC :=
      ⟨by simp [c2xDR1WqN,c2xDR1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR1Wqcof⟩
    have lX17 : Lift s b J (X.getD 17 0) c2xDR1L c2xDR1X17N c2xDR1X17D c2xDR1X17C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        have e : X.getD 17 0=((getRat xs 526 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 17]; rfl
        rw [e]; exact hr.1,c2xDR1X17cof⟩
    have lY32 : Lift s b J (Y.getD 32 0) c2xDR1L c2xDR1Y32N c2xDR1Y32D c2xDR1Y32C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        have e : Y.getD 32 0=((getRat xs 395 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 32]; rfl
        rw [e]; exact hr.1,c2xDR1Y32cof⟩
    have lone : Lift s b J (1) c2xDR1L c2xDR1oneN c2xDR1oneD c2xDR1oneC :=
      ⟨by simp [c2xDR1oneN,c2xDR1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xDR1onecof⟩
    have hL : Ex.ev s b J c2xDR1L≠0 := by
      have k := RegCert.auto_sound c2xDR1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).2) (by simp [c2xDR1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2xDR1ok hL (detX_ev lBx15.eq lBy.eq lX17.eq lY32.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lX50 : Lift s b J (X.getD 50 0) c2xhdlL c2xhdlX50N c2xhdlX50D c2xhdlX50C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.head _))
        have e : X.getD 50 0=((getRat xs 1070 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 50]; rfl
        rw [e]; exact hr.1,c2xhdlX50cof⟩
    have lone : Lift s b J (1) c2xhdlL c2xhdloneN c2xhdloneD c2xhdloneC :=
      ⟨by simp [c2xhdloneN,c2xhdloneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xhdlonecof⟩
    have hL : Ex.ev s b J c2xhdlL≠0 := by
      have k := RegCert.auto_sound c2xhdlLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c2xhdlok hL (linX_ev (one:=.mul c2xhdloneN c2xhdloneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 50 0),(0,1)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX50.eq⟩,⟨by trivial,lone.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lWq : Lift s b J (s/320) c2xhdrL c2xhdrWqN c2xhdrWqD c2xhdrWqC :=
      ⟨by simp [c2xhdrWqN,c2xhdrWqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xhdrWqcof⟩
    have lX51 : Lift s b J (X.getD 51 0) c2xhdrL c2xhdrX51N c2xhdrX51D c2xhdrX51C :=
      ⟨by
        have hr := H _ (List.Mem.head _)
        have e : X.getD 51 0=((getRat xs 1217 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 51]; rfl
        rw [e]; exact hr.1,c2xhdrX51cof⟩
    have lone : Lift s b J (1) c2xhdrL c2xhdroneN c2xhdroneD c2xhdroneC :=
      ⟨by simp [c2xhdroneN,c2xhdroneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xhdronecof⟩
    have hL : Ex.ev s b J c2xhdrL≠0 := by
      have k := RegCert.auto_sound c2xhdrLne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (by simp [Ex.ev,ev3,ev2,ev1])
    have h := zero_of_check c2xhdrok hL (linX_ev (one:=.mul c2xhdroneN c2xhdroneC) (lone.eq.trans (one_mul _)) _ [(1,X.getD 51 0),(-1,s/320)] (by
        simp only [List.forall₂_cons,List.Forall₂.nil,and_true]; exact ⟨⟨by trivial,lX51.eq⟩,⟨by trivial,lWq.eq⟩⟩))
    simp only [linR] at h; push_cast at h ⊢; linarith
  · have lBx : Lift s b J (s/320+b*(50050/s^2)) c2xCW0L c2xCW0BxN c2xCW0BxD c2xCW0BxC :=
      ⟨by simp [c2xCW0BxN,c2xCW0BxD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW0Bxcof⟩
    have lBy : Lift s b J (1-50050/s^2) c2xCW0L c2xCW0ByN c2xCW0ByD c2xCW0ByC :=
      ⟨by simp [c2xCW0ByN,c2xCW0ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW0Bycof⟩
    have lWq : Lift s b J (s/320) c2xCW0L c2xCW0WqN c2xCW0WqD c2xCW0WqC :=
      ⟨by simp [c2xCW0WqN,c2xCW0WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW0Wqcof⟩
    have lX20 : Lift s b J (X.getD 20 0) c2xCW0L c2xCW0X20N c2xCW0X20D c2xCW0X20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 20 0=((getRat xs 393 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 20]; rfl
        rw [e]; exact hr.1,c2xCW0X20cof⟩
    have lY35 : Lift s b J (Y.getD 35 0) c2xCW0L c2xCW0Y35N c2xCW0Y35D c2xCW0Y35C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 35 0=((getRat xs 521 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 35]; rfl
        rw [e]; exact hr.1,c2xCW0Y35cof⟩
    have lone : Lift s b J (1) c2xCW0L c2xCW0oneN c2xCW0oneD c2xCW0oneC :=
      ⟨by simp [c2xCW0oneN,c2xCW0oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW0onecof⟩
    have hL : Ex.ev s b J c2xCW0L≠0 := by
      have k := RegCert.auto_sound c2xCW0Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c2xCW0BxD,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2xCW0ok hL (detX_ev lBx.eq lBy.eq lX20.eq lY35.eq lWq.eq lone.eq)
    push_cast at h; linarith
  · have lBx15 : Lift s b J (s/320+b*(50050/s^2)+3/2) c2xCW1L c2xCW1Bx15N c2xCW1Bx15D c2xCW1Bx15C :=
      ⟨by simp [c2xCW1Bx15N,c2xCW1Bx15D,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW1Bx15cof⟩
    have lBy : Lift s b J (1-50050/s^2) c2xCW1L c2xCW1ByN c2xCW1ByD c2xCW1ByC :=
      ⟨by simp [c2xCW1ByN,c2xCW1ByD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW1Bycof⟩
    have lWq : Lift s b J (s/320) c2xCW1L c2xCW1WqN c2xCW1WqD c2xCW1WqC :=
      ⟨by simp [c2xCW1WqN,c2xCW1WqD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW1Wqcof⟩
    have lX20 : Lift s b J (X.getD 20 0) c2xCW1L c2xCW1X20N c2xCW1X20D c2xCW1X20C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
        have e : X.getD 20 0=((getRat xs 393 : ℚ) : ℝ) := by
          rw [Xdef,grid_ref m run false 20]; rfl
        rw [e]; exact hr.1,c2xCW1X20cof⟩
    have lY35 : Lift s b J (Y.getD 35 0) c2xCW1L c2xCW1Y35N c2xCW1Y35D c2xCW1Y35C :=
      ⟨by
        have hr := H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        have e : Y.getD 35 0=((getRat xs 521 : ℚ) : ℝ) := by
          rw [Ydef,grid_ref m run true 35]; rfl
        rw [e]; exact hr.1,c2xCW1Y35cof⟩
    have lone : Lift s b J (1) c2xCW1L c2xCW1oneN c2xCW1oneD c2xCW1oneC :=
      ⟨by simp [c2xCW1oneN,c2xCW1oneD,Ex.ev,ev3,ev2,ev1] <;> field_simp <;> ring,c2xCW1onecof⟩
    have hL : Ex.ev s b J c2xCW1L≠0 := by
      have k := RegCert.auto_sound c2xCW1Lne s b J
      simp only [Ex.ev] at k
      intro h0; rw [h0,zero_mul,zero_sub,neg_eq_zero] at k
      exact absurd k (mul_ne_zero (mul_ne_zero (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))).2 (H _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))).2) (by simp [c2xCW1Bx15D,Ex.ev,ev3,ev2,ev1]; positivity))
    have h := signed_sound B c2xCW1ok hL (detX_ev lBx15.eq lBy.eq lX20.eq lY35.eq lWq.eq lone.eq)
    push_cast at h; linarith

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Shifted_40_200_520
end
