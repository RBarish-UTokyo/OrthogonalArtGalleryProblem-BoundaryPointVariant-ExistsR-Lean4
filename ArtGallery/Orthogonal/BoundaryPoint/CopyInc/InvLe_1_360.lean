module

public import ArtGallery.Orthogonal.BoundaryPoint.RowLit.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.RegCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_1_360

/-! Exact nook incidences of the copy channels of profile `InvLe_1_360` (generated).
Closed forms of the axis registers in the variables `(s,b,J)` are certified by `RegCert`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyInc.InvLe_1_360
open MarginCert RegisterTable RegisterOrder KronCert WingOrder.InvLe_1_360
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false


/-! ## Channel 0: receiver role 0, bank 1, nook axis register 579 -/

noncomputable def c0ins : RegCert.Inputs := [(0,(.lit ([[],[[1]]] : P3)),1),(1,(.lit ([[[0,1]]] : P3)),1),(2,(.lit ([[[-8],[10010]],[[0,-400]]] : P3)),25)]
noncomputable def c0top : RegCert.Entry := ⟨579,(.lit ([[[271791520],[-1601600]],[[-5005]],[[16]]] : P3)),(.lit ([[[30750720],[-1601600]],[],[[16]]] : P3)),(.lit ([[[1]]] : P3))⟩
noncomputable def c0cert : List RegCert.Entry := [
  ⟨861,(.lit ([[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨860,(.lit ([[[0,1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨859,(.lit ([[[-8],[10010]],[[0,-400]]] : P3)),(.lit ([[[25]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨857,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨856,(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨855,(.lit ([[[1]]] : P3)),(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨854,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨851,(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨850,(.lit ([[[1]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨849,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[100100]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨848,(.lit ([[[96]]] : P3)),(.lit ([[[5]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨847,(.lit ([[[1921920]],[],[[1]]] : P3)),(.lit ([[[100100]]] : P3)),(.lit ([[[5]]] : P3))⟩,
  ⟨840,(.lit ([[[5]]] : P3)),(.lit ([[[2002]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨839,(.lit ([[[-4],[5005]],[[0,-200]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[10]]] : P3))⟩,
  ⟨838,(.lit ([[[4]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨837,(.lit ([[[],[1001]],[[0,-40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[25025]]] : P3))⟩,
  ⟨836,(.lit ([[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨835,(.lit ([[],[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨834,(.lit ([[],[[0,40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨833,(.lit ([[[],[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1002001]]] : P3))⟩,
  ⟨832,(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨831,(.lit ([[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨830,(.lit ([[],[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨827,(.lit ([[],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨826,(.lit ([[[301]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨825,(.lit ([[[48160]],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[2]]] : P3))⟩,
  ⟨824,(.lit ([[[],[-1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨823,(.lit ([[[1921920],[-100100]],[],[[1]]] : P3)),(.lit ([[[100100]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨822,(.lit ([[[100100]]] : P3)),(.lit ([[[1921920],[-100100]],[],[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨821,(.lit ([[[241040800]],[[-5005]]] : P3)),(.lit ([[[30750720],[-1601600]],[],[[16]]] : P3)),(.lit ([[[20]]] : P3))⟩,
  ⟨812,(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩] ++ [c0top]
theorem c0ok : RegCert.check rows boxes c0ins [] c0cert=true := by (try rw [RowLit.InvLe_1_360.out_eq]); (try rw [RowLit.InvLe_1_360.check_eq]); decide +kernel

/-- The nook axis of channel 0 meets the base and receiver central rays exactly. -/
theorem lower0 {args xs : List ℚ} (m : Model args xs rows boxes cache) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 2
    let b : ℝ := ((((1:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let H : ℝ := (getRat xs 579 : ℝ)-1
    s/320-b*H=301/2-((96/5:ℝ) + (1/100100:ℝ)*s^2)*H := by
  intro s J Q b H
  have hin : ∀ k P d, (k,P,d)∈c0ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c0ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have h := RegCert.check_sound m.run m.bounds hin c0cert [] (by simp) c0ok c0top
    (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨hx,hD⟩ := h
  have hreg : c0top.reg=579 := rfl
  rw [hreg] at hx
  have eN : Ex.ev s b J c0top.N=((271791520:ℝ) + (-1601600:ℝ)*b + (-5005:ℝ)*s + (16:ℝ)*s^2) := by simp [c0top,Ex.ev,ev3,ev2,ev1]; ring
  have eD : Ex.ev s b J c0top.D=((30750720:ℝ) + (-1601600:ℝ)*b + (16:ℝ)*s^2) := by simp [c0top,Ex.ev,ev3,ev2,ev1]; ring
  have key : (s/320-b*H-(301/2-((96/5:ℝ) + (1/100100:ℝ)*s^2)*H))*Ex.ev s b J c0top.D=0 := by
    rw [eN,eD] at hx; rw [eD]; simp only [H]; linear_combination (((96/5:ℝ) + (1/100100:ℝ)*s^2)-b)*hx
  rcases mul_eq_zero.mp key with h|h
  · linarith
  · exact absurd h hD

/-! ## Channel 1: receiver role 1, bank 360, nook axis register 368 -/

noncomputable def c1ins : RegCert.Inputs := [(0,(.lit ([[],[[1]]] : P3)),1),(1,(.lit ([[[0,1]]] : P3)),1),(3,(.lit ([[[-3598],[10010]],[[0,-400]]] : P3)),25)]
noncomputable def c1top : RegCert.Entry := ⟨368,(.lit ([[[1366729364000],[-8016008000]],[[-25050025]],[[80080]],[],[[-4]]] : P3)),(.lit ([[[160320160000],[-8016008000]],[],[[80080]],[],[[-4]]] : P3)),(.lit ([[[1]]] : P3))⟩
noncomputable def c1cert : List RegCert.Entry := [
  ⟨861,(.lit ([[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨860,(.lit ([[[0,1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨858,(.lit ([[[-3598],[10010]],[[0,-400]]] : P3)),(.lit ([[[25]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨857,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨856,(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨855,(.lit ([[[1]]] : P3)),(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨854,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨853,(.lit ([[[5]]] : P3)),(.lit ([[[4]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨852,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[40040]]] : P3)),(.lit ([[[5]]] : P3))⟩,
  ⟨846,(.lit ([[],[],[[-1]]] : P3)),(.lit ([[[40040]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨845,(.lit ([[[1]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨844,(.lit ([[[20020]],[],[[-1]]] : P3)),(.lit ([[[40040]]] : P3)),(.lit ([[[2]]] : P3))⟩,
  ⟨843,(.lit ([[],[],[[20020]],[],[[-1]]] : P3)),(.lit ([[[2004002000]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨842,(.lit ([[[20]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨841,(.lit ([[[40080040000]],[],[[20020]],[],[[-1]]] : P3)),(.lit ([[[2004002000]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨840,(.lit ([[[5]]] : P3)),(.lit ([[[2002]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨836,(.lit ([[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨835,(.lit ([[],[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨834,(.lit ([[],[[0,40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨832,(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨831,(.lit ([[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨830,(.lit ([[],[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨827,(.lit ([[],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨826,(.lit ([[[301]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨825,(.lit ([[[48160]],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[2]]] : P3))⟩,
  ⟨812,(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨574,(.lit ([[[-1799],[5005]],[[0,-200]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[10]]] : P3))⟩,
  ⟨573,(.lit ([[[257]]] : P3)),(.lit ([[[715]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨572,(.lit ([[[],[1001]],[[0,-40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[3575]]] : P3))⟩,
  ⟨571,(.lit ([[[],[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1002001]]] : P3))⟩,
  ⟨570,(.lit ([[[],[-1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨569,(.lit ([[[40080040000],[-2004002000]],[],[[20020]],[],[[-1]]] : P3)),(.lit ([[[2004002000]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨568,(.lit ([[[2004002000]]] : P3)),(.lit ([[[40080040000],[-2004002000]],[],[[20020]],[],[[-1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨567,(.lit ([[[1206409204000]],[[-25050025]]] : P3)),(.lit ([[[160320160000],[-8016008000]],[],[[80080]],[],[[-4]]] : P3)),(.lit ([[[80]]] : P3))⟩] ++ [c1top]
theorem c1ok : RegCert.check rows boxes c1ins [] c1cert=true := by (try rw [RowLit.InvLe_1_360.out_eq]); (try rw [RowLit.InvLe_1_360.check_eq]); decide +kernel

/-- The nook axis of channel 1 meets the base and receiver central rays exactly. -/
theorem lower1 {args xs : List ℚ} (m : Model args xs rows boxes cache) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((360:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let H : ℝ := (getRat xs 368 : ℝ)-1
    s/320-b*H=301/2-((20:ℝ) + (-1/2004002000:ℝ)*s^4 + (1/100100:ℝ)*s^2)*H := by
  intro s J Q b H
  have hin : ∀ k P d, (k,P,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c1ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have h := RegCert.check_sound m.run m.bounds hin c1cert [] (by simp) c1ok c1top
    (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨hx,hD⟩ := h
  have hreg : c1top.reg=368 := rfl
  rw [hreg] at hx
  have eN : Ex.ev s b J c1top.N=((1366729364000:ℝ) + (-8016008000:ℝ)*b + (-25050025:ℝ)*s + (-4:ℝ)*s^4 + (80080:ℝ)*s^2) := by simp [c1top,Ex.ev,ev3,ev2,ev1]; ring
  have eD : Ex.ev s b J c1top.D=((160320160000:ℝ) + (-8016008000:ℝ)*b + (-4:ℝ)*s^4 + (80080:ℝ)*s^2) := by simp [c1top,Ex.ev,ev3,ev2,ev1]; ring
  have key : (s/320-b*H-(301/2-((20:ℝ) + (-1/2004002000:ℝ)*s^4 + (1/100100:ℝ)*s^2)*H))*Ex.ev s b J c1top.D=0 := by
    rw [eN,eD] at hx; rw [eD]; simp only [H]; linear_combination (((20:ℝ) + (-1/2004002000:ℝ)*s^4 + (1/100100:ℝ)*s^2)-b)*hx
  rcases mul_eq_zero.mp key with h|h
  · linarith
  · exact absurd h hD

end ArtGallery.Orthogonal.BoundaryPoint.CopyInc.InvLe_1_360
end
