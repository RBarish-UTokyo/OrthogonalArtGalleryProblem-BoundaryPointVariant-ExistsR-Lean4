module

public import ArtGallery.Orthogonal.BoundaryPoint.RowLit.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.RegCert
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Lower_10_520_1000

/-! Exact nook incidences of the copy channels of profile `Lower_10_520_1000` (generated).
Closed forms of the axis registers in the variables `(s,b,J)` are certified by `RegCert`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyInc.Lower_10_520_1000
open MarginCert RegisterTable RegisterOrder KronCert WingOrder.Lower_10_520_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false


/-! ## Channel 0: receiver role 3, bank 10, nook axis register 968 -/

noncomputable def c0ins : RegCert.Inputs := [(0,(.lit ([[],[[1]]] : P3)),1),(1,(.lit ([[[0,1]]] : P3)),1),(2,(.lit ([[[-98],[10010]],[[0,-400]]] : P3)),25)]
noncomputable def c0top : RegCert.Entry := ⟨968,(.lit ([[[62560],[-320]],[[-1]]] : P3)),(.lit ([[[14400],[-320]]] : P3)),(.lit ([[[1]]] : P3))⟩
noncomputable def c0cert : List RegCert.Entry := [
  ⟨1239,(.lit ([[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1238,(.lit ([[[0,1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1237,(.lit ([[[-98],[10010]],[[0,-400]]] : P3)),(.lit ([[[25]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1226,(.lit ([[[5]]] : P3)),(.lit ([[[2002]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1225,(.lit ([[[-49],[5005]],[[0,-200]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[10]]] : P3))⟩,
  ⟨1224,(.lit ([[[7]]] : P3)),(.lit ([[[715]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1223,(.lit ([[[],[1001]],[[0,-40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[3575]]] : P3))⟩,
  ⟨1222,(.lit ([[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1221,(.lit ([[],[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1220,(.lit ([[],[[0,40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1219,(.lit ([[[],[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1002001]]] : P3))⟩,
  ⟨1218,(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1217,(.lit ([[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1216,(.lit ([[],[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1213,(.lit ([[],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1212,(.lit ([[[301]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1211,(.lit ([[[48160]],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[2]]] : P3))⟩,
  ⟨1210,(.lit ([[[],[-1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1209,(.lit ([[[45]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1208,(.lit ([[[45],[-1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1207,(.lit ([[[1]]] : P3)),(.lit ([[[45],[-1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1206,(.lit ([[[48160]],[[-1]]] : P3)),(.lit ([[[14400],[-320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1197,(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩] ++ [c0top]
theorem c0ok : RegCert.check rows boxes c0ins [] c0cert=true := by (try rw [RowLit.Lower_10_520_1000.out_eq]); (try rw [RowLit.Lower_10_520_1000.check_eq]); decide +kernel

/-- The nook axis of channel 0 meets the base and receiver central rays exactly. -/
theorem lower0 {args xs : List ℚ} (m : Model args xs rows boxes cache) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 2
    let b : ℝ := ((((10:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let H : ℝ := (getRat xs 968 : ℝ)-1
    s/320-b*H=301/2-((45:ℝ))*H := by
  intro s J Q b H
  have hin : ∀ k P d, (k,P,d)∈c0ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c0ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have h := RegCert.check_sound m.run m.bounds hin c0cert [] (by simp) c0ok c0top
    (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨hx,hD⟩ := h
  have hreg : c0top.reg=968 := rfl
  rw [hreg] at hx
  have eN : Ex.ev s b J c0top.N=((62560:ℝ) + (-1:ℝ)*s + (-320:ℝ)*b) := by simp [c0top,Ex.ev,ev3,ev2,ev1]; ring
  have eD : Ex.ev s b J c0top.D=((14400:ℝ) + (-320:ℝ)*b) := by simp [c0top,Ex.ev,ev3,ev2,ev1]; ring
  have key : (s/320-b*H-(301/2-((45:ℝ))*H))*Ex.ev s b J c0top.D=0 := by
    rw [eN,eD] at hx; rw [eD]; simp only [H]; linear_combination (((45:ℝ))-b)*hx
  rcases mul_eq_zero.mp key with h|h
  · linarith
  · exact absurd h hD

/-! ## Channel 1: receiver role 5, bank 520, nook axis register 748 -/

noncomputable def c1ins : RegCert.Inputs := [(0,(.lit ([[],[[1]]] : P3)),1),(1,(.lit ([[[0,1]]] : P3)),1),(3,(.lit ([[[-5198],[10010]],[[0,-400]]] : P3)),25)]
noncomputable def c1top : RegCert.Entry := ⟨748,(.lit ([[[210880],[-960]],[[-3]]] : P3)),(.lit ([[[66400],[-960]]] : P3)),(.lit ([[[1]]] : P3))⟩
noncomputable def c1cert : List RegCert.Entry := [
  ⟨1239,(.lit ([[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1238,(.lit ([[[0,1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1236,(.lit ([[[-5198],[10010]],[[0,-400]]] : P3)),(.lit ([[[25]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1226,(.lit ([[[5]]] : P3)),(.lit ([[[2002]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1222,(.lit ([[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1221,(.lit ([[],[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1220,(.lit ([[],[[0,40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1218,(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1217,(.lit ([[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1216,(.lit ([[],[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1213,(.lit ([[],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1212,(.lit ([[[301]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1211,(.lit ([[[48160]],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[2]]] : P3))⟩,
  ⟨1197,(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨963,(.lit ([[[-2599],[5005]],[[0,-200]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[10]]] : P3))⟩,
  ⟨962,(.lit ([[[2599]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨961,(.lit ([[[],[1001]],[[0,-40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[25025]]] : P3))⟩,
  ⟨960,(.lit ([[[],[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1002001]]] : P3))⟩,
  ⟨959,(.lit ([[[],[-1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨958,(.lit ([[[415]]] : P3)),(.lit ([[[6]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨957,(.lit ([[[415],[-6]]] : P3)),(.lit ([[[6]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨956,(.lit ([[[6]]] : P3)),(.lit ([[[415],[-6]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨955,(.lit ([[[144480]],[[-3]]] : P3)),(.lit ([[[66400],[-960]]] : P3)),(.lit ([[[2]]] : P3))⟩] ++ [c1top]
theorem c1ok : RegCert.check rows boxes c1ins [] c1cert=true := by (try rw [RowLit.Lower_10_520_1000.out_eq]); (try rw [RowLit.Lower_10_520_1000.check_eq]); decide +kernel

/-- The nook axis of channel 1 meets the base and receiver central rays exactly. -/
theorem lower1 {args xs : List ℚ} (m : Model args xs rows boxes cache) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 3
    let b : ℝ := ((((520:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let H : ℝ := (getRat xs 748 : ℝ)-1
    s/320-b*H=301/2-((415/6:ℝ))*H := by
  intro s J Q b H
  have hin : ∀ k P d, (k,P,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c1ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have h := RegCert.check_sound m.run m.bounds hin c1cert [] (by simp) c1ok c1top
    (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨hx,hD⟩ := h
  have hreg : c1top.reg=748 := rfl
  rw [hreg] at hx
  have eN : Ex.ev s b J c1top.N=((210880:ℝ) + (-960:ℝ)*b + (-3:ℝ)*s) := by simp [c1top,Ex.ev,ev3,ev2,ev1]; ring
  have eD : Ex.ev s b J c1top.D=((66400:ℝ) + (-960:ℝ)*b) := by simp [c1top,Ex.ev,ev3,ev2,ev1]; ring
  have key : (s/320-b*H-(301/2-((415/6:ℝ))*H))*Ex.ev s b J c1top.D=0 := by
    rw [eN,eD] at hx; rw [eD]; simp only [H]; linear_combination (((415/6:ℝ))-b)*hx
  rcases mul_eq_zero.mp key with h|h
  · linarith
  · exact absurd h hD

/-! ## Channel 2: receiver role 6, bank 1000, nook axis register 525 -/

noncomputable def c2ins : RegCert.Inputs := [(0,(.lit ([[],[[1]]] : P3)),1),(1,(.lit ([[[0,1]]] : P3)),1),(4,(.lit ([[[-9998],[10010]],[[0,-400]]] : P3)),25)]
noncomputable def c2top : RegCert.Entry := ⟨525,(.lit ([[[414814400],[-1601600]],[[-5005]],[[48]]] : P3)),(.lit ([[[173773600],[-1601600]],[],[[48]]] : P3)),(.lit ([[[1]]] : P3))⟩
noncomputable def c2cert : List RegCert.Entry := [
  ⟨1239,(.lit ([[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1238,(.lit ([[[0,1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1235,(.lit ([[[-9998],[10010]],[[0,-400]]] : P3)),(.lit ([[[25]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1234,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1233,(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1232,(.lit ([[[1]]] : P3)),(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1231,(.lit ([[],[],[[1]]] : P3)),(.lit ([[[50050]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1230,(.lit ([[[3]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1229,(.lit ([[],[],[[3]]] : P3)),(.lit ([[[100100]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1228,(.lit ([[[217]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1227,(.lit ([[[10860850]],[],[[3]]] : P3)),(.lit ([[[100100]]] : P3)),(.lit ([[[2]]] : P3))⟩,
  ⟨1226,(.lit ([[[5]]] : P3)),(.lit ([[[2002]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1222,(.lit ([[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1221,(.lit ([[],[[40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1220,(.lit ([[],[[0,40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1218,(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1217,(.lit ([[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1216,(.lit ([[],[[1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1213,(.lit ([[],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1212,(.lit ([[[301]]] : P3)),(.lit ([[[2]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨1211,(.lit ([[[48160]],[[-1]]] : P3)),(.lit ([[[320]]] : P3)),(.lit ([[[2]]] : P3))⟩,
  ⟨1197,(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨743,(.lit ([[[-4999],[5005]],[[0,-200]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[10]]] : P3))⟩,
  ⟨742,(.lit ([[[4999]]] : P3)),(.lit ([[[5005]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨741,(.lit ([[[],[1001]],[[0,-40]]] : P3)),(.lit ([[[1001]]] : P3)),(.lit ([[[25025]]] : P3))⟩,
  ⟨740,(.lit ([[[],[1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1002001]]] : P3))⟩,
  ⟨739,(.lit ([[[],[-1]]] : P3)),(.lit ([[[1]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨738,(.lit ([[[10860850],[-100100]],[],[[3]]] : P3)),(.lit ([[[100100]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨737,(.lit ([[[100100]]] : P3)),(.lit ([[[10860850],[-100100]],[],[[3]]] : P3)),(.lit ([[[1]]] : P3))⟩,
  ⟨736,(.lit ([[[241040800]],[[-5005]]] : P3)),(.lit ([[[173773600],[-1601600]],[],[[48]]] : P3)),(.lit ([[[20]]] : P3))⟩] ++ [c2top]
theorem c2ok : RegCert.check rows boxes c2ins [] c2cert=true := by (try rw [RowLit.Lower_10_520_1000.out_eq]); (try rw [RowLit.Lower_10_520_1000.check_eq]); decide +kernel

/-- The nook axis of channel 2 meets the base and receiver central rays exactly. -/
theorem lower2 {args xs : List ℚ} (m : Model args xs rows boxes cache) :
    let s : ℝ := getRat args 0
    let J : ℝ := getRat args 1
    let Q : ℝ := getRat args 4
    let b : ℝ := ((((1000:ℕ):ℝ)-1/5)/1001+5/2002*Q+40/1001*J*s : ℝ)
    let H : ℝ := (getRat xs 525 : ℝ)-1
    s/320-b*H=301/2-((217/2:ℝ) + (3/100100:ℝ)*s^2)*H := by
  intro s J Q b H
  have hin : ∀ k P d, (k,P,d)∈c2ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev s b J P := by
    intro k P d hk
    simp only [c2ins,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hk
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
      simp [Ex.ev,ev3,ev2,ev1,b] <;> ring
  have h := RegCert.check_sound m.run m.bounds hin c2cert [] (by simp) c2ok c2top
    (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨hx,hD⟩ := h
  have hreg : c2top.reg=525 := rfl
  rw [hreg] at hx
  have eN : Ex.ev s b J c2top.N=((414814400:ℝ) + (-1601600:ℝ)*b + (-5005:ℝ)*s + (48:ℝ)*s^2) := by simp [c2top,Ex.ev,ev3,ev2,ev1]; ring
  have eD : Ex.ev s b J c2top.D=((173773600:ℝ) + (-1601600:ℝ)*b + (48:ℝ)*s^2) := by simp [c2top,Ex.ev,ev3,ev2,ev1]; ring
  have key : (s/320-b*H-(301/2-((217/2:ℝ) + (3/100100:ℝ)*s^2)*H))*Ex.ev s b J c2top.D=0 := by
    rw [eN,eD] at hx; rw [eD]; simp only [H]; linear_combination (((217/2:ℝ) + (3/100100:ℝ)*s^2)-b)*hx
  rcases mul_eq_zero.mp key with h|h
  · linarith
  · exact absurd h hD

end ArtGallery.Orthogonal.BoundaryPoint.CopyInc.Lower_10_520_1000
end
