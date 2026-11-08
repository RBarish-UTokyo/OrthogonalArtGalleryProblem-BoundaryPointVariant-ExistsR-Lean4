module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomCell
public import ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.InvRevGe
public import ArtGallery.Orthogonal.BoundaryPoint.InversionCriticalAlgebra

/-! Under the satisfied relation `x*(5/2-y) ≥ 1` the two inversion guards cover the cells left of
the axis: the ray of the second guard is below the first at the axis and steeper. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.InvRevGe
open RoomFamily.InvRevGe RoomRelation.InvRevGe RoomCoordinates SlotLines RoomCell ArtGallery DerivedAlgebra
set_option linter.unnecessarySeqFocus false

theorem coords_A (s t : ℝ) : guard s 0 t=(493/2+s^2/20020+t*(2/3)*(3/20020*s^2),-4) := by
  rw [position_A]; ext <;> simp only [evalR] <;> push_cast <;> ring_nf
theorem coords_B (s t : ℝ) : guard s 1 t=
    (501/2-s^2/5005+s^4/400800400+t*(2/3)*(3/20020*s^2),-4) := by
  rw [position_B]; ext <;> simp only [evalR] <;> push_cast <;> ring_nf

theorem cell {s x y : ℝ} (hs : 0<s) (hu : s≤1/65) (hx : InRange x) (hy : InRange y) (rel : 1≤x*(5/2-y))
    {z : Point} (hz : z.1≤501/2) :
    0≤det (guard s 0 (x-1/2)) z (497/2,-23/6) ∨
      det (guard s 1 (y-1/2)) z (501/2-s^4/400800400,-11/3)≤0 := by
  let v := s^2/50050
  let E := 2/(5*v)
  have hv : 0<v := by positivity
  have ePos : 100≤E := by
    apply (le_div_iff₀ (show 0<5*v by positivity)).mpr
    dsimp [v]; nlinarith [mul_le_mul hu hu hs.le (by norm_num : (0:ℝ)≤1/65)]
  have wA : ((497/2:ℝ),(-23/6:ℝ))=world v (-E,2) := by
    ext <;> simp only [world,E] <;> field_simp <;> ring
  have wB : ((501/2-s^4/400800400:ℝ),(-11/3:ℝ))=world v (-1/(2*E),4) := by
    ext <;> simp only [world,E,v] <;> field_simp <;> ring
  have id := physical_axis s x y hs hu hx hy
  simp only at id
  rw [← wA,← wB] at id
  have hy' : InRange (5/2-y) := ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have den := InversionCriticalAlgebra.denominators_pos ePos hx hy'
  have pos : 0<(E-x)*((5/2-y)-1/E) := mul_pos den.1 den.2
  have ord : rayY (guard s 1 (y-1/2)) (501/2-s^4/400800400,-11/3) (501/2)≤
      rayY (guard s 0 (x-1/2)) (497/2,-23/6) (501/2) := by
    have h : 0≤2*(x*(5/2-y)-1)/((E-x)*((5/2-y)-1/E)) := div_nonneg (by linarith) pos.le
    have k := h.trans_eq id.symm
    linarith
  have s2 : s^2≤1/4225 := by nlinarith
  have s4 : s^4≤s^2/4225 := by nlinarith [sq_nonneg s]
  have tA : 0≤(x-1/2)*s^2 ∧ (x-1/2)*s^2≤3/2*s^2 :=
    ⟨mul_nonneg (by linarith [hx.1]) (sq_nonneg s),by nlinarith [hx.2]⟩
  have tB : 0≤(y-1/2)*s^2 ∧ (y-1/2)*s^2≤3/2*s^2 :=
    ⟨mul_nonneg (by linarith [hy.1]) (sq_nonneg s),by nlinarith [hy.2]⟩
  rw [coords_A,coords_B] at ord ⊢
  unfold rayY at ord
  have dA : 1<(497/2:ℝ)-(493/2+s^2/20020+(x-1/2)*(2/3)*(3/20020*s^2)) := by nlinarith
  have dB : 0<(501/2-s^4/400800400:ℝ)-(501/2-s^2/5005+s^4/400800400+(y-1/2)*(2/3)*(3/20020*s^2)) := by
    nlinarith [sq_nonneg s,pow_pos hs 2]
  have dB' : (501/2-s^4/400800400:ℝ)-(501/2-s^2/5005+s^4/400800400+(y-1/2)*(2/3)*(3/20020*s^2))≤1/3 := by
    nlinarith [sq_nonneg s,pow_pos hs 4]
  have mA : (-23/6-(-4:ℝ))/((497/2:ℝ)-(493/2+s^2/20020+(x-1/2)*(2/3)*(3/20020*s^2)))≤1 := by
    rw [div_le_one (by linarith)]; linarith
  have mB : 1≤(-11/3-(-4:ℝ))/((501/2-s^4/400800400:ℝ)-(501/2-s^2/5005+s^4/400800400+(y-1/2)*(2/3)*(3/20020*s^2))) := by
    rw [one_le_div dB]; linarith
  rcases axis_union (z:=z) hz ord (by simp only; linarith) with h|h
  · right
    rw [det_ray _ _ _ (sub_ne_zero.mp dB.ne')]
    exact mul_nonpos_of_nonneg_of_nonpos dB.le (by simp only at h ⊢; linarith)
  · left
    rw [det_ray _ _ _ (sub_ne_zero.mp (by linarith : (0:ℝ)<_).ne')]
    exact mul_nonneg (by linarith) (by simp only at h ⊢; linarith)

end ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.InvRevGe
end
