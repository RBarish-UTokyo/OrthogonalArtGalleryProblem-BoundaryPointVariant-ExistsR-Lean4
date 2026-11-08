module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomCell
public import ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.InvLe
public import ArtGallery.Orthogonal.BoundaryPoint.InversionCriticalAlgebra

/-! Under the satisfied relation `x*y ≤ 1` the two inversion guards cover the cells left of the
axis: the first ray is below the second at the axis and steeper. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.InvLe
open RoomFamily.InvLe RoomRelation.InvLe RoomCoordinates SlotLines RoomCell ArtGallery DerivedAlgebra
set_option linter.unnecessarySeqFocus false

theorem coords_A (s t : ℝ) : guard s 0 t=(493/2+s^2/20020+t*(2/3)*(3/20020*s^2),-4) := by
  rw [position_A]; ext <;> simp only [evalR] <;> push_cast <;> ring_nf
theorem coords_B (s t : ℝ) : guard s 1 t=
    (501/2+s^2/20020-s^4/400800400+t*(2/3)*(3/20020*s^2),-4) := by
  rw [position_B]; ext <;> simp only [evalR] <;> push_cast <;> ring_nf

theorem cell {s x y : ℝ} (hs : 0<s) (hu : s≤1/65) (hx : InRange x) (hy : InRange y) (rel : x*y≤1)
    {z : Point} (hz : z.1≤501/2) :
    det (guard s 0 (x-1/2)) z (497/2,-95/24)≤0 ∨
      det (guard s 1 (y-1/2)) z (501/2+s^4/400800400,-47/12)≤0 := by
  let v := s^2/50050
  let E := 2/(5*v)
  have hv : 0<v := by positivity
  have ePos : 100≤E := by
    apply (le_div_iff₀ (show 0<5*v by positivity)).mpr
    dsimp [v]; nlinarith [mul_le_mul hu hu hs.le (by norm_num : (0:ℝ)≤1/65)]
  have wA : ((497/2:ℝ),(-95/24:ℝ))=world v (-E,1/2) := by
    ext <;> simp only [world,E] <;> field_simp <;> ring
  have wB : ((501/2+s^4/400800400:ℝ),(-47/12:ℝ))=world v (1/(2*E),1) := by
    ext <;> simp only [world,E,v] <;> field_simp <;> ring
  have id := physical_axis s x y hs hu hx hy
  simp only at id
  rw [← wA,← wB] at id
  have den := InversionCriticalAlgebra.denominators_pos ePos hx hy
  have pos : 0<2*(E-x)*(y-1/E) := mul_pos (mul_pos (by norm_num) den.1) den.2
  have ord : rayY (guard s 0 (x-1/2)) (497/2,-95/24) (501/2)≤
      rayY (guard s 1 (y-1/2)) (501/2+s^4/400800400,-47/12) (501/2) := by
    have h : (x*y-1)/(2*(E-x)*(y-1/E))≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) pos.le
    have k := id.trans_le h
    linarith
  have s2 : s^2≤1/4225 := by nlinarith
  have s4 : s^4≤s^2 := by nlinarith [sq_nonneg s]
  have tA : 0≤(x-1/2)*s^2 ∧ (x-1/2)*s^2≤1/2000 :=
    ⟨mul_nonneg (by linarith [hx.1]) (sq_nonneg s),by nlinarith [hx.2]⟩
  have tB : 0≤(y-1/2)*s^2 ∧ (y-1/2)*s^2≤1/2000 :=
    ⟨mul_nonneg (by linarith [hy.1]) (sq_nonneg s),by nlinarith [hy.2]⟩
  rw [coords_A,coords_B] at ord ⊢
  unfold rayY at ord
  have dA : 0<(497/2:ℝ)-(493/2+s^2/20020+(x-1/2)*(2/3)*(3/20020*s^2)) := by nlinarith
  have dB : (501/2+s^4/400800400:ℝ)-(501/2+s^2/20020-s^4/400800400+(y-1/2)*(2/3)*(3/20020*s^2))<0 := by
    nlinarith [sq_nonneg s,pow_pos hs 2]
  rcases axis_union (z:=z) hz ord (by
      simp only
      exact (div_neg_of_pos_of_neg (by norm_num) dB).le.trans (div_pos (by norm_num) dA).le) with h|h
  · left
    rw [det_ray _ _ _ (sub_ne_zero.mp dA.ne')]
    exact mul_nonpos_of_nonneg_of_nonpos dA.le (by simp only at h ⊢; linarith)
  · right
    rw [det_ray _ _ _ (sub_ne_zero.mp dB.ne)]
    exact mul_nonpos_of_nonpos_of_nonneg dB.le (by simp only at h ⊢; linarith)

end ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.InvLe
end
