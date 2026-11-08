module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomCell
public import ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.Ordinary

/-! Under the satisfied relation the sign conditions of the critical room cells of the family
cover them: the addition triangle (balanced slopes) and the relay mouth (equal copied values). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.Ordinary
open RoomFamily.Ordinary RoomRelation.Ordinary RoomCoordinates SlotLines RoomCell ArtGallery
set_option linter.unnecessarySeqFocus false

theorem coords_x (s t : ℝ) : guard s 5 t=(358+t*(2/3)*(9/100100*s^2),-2) := by
  rw [position_x]; ext <;> simp only [evalR] <;> push_cast <;> ring_nf
theorem coords_r (s t : ℝ) : guard s 4 t=(100879/70+t*(2/3)*(27/557375*s^2),-33/245) := by
  rw [position_r]; ext <;> simp only [evalR] <;> push_cast <;> ring_nf
theorem coords_q (s t : ℝ) : guard s 3 t=(272+t*(2/3)*(81/1001000*s^2),-17/10) := by
  rw [position_q]; ext <;> simp only [evalR] <;> push_cast <;> ring_nf

theorem triangle {s tx tr tz : ℝ} (hs : 0<s) (hu : s≤1/65)
    (hx : 0≤tx ∧ tx≤3/2) (hr : 0≤tr ∧ tr≤3/2) (rel : tz≤tx+tr+(1/2)) {z : Point} (hy : 45/100≤z.2) :
    (0≤det (guard s 5 tx) z (766,0) ∧ det (guard s 5 tx) z (1655/2,0)≤0) ∨
      0≤det (guard s 4 tr) z (2639/2,0) ∨ det (guard s 6 tz) z (1655/2,0)≤0 := by
  have id := balance s tx tr tz
  have neg : (4/3)*(s^2/50050)*(tz-tx-tr-(1/2))≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have small : s^2≤1/4225 := by nlinarith
  have bx : 0≤tx*s^2 ∧ tx*s^2≤1/2000 := ⟨mul_nonneg hx.1 (sq_nonneg s),by nlinarith⟩
  have br : 0≤tr*s^2 ∧ tr*s^2≤1/2000 := ⟨mul_nonneg hr.1 (sq_nonneg s),by nlinarith⟩
  have gz2 : (guard s 6 tz).2=-3 := by rw [position_z]
  unfold xSlope at id
  rw [coords_x,coords_r] at id ⊢
  have H := triangle_union (gx:=(358+tx*(2/3)*(9/100100*s^2),-2)) (gr:=(100879/70+tr*(2/3)*(27/557375*s^2),-33/245))
    (gz:=guard s 6 tz) (z:=z) (ax:=766) (ar:=2639/2) (az:=1655/2) (fy:=0)
    (by norm_num) (by norm_num) (by rw [gz2]; norm_num) (by norm_num)
    (by simp only [zero_sub] at id ⊢; linarith [neg]) (by linarith)
  rcases H with h|h|h
  · by_cases h2 : det (358+tx*(2/3)*(9/100100*s^2),(-2:ℝ)) z (1655/2,0)≤0
    · exact Or.inl ⟨h,h2⟩
    · right; left
      refine beyond (y0:=45/100) (by norm_num) (by norm_num) (by simpa using hy) ?_ ?_ (not_le.mp h2)
      · simp only; apply (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr; nlinarith
      · simp only; norm_num; nlinarith [bx.1,bx.2,br.1,br.2]
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem relay {s tq tr : ℝ} (hs : 0<s) (hu : s≤1/65) (hq : 0≤tq ∧ tq≤3/2) (rel : tr=tq)
    {z : Point} (top : z.2≤19834298/9008765) :
    0≤det (guard s 3 tq) z (50352/35,11/5) ∨ det (guard s 4 tr) z (100739/70,11/5)≤0 := by
  have small : s^2≤1/4225 := by nlinarith
  have bq : 0≤tq*s^2 ∧ tq*s^2≤1/2000 := ⟨mul_nonneg hq.1 (sq_nonneg s),by nlinarith⟩
  rw [coords_q,coords_r,rel]
  apply relay_union (h1:=19834298/9008765) (by norm_num) (by norm_num) top
  · simp only; field_simp; ring
  · simp only; apply (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr; nlinarith

end ArtGallery.Orthogonal.BoundaryPoint.RoomCellCover.Ordinary
end
