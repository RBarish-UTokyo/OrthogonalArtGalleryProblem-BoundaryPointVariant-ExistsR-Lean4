module

public import ArtGallery.Orthogonal.BoundaryPoint.ChimneyCells
public import ArtGallery.Orthogonal.BoundaryPoint.BankPitch
public import Mathlib.Tactic.Linarith

/-! # Uniform visibility over the base-bay floor dividers

The rightmost hub step guard sees the lower band over each divider. A base
guard in the bay immediately to the right sees the higher band. The same
bounds apply to every position on that base slot and every compiled size.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubDivider
open ChimneyRegion

/-- The segment descends below the low ceiling before it exits the high step. -/
theorem from_step {x y bottom : ℝ} (hx : 110 ≤ x) (hb : bottom ≤ y) (hy : y ≤ -6)
    (hslope : 7*(x-100) ≤ 10*(1-y)) :
    ArtGallery.segment (100,1) (x,y) ⊆ cell 100 110 bottom 1 ∪ cell 110 x bottom (-6) := by
  rintro p ⟨t,ht,ht',rfl⟩
  change (100+t*(x-100),1+t*(y-1)) ∈ _
  have xlo := mul_nonneg ht (show 0 ≤ x-100 by linarith)
  have xhi := mul_le_mul_of_nonneg_right ht' (show 0 ≤ x-100 by linarith)
  have ylo := mul_le_mul_of_nonpos_right ht' (show y-1 ≤ 0 by linarith)
  have yhi := mul_nonpos_of_nonneg_of_nonpos ht (show y-1 ≤ 0 by linarith)
  by_cases h : 100+t*(x-100) ≤ 110
  · exact Or.inl ⟨by linarith, h, by linarith, by linarith⟩
  · have hs := mul_le_mul_of_nonneg_left hslope ht
    exact Or.inr ⟨by linarith, by linarith, by linarith, by nlinarith only [hs,h]⟩

/-- Starting at least two units right of a unit-width divider gives clearance
for every target at least one unit above the base floor. -/
theorem from_bay {u d a floor y : ℝ} (hd : 2 ≤ d) (ha : 0 ≤ a ∧ a ≤ 1)
    (hy : floor+1 ≤ y) :
    ArtGallery.segment (u+d,floor) (u-a,y) ⊆
      cell u (u+d) floor y ∪ cell (u-1) u (floor+1/4) y := by
  rintro p ⟨t,ht,ht',rfl⟩
  change (u+d+t*((u-a)-(u+d)),floor+t*(y-floor)) ∈ _
  have hx := mul_nonpos_of_nonneg_of_nonpos ht (show (u-a)-(u+d) ≤ 0 by linarith [ha.1])
  have hx' := mul_le_mul_of_nonpos_right ht' (show (u-a)-(u+d) ≤ 0 by linarith [ha.1])
  have hv := mul_nonneg ht (show 0 ≤ y-floor by linarith)
  have hv' := mul_le_mul_of_nonneg_right ht' (show 0 ≤ y-floor by linarith)
  by_cases h : u ≤ u+d+t*((u-a)-(u+d))
  · exact Or.inl ⟨h,by linarith,by linarith,by linarith⟩
  · have hta := mul_le_mul_of_nonneg_right ht' ha.1
    have hh : 1/2 ≤ t := by
      by_contra! hh
      have hg := mul_lt_mul_of_pos_right hh (show 0 < d by linarith)
      nlinarith only [hg,h,hta,ha.2,hd]
    have hgain := mul_le_mul_of_nonneg_left (show 1 ≤ y-floor by linarith) ht
    exact Or.inr ⟨by nlinarith [ha.2],by linarith,by nlinarith,by linarith⟩

theorem last_slot_bound {n b rank : ℝ} (hn : 1 ≤ n) (hb : b ≤ 1000)
    (hr : rank ≤ n) : BankPitch.slot n b rank + 3/2 ≤ 11/10*BankPitch.depth n := by
  have hprod := mul_le_mul_of_nonneg_left (show b-1/5 ≤ 1000 by linarith)
    (show 0 ≤ BankPitch.scale n by unfold BankPitch.scale; positivity)
  have hrank := mul_le_mul_of_nonneg_right hr (show 0 ≤ BankPitch.pitch n by unfold BankPitch.pitch; linarith)
  have hw := BankPitch.width_le_half hn
  unfold BankPitch.slot BankPitch.scale BankPitch.pitch BankPitch.depth at *
  nlinarith [mul_nonneg (show 0 ≤ n-1 by linarith) (show 0 ≤ n by linarith)]

/-- If the carrier rectangles are included in the physical hub, two canonical
guards cover every height over the divider. Here u is the right divider edge
and floor = 1-D. -/
theorem covered {P : Polygon} {u d a D y : ℝ} (hD : 100 ≤ D)
    (hx : 110 ≤ u-a) (hmax : u-a ≤ 11/10*D)
    (hd : 2 ≤ d) (ha : 0 ≤ a ∧ a ≤ 1)
    (hy : 1-D+1/4 ≤ y ∧ y ≤ -6)
    (hhi : cell 100 110 (1-D+1/4) 1 ⊆ P.filled)
    (hlo : cell 110 (u-a) (1-D+1/4) (-6) ⊆ P.filled)
    (hbay : cell u (u+d) (1-D) (-6) ⊆ P.filled)
    (hdiv : cell (u-1) u (1-D+1/4) (-6) ⊆ P.filled) :
    P.Sees (100,1) (u-a,y) ∨ P.Sees (u+d,1-D) (u-a,y) := by
  by_cases h : y ≤ 1-D+1
  · left
    exact (from_step hx hy.1 hy.2 (by linarith)).trans (Set.union_subset hhi hlo)
  · right
    apply (from_bay hd ha (by linarith : 1-D+1 ≤ y)).trans
    apply Set.union_subset
    · exact fun p hp => hbay ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.trans hy.2⟩
    · exact fun p hp => hdiv ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.trans hy.2⟩

end ArtGallery.Orthogonal.BoundaryPoint.HubDivider
end
