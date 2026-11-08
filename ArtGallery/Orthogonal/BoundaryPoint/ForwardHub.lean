module

public import ArtGallery.Orthogonal.BoundaryPoint.HubCover
public import ArtGallery.Orthogonal.BoundaryPoint.HubAccess
public import ArtGallery.Vis.API

/-! # Hub facts for the canonical guards

Every base guard on the floor of its slot sees every point of every door segment (the three
strips of `HubAccess`), the slots satisfy the size bound of `HubCover.hub_cover`, and base and
step guards stand on the hub boundary. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ForwardHub
open Set RectContour BoundaryChart BankCoordinates HubComb HubPoints HubCells HubCover ChimneyRegion

section
variable {n k : Nat} {ss : List ℚ}

theorem W_le (hn : 65≤n) : (W n:ℝ)≤1/2 := by
  have : (65:ℝ)≤n := by exact_mod_cast hn
  unfold W; push_cast
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- A base guard on the floor of its slot sees a point of the door segment of a door `j`. -/
theorem door_sees (hn : 65≤n) (placed : Placed ss) {p : ℚ} (hp : p∈ss) {t : ℝ} (ht : 0≤t ∧ t≤3/2)
    {j : Nat} (hj : j<k+1) {x : ℝ} (hx : (door j:ℝ)≤x ∧ x≤(door j:ℝ)+(W n:ℝ))
    (width : (p:ℝ)+t-x≤2*(D n:ℝ)) :
    (HP n k ss).Sees ((p:ℝ)+t,((1-D n:ℚ):ℝ)) (x,1) := by
  have F7 := F_lt hn
  have FD : ((1-D n:ℚ):ℝ)=1-(D n:ℝ) := by push_cast; ring
  have hW := W_le hn
  have dj := door_le j
  have dk := door_mono (Nat.lt_succ_iff.mp hj)
  have pf := slot_far placed hp
  have pl := slot_last placed hp
  have hD : (8:ℝ)≤D n := by linarith
  rw [Polygon.sees_comm]
  rw [FD]
  apply HubAccess.three_strips hD (by linarith) width
  · rw [← FD]
    exact mono (cap_column hn placed hj) (by linarith) (by linarith) le_rfl le_rfl
  · rw [← FD]
    exact mono (band_cell hn placed) (by linarith) (by linarith) le_rfl le_rfl
  · rw [← FD]
    refine gap_cell hn placed (by linarith) (by linarith) (by linarith) ?_
    intro x hx
    rcases slot_gap placed hp (List.mem_of_mem_tail hx) with e|h|h
    · subst e; left; linarith
    · right; linarith
    · left; linarith

/-- A base guard on its floor stands on the hub boundary. -/
theorem base_on (placed : Placed ss) {p : ℚ} (hp : p∈ss) {t : ℝ} (ht : 0≤t ∧ t≤3/2) :
    ((p:ℝ)+t,((1-D n:ℚ):ℝ))∈(HP n k ss).boundary :=
  floor_slot placed hp ⟨by linarith,by push_cast; linarith⟩

/-- A step guard stands on the hub boundary. -/
theorem step_on {j : Nat} (hj : j<k+1) : ((door j:ℝ)+100,(1:ℝ))∈(HP n k ss).boundary :=
  cap_top hj ⟨by push_cast; linarith,by push_cast; linarith⟩

end

/-- The slot bound of `HubCover.hub_cover`. -/
theorem big {n bank rank : Nat} (hn : 1≤n) (hb : bank≤1000) (hr : rank≤n) :
    (slotX n bank rank:ℝ)+20≤11/10*(D n:ℝ) := by
  have h1 : (1:ℝ)≤n := by exact_mod_cast hn
  have h2 : (bank:ℝ)≤1000 := by exact_mod_cast hb
  have h3 : (rank:ℝ)≤n := by exact_mod_cast hr
  have hw : (W n:ℝ)≤1/2 := by
    unfold W; push_cast; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hW : (slotX n bank rank:ℝ)=(W n:ℝ)+50*(n:ℝ)^2*((bank:ℝ)-1/5)+(rank:ℝ)*(125*(n:ℝ)) := by
    unfold slotX BankCoordinates.k delta; push_cast; ring
  have hD : (D n:ℝ)=50050*(n:ℝ)^2 := by unfold D BankCoordinates.k; push_cast; ring
  rw [hW,hD]
  have hprod := mul_le_mul_of_nonneg_left (show (bank:ℝ)-1/5≤1000 by linarith)
    (show 0≤50*(n:ℝ)^2 by positivity)
  have hrank := mul_le_mul_of_nonneg_right h3 (show 0≤125*(n:ℝ) by positivity)
  nlinarith [mul_nonneg (show 0≤(n:ℝ)-1 by linarith) (show 0≤(n:ℝ) by linarith)]

end ArtGallery.Orthogonal.BoundaryPoint.ForwardHub
end
