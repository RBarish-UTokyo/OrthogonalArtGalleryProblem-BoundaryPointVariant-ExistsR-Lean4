module

public import ArtGallery.Orthogonal.BoundaryPoint.InverseGap
public import ArtGallery.Orthogonal.BoundaryPoint.CriticalOwnership
public import ArtGallery.Orthogonal.BoundaryPoint.RoomForeign.InvRevGe
public import ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.InvRevGe

/-! Soundness of the actual four-role inverse room at all generated scales. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomSound.InvRevGe
open RoomFamily.InvRevGe RoomRelation.InvRevGe RoomPolynomials RoomCoordinates AxisBlock InverseGap
open ArtGallery.Orthogonal.Hard DerivedAlgebra SlotLines RoomGrid
set_option maxRecDepth 15000
set_option maxHeartbeats 2000000

def leftEdge : P := [(501/2), 0, 0, 0, (-1/400800400)]
def axis : P := [(501/2)]
def bottom : P := [(-11/3), 0, (1/400400)]
def top : P := [(-11/3), 0, (1/48048)]
def aQuery : AxisBlock.Query := ⟨0,([(497/2)], [(-23/6)]),axis,bottom,top,true,false,true⟩
def bQuery : AxisBlock.Query := ⟨1,([(501/2), 0, 0, 0, (-1/400800400)], [(-11/3)]),axis,bottom,top,true,true,false⟩

theorem a_blocks : ok xAxis yAxis cells roles aQuery=true := by decide +kernel
theorem b_blocks : ok xAxis yAxis cells roles bQuery=true := by decide +kernel
theorem a_margins : margins xAxis yAxis roles aQuery=true := by decide +kernel
theorem b_margins : margins xAxis yAxis roles bQuery=true := by decide +kernel
theorem positive_width : ltP leftEdge axis=true := by decide +kernel
theorem box_fits : fits xAxis yAxis leftEdge axis bottom top (10,12,8,12)=true := by decide +kernel
theorem box_member : (10,12,8,12) ∈ cells := by decide +kernel

noncomputable def spot (s : ℝ) (i : Nat) : Set Point :=
  let f := gridPt (xAxis.coordsR s) (yAxis.coordsR s)
  ArtGallery.segment (f (RoomExclusion.nodeAt roles i 1)) (f (RoomExclusion.nodeAt roles i 2))

def critical (s : ℝ) (z : Point) : Prop :=
  evalR s leftEdge≤z.1 ∧ z.1<evalR s axis ∧ evalR s bottom≤z.2 ∧ z.2≤evalR s top

theorem forces (n : Nat) (hn : 65≤n) (x y : ℝ) (hx : InRange x) (hy : InRange y)
    (u v : Point) (hU : u∈spot (1/n) 2) (hV : v∈spot (1/n) 3)
    (cover : ∀ z∈(room n).filled, critical (1/n) z → (room n).Sees (guard (1/n) 0 (x-1/2)) z ∨
      (room n).Sees (guard (1/n) 1 (y-1/2)) z ∨ (room n).Sees u z ∨ (room n).Sees v z) :
    1≤x*(5/2-y) := by
  let s : ℝ := 1/n
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have positive : (0:ℝ)<n := by linarith
  have hs : 0<s := by dsimp [s]; positivity
  have hu : s≤1/65 := one_div_le_one_div_of_le (by norm_num) hn'
  let gA := guard s 0 (x-1/2)
  let gB := guard s 1 (y-1/2)
  have posA := slot_member (s:=s) xAxis yAxis roles 0 hx
  have posB := slot_member (s:=s) xAxis yAxis roles 1 hy
  let A := pt s aQuery.corner
  let B := pt s bQuery.corner
  let X := evalR s axis
  let rA := rayY gA A X
  let rB := rayY gB B X
  have aBound : evalR s bottom<rA ∧ rA<evalR s top := interior hs hu a_margins posA
  have bBound : evalR s bottom<rB ∧ rB<evalR s top := interior hs hu b_margins posB
  have filled := RoomFill.InvRevGe.filled_eq n hn
  have coord : X=(501/2:ℝ) := by simp [X,axis,evalR]
  have exclude := RoomForeign.InvRevGe.exclude n hn
  have region : ∀ x', evalR s leftEdge≤x' → x'<X → ∀ y', evalR s bottom≤y' → y'≤evalR s top →
      (room n).Sees gB (x',y') ∨ (room n).Sees gA (x',y') := by
    intro x' hl hr y' hb ht
    have seen := cover (x',y') (free_box hs hu filled box_member box_fits _ _ hl hr.le hb ht) ⟨hl,hr,hb,ht⟩
    have hxx : x'<501/2 := hr.trans_eq coord
    have U := exclude 2 (by simp) u hU (x',y') hxx hb
    have V := exclude 3 (by simp) v hV (x',y') hxx hb
    rcases seen with a|b|c|d
    · exact Or.inr a
    · exact Or.inl b
    · exact (U c).elim
    · exact (V d).elim
  have ordered : rB≤rA := by
    apply axis_order (lt_sound hs hu positive_width) bBound aBound region
    · intro Y hl ht see
      exact sound hs hu filled b_blocks posB (target hl ht) see
    · intro Y hl ht see
      exact sound hs hu filled a_blocks posA (target hl ht) see
  let factor := s^2/50050
  let E := 2/(5*factor)
  have hf : 0<factor := by dsimp [factor]; positivity
  have ePos : 100≤E := by
    apply (le_div_iff₀ (show 0<5*factor by positivity)).mpr
    dsimp [factor]; nlinarith [mul_le_mul hu hu hs.le (by norm_num : (0:ℝ)≤1/65)]
  have aWorld : A=world factor (-E, 2) := by
    ext <;> simp [A,aQuery,world,pt,evalR,E,factor] <;> field_simp [hs.ne'] <;> ring
  have bWorld : B=world factor (-1/(2*E), 4) := by
    ext <;> simp [B,bQuery,world,pt,evalR,E,factor] <;> field_simp [hs.ne'] <;> ring
  have id := physical_axis s x y hs hu hx hy
  change (rayY gA (world factor (-E,2)) (501/2) -
    rayY gB (world factor (-1/(2*E),4)) (501/2))*12 = _ at id
  rw [← aWorld,← bWorld,← coord] at id
  change (rA-rB)*12=_ at id
  have den := InversionCriticalAlgebra.denominators_pos ePos hx (complement_inRange hy)
  change 0<E-x ∧ 0<(5/2-y)-1/E at den
  have pos := mul_pos den.1 den.2
  have sign := (le_div_iff₀ pos).mp (id ▸ (mul_nonneg (sub_nonneg.mpr ordered) (by norm_num)))
  linarith

theorem spot_marks (i : Fin 4) : (RoomExclusion.nodeAt roles i 1, RoomExclusion.nodeAt roles i 2) ∈
    GridPins.requirements roles := by fin_cases i <;> decide +kernel

theorem joined_forces (n : Nat) (hn : 65≤n) (P : Polygon) (tree : WindowTree.Attachments (room n).filled P.filled)
    (H : Set Point) (G : Nat → Point) (pins : ∀ i, i<4 → G i∈spot (1/n) i)
    (cover : ∀ z∈P.filled, ∃ g∈H, P.Sees g z)
    (foreign : ∀ z∈(room n).filled, critical (1/n) z → ∀ g∈H, (∀ i, i<4 → g≠G i) → ¬P.Sees g z)
    (x y : ℝ) (hx : InRange x) (hy : InRange y) (a : G 0=guard (1/n) 0 (x-1/2))
    (b : G 1=guard (1/n) 1 (y-1/2)) : 1≤x*(5/2-y) := by
  have actors (i : Nat) (hi : i<4) : G i∈(room n).filled :=
    Or.inl (guards_and_witnesses_on_boundary n hn _ (spot_marks ⟨i,hi⟩) (pins i hi))
  apply forces n hn x y hx hy (G 2) (G 3) (pins 2 (by decide)) (pins 3 (by decide))
  intro z hz criticalZ
  obtain ⟨i,hi,seen⟩ := CriticalOwnership.restrict_to_room tree (critical (1/n)) H 4 G actors cover foreign z hz criticalZ
  interval_cases i
  · exact Or.inl (a ▸ seen)
  · exact Or.inr (Or.inl (b ▸ seen))
  · exact Or.inr (Or.inr (Or.inl seen))
  · exact Or.inr (Or.inr (Or.inr seen))

end ArtGallery.Orthogonal.BoundaryPoint.RoomSound.InvRevGe
end
