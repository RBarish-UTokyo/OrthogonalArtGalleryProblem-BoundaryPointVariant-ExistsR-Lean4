module

public import ArtGallery.Orthogonal.BoundaryPoint.HubDivider
public import ArtGallery.Orthogonal.BoundaryPoint.BankCoordinates
public import ArtGallery.Orthogonal.BoundaryPoint.PhysicalLayout

/-! # All base slots can see every hub door

The middle closed strip of the hub joins all the bays. A segment from the
floor to a door lies either in this strip, in the last half unit of its own
bay, or within fourteen horizontal units of the door. This includes base
guards that do not belong to the given constraint. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.HubAccess
open ChimneyRegion PhysicalLayout PrimitiveNetwork FlattenNetwork SourcePortPlan PrivatePorts

private theorem flatten_min {α} (rows : List (List α)) (b : Nat) (h : ∀ l∈rows,b≤l.length) :
    b*rows.length≤rows.flatten.length := by
  induction rows with
  | nil => simp
  | cons l rows ih =>
    have top := h l (by simp)
    have rest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one,List.flatten_cons,List.length_append]
    omega

theorem size_floor (Φ : List ETRINV.Constraint) : 65*Φ.length ≤ size Φ := by
  have logicalLB : 5*Φ.length≤(logical Φ).length := by
    unfold logical
    apply le_trans _ (flatten_min _ 5 ?_)
    · simp
    · intro row hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      rw [clause,length_order,emit_length]
      generalize Φ[i]=e
      cases e <;> simp [lowerConstraint,Net.size,invGe,comp,addLe]
  have physicalLB : 13*(logical Φ).length≤(leaves Φ).length := by
    unfold leaves physical
    apply le_trans _ (flatten_min _ 13 ?_)
    · simp
    · intro row hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      rw [row_length]
      generalize (logical Φ)[i]=a
      cases a <;> simp [ports]
  have bound := le_max_left (leaves Φ).length (slots Φ).length
  unfold size; omega

theorem nonempty_scale {Φ : List ETRINV.Constraint} (h : Φ≠[]) : 65≤size Φ := by
  have positive := List.length_pos_iff.mpr h
  have bound := size_floor Φ
  omega

theorem three_strips {P : Polygon} {door p D : ℝ} (hD : 8≤D) (hd : 0≤p-door)
    (width : p-door≤2*D)
    (step : cell door (door+14) (1-D) 1 ⊆ P.filled)
    (middle : cell door p (1-D+1/4) (-6) ⊆ P.filled)
    (bay : cell (p-1/2) p (1-D) (-6) ⊆ P.filled) :
    P.Sees (door,1) (p,1-D) := by
  rintro z ⟨t,ht,ht',rfl⟩
  let x := door+t*(p-door)
  let y := 1+t*((1-D)-1)
  change (x,y)∈P.filled
  have hx : door≤x ∧ x≤p := by
    dsimp [x]; constructor
    · linarith [mul_nonneg ht hd]
    · linarith [mul_le_mul_of_nonneg_right ht' hd]
  have hy : 1-D≤y ∧ y≤1 := by
    dsimp [y]; constructor
    · linarith [mul_le_mul_of_nonneg_right ht' (by linarith : 0≤D)]
    · linarith [mul_nonneg ht (by linarith : 0≤D)]
  by_cases high : -6<y
  · apply step
    refine ⟨hx.1,?_,hy.1,hy.2⟩
    dsimp [x,y] at *
    nlinarith only [high,mul_le_mul_of_nonneg_left width ht]
  by_cases low : y<1-D+1/4
  · apply bay
    refine ⟨?_,hx.2,hy.1,le_of_not_gt high⟩
    dsimp [x,y] at *
    nlinarith only [low,mul_le_mul_of_nonneg_left width (sub_nonneg.mpr ht')]
  · exact middle ⟨hx.1,hx.2,le_of_not_gt low,le_of_not_gt high⟩

theorem span {n bank rank row : ℝ} (hn : 65≤n) (hb : 1≤bank ∧ bank≤1000)
    (hi : 0≤rank ∧ rank≤n) (hj : 0≤row ∧ row≤n)
    {t k : ℝ} (ht : 0≤t ∧ t≤3/2) (hk : 0≤k ∧ k≤BankPitch.width n) :
    let dist := BankPitch.slot n bank rank+t-(-2000*row+k)
    0≤dist ∧ dist≤2*BankPitch.depth n := by
  have h := BankPitch.base_rate_bound (by linarith : 1≤n) hb hi hj
  have pos : 0<BankPitch.depth n := by unfold BankPitch.depth; positivity
  have large : 10≤BankPitch.depth n := by
    unfold BankPitch.depth; nlinarith [sq_nonneg (n-1)]
  dsimp only
  constructor
  · have low := (le_div_iff₀ pos).mp h.1
    nlinarith only [low,hk.2,ht.1,large]
  · have upper := HubDivider.last_slot_bound (by linarith : 1≤n) hb.2 hi.2
    have shift : 2000*n≤9/10*BankPitch.depth n := by
      unfold BankPitch.depth
      nlinarith [mul_nonneg (show 0≤n-1 by linarith) (show 0≤n by linarith)]
    linarith only [upper,hj.2,ht.2,hk.1,shift]

end ArtGallery.Orthogonal.BoundaryPoint.HubAccess
end
