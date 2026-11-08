module

public import ArtGallery.Orthogonal.BoundaryPoint.CompiledAddresses

/-! # Actual order of the hub floor slots in the word generator -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PlacedSlots
open CatalogPlan CatalogRanks CompiledSize BankCoordinates

def ordered (a b : Addr) : Prop := a.1<b.1 ∨ (a.1=b.1 ∧ a.2<b.2)

theorem addresses (ks : List Key) : (address ks).Pairwise ordered := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro b _
    exact List.pairwise_map.mpr (List.pairwise_lt_range.imp (fun h => Or.inr ⟨rfl,h⟩))
  · have sorted : banks.Pairwise (·<·) := by decide
    apply sorted.imp
    intro b c h x hx y hy
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
    exact Or.inl h

def starts (eqs : List ETRINV.Constraint) : List ℚ :=
  (compile eqs).2.map fun a => slotX (scale eqs) a.1 a.2

theorem right_of_all_wings {eqs : List ETRINV.Constraint} (ne : eqs≠[]) {x : ℚ} (hx : x∈starts eqs) :
    1970<x := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  have bank := (CompiledAddresses.address_spec eqs ha).1
  have lower : 1≤a.1 := by simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at bank; omega
  let n := scale eqs
  have hn : (65:ℚ)≤n := by exact_mod_cast (scale_bounds ne).1
  have hb : (1:ℚ)≤a.1 := by exact_mod_cast lower
  have pos : (0:ℚ)<n := lt_of_lt_of_le (by norm_num) hn
  have wpos : 0<W n := by unfold W; positivity
  change 1970<slotX n a.1 a.2
  unfold slotX BankCoordinates.k delta
  have term : (0:ℚ)≤(a.2:ℚ)*(125*(n:ℚ)) := by positivity
  nlinarith [mul_nonneg (show 0≤50*(n:ℚ)*n by positivity) (sub_nonneg.mpr hb),
    mul_self_le_mul_self (by norm_num : (0:ℚ)≤65) hn]

theorem increasing {eqs : List ETRINV.Constraint} (ne : eqs≠[]) :
    (starts eqs).Pairwise (fun a b => a+delta (scale eqs)≤b) := by
  apply List.pairwise_map.mpr
  have sorted : (compile eqs).2.Pairwise ordered := addresses _
  apply sorted.imp_of_mem
  intro a b ha hb ord
  have ⟨aBank,aRank⟩ := CompiledAddresses.address_spec eqs ha
  have bBank := (CompiledAddresses.address_spec eqs hb).1
  let n := scale eqs
  have natural : 1≤n := by have h := (scale_bounds ne).1; change 65≤n at h; omega
  have pos : (1:ℝ)≤n := by exact_mod_cast natural
  change slotX n a.1 a.2+delta n≤slotX n b.1 b.2
  apply (Rat.cast_le (K:=ℝ)).mp
  rw [Rat.cast_add,cast_slotX,cast_slotX]
  have pitch : (delta n:ℝ)=BankPitch.pitch n := by simp [delta,BankPitch.pitch]
  rw [pitch]
  rcases ord with bank|⟨eq,ij⟩
  · have gap : a.1+9≤b.1 := by
      simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at aBank bBank
      omega
    exact BankPitch.different_banks pos (by exact_mod_cast gap) (by exact_mod_cast aRank.le) (by positivity)
  · rw [eq]
    exact BankPitch.same_bank pos (by exact_mod_cast ij)

end ArtGallery.Orthogonal.BoundaryPoint.PlacedSlots
end
