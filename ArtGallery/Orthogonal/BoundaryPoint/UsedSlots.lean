module

public import ArtGallery.Orthogonal.BoundaryPoint.HubAccess

/-! # Separation of the actual occurrence-ranked base slots -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.UsedSlots
open PrivatePorts PhysicalLayout BankCoordinates

theorem bank_list {ι row} (t : Slot ι row) : bank t∈[1,10,40,200,360,520,1000] := by
  cases t with
  | privatePort _ k => cases k <;> simp [bank]
  | _ => simp [bank]

theorem gap {ι row} {s t : Slot ι row} (h : bank s<bank t) : bank s+9≤bank t := by
  have hs := bank_list s
  have ht := bank_list t
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hs ht
  omega

def start {Φ} (s : Label Φ) := slotX (size Φ) (bank s) (rank s)

theorem separated {Φ} {s t : Label Φ} (hs : s∈slots Φ) (ht : t∈slots Φ) (hne : s≠t) :
    let pitch := BankPitch.pitch (size Φ)
    (start s : ℝ)+pitch≤start t ∨ (start t : ℝ)+pitch≤start s := by
  have a := rank_lt hs
  have b := rank_lt ht
  have hn : (1:ℝ)≤size Φ := by exact_mod_cast (show 1≤size Φ by omega)
  dsimp only [start]
  rw [cast_slotX,cast_slotX]
  rcases lt_trichotomy (bank s) (bank t) with e|e|e
  · exact Or.inl (BankPitch.different_banks hn (by exact_mod_cast gap e)
      (by exact_mod_cast a.le) (by positivity))
  · have d := fun h => hne (distinct_address hs ht e h)
    rcases lt_or_gt_of_ne d with lt|lt
    · left; rw [e]; exact BankPitch.same_bank hn (by exact_mod_cast lt)
    · right; rw [e]; exact BankPitch.same_bank hn (by exact_mod_cast lt)
  · exact Or.inr (BankPitch.different_banks hn (by exact_mod_cast gap e)
      (by exact_mod_cast b.le) (by positivity))

theorem right_of_wings {Φ} (h : Φ≠[]) (s : Label Φ) : 1970<(start s:ℝ) := by
  have hn : (65:ℝ)≤size Φ := by exact_mod_cast HubAccess.nonempty_scale h
  have hb := bank_list s
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hb
  have hb' : (1:ℝ)≤bank s := by exact_mod_cast (show 1≤bank s by omega)
  have hpos : (0:ℝ)<size Φ := by linarith
  have hw : 0<BankPitch.width (size Φ) := by unfold BankPitch.width; positivity
  unfold start; rw [cast_slotX]
  unfold BankPitch.slot BankPitch.scale BankPitch.pitch
  have t : 0≤(50:ℝ)*(size Φ:ℝ)^2 := by positivity
  have r : 0≤(rank s:ℝ)*(125*(size Φ:ℝ)) := by positivity
  nlinarith [mul_nonneg t (sub_nonneg.mpr hb'),mul_self_le_mul_self (by norm_num) hn]

theorem register_rate (n b i j : Nat) (hn : 0<n) :
    let s : ℚ := 1/n
    baseRate n b i j = ((b:ℚ)-1/5)/1001 + (125/50050)*((i:ℚ)*s) +
      (2000/50050)*s*((j:ℚ)*s) := by
  have pos : (n:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp only
  unfold baseRate slotX delta door D k
  push_cast
  field_simp [pos] <;> ring

end ArtGallery.Orthogonal.BoundaryPoint.UsedSlots
end
