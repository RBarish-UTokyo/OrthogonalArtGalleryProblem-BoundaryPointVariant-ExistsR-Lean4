module

public import ArtGallery.Orthogonal.BoundaryPoint.CompiledSize
public import ArtGallery.Orthogonal.BoundaryPoint.UsedSlots

/-! # Separation and normalization of the numeric slots used by the word map -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CompiledAddresses
open CatalogPlan CatalogLogic CatalogRanks CompiledSize BankCoordinates

private theorem group_length {α β : Type} {b : α} (f : α → List β) (l : List α) (h : b∈l) :
    (f b).length≤(l.flatMap f).length := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.flatMap_cons,List.length_append]
    rcases List.mem_cons.mp h with rfl|m
    · omega
    · exact (ih m).trans (Nat.le_add_left _ _)

theorem address_spec (eqs : List ETRINV.Constraint) {a : Addr} (h : a∈(compile eqs).2) :
    a.1∈banks ∧ a.2<scale eqs := by
  let keys := keysOf eqs
  let f (b : Nat) := (List.range (bankKeys keys b).length).map fun j => (b,j)
  change a∈banks.flatMap f at h
  obtain ⟨b,hb,mem⟩ := List.mem_flatMap.mp h
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp mem
  have bound := group_length f banks hb
  change (f b).length≤(address keys).length at bound
  have short : (f b).length=(bankKeys keys b).length := by simp [f]
  rw [short] at bound
  exact ⟨hb,(List.mem_range.mp hj).trans_le (bound.trans (le_max_right _ _))⟩

theorem program_ranks (eqs : List ETRINV.Constraint) {r : Row} (hr : r∈(compile eqs).1)
    {j : Nat} (hj : j∈r.2) : j<scale eqs := by
  change r∈(expanded eqs).map (fun l => (l.1,l.2.map (CatalogPlan.rank (keysOf eqs)))) at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj
  have used : k∈keysOf eqs := List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨q,hq,hk⟩)
  exact (address_spec eqs (address_used eqs k used)).2

theorem program_door (eqs : List ETRINV.Constraint) {r : Row} {j : Nat}
    (row : (r,j)∈(compile eqs).1.zipIdx) : j<scale eqs :=
  (List.mem_zipIdx' row).1.trans_le (le_max_left _ _)

private theorem gap {a b : Nat} (ha : a∈banks) (hb : b∈banks) (h : a<b) : a+9≤b := by
  simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at ha hb
  omega

theorem separated {eqs : List ETRINV.Constraint} (hn : eqs≠[]) {a b : Addr}
    (ha : a∈(compile eqs).2) (hb : b∈(compile eqs).2) (hne : a≠b) :
    let n := scale eqs
    let L := (slotX n a.1 a.2:ℝ)
    let R := (slotX n b.1 b.2:ℝ)
    L+BankPitch.pitch n≤R ∨ R+BankPitch.pitch n≤L := by
  let n := scale eqs
  have ⟨aBank,aRank⟩ := address_spec eqs ha
  have ⟨bBank,bRank⟩ := address_spec eqs hb
  have pos : (1:ℝ)≤n := by exact_mod_cast (show 1≤n from (by have := (scale_bounds hn).1; dsimp [n]; omega))
  dsimp only
  rw [cast_slotX,cast_slotX]
  rcases lt_trichotomy a.1 b.1 with h|h|h
  · exact Or.inl (BankPitch.different_banks pos (by exact_mod_cast gap aBank bBank h)
      (by exact_mod_cast aRank.le) (by positivity))
  · have ne : a.2≠b.2 := fun eq => hne (Prod.ext h eq)
    rcases lt_or_gt_of_ne ne with k|k
    · left; rw [h]; exact BankPitch.same_bank pos (by exact_mod_cast k)
    · right; rw [h]; exact BankPitch.same_bank pos (by exact_mod_cast k)
  · exact Or.inr (BankPitch.different_banks pos (by exact_mod_cast gap bBank aBank h)
      (by exact_mod_cast bRank.le) (by positivity))

theorem routed {Φ : List ETRINV.Constraint} (l : PrivatePorts.Leaf (PhysicalLayout.Label Φ)) :
    ∃ t : ChartDrawing.Template, ChartDrawing.catalog[style l]?=some t ∧
      t.corridor=PlanGeometry.corridor l ∧ t.room=PlanGeometry.room l := by
  cases l with
  | ordinary | shifted => exact ⟨_,rfl,rfl,rfl⟩
  | lower a b _ | invLe a b =>
    have ha := UsedSlots.bank_list a
    have hb := UsedSlots.bank_list b
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with h|h|h|h|h|h|h <;> rcases hb with k|k|k|k|k|k|k <;>
      simp only [style,PlanGeometry.corridor,h,k] <;> exact ⟨_,rfl,rfl,rfl⟩
  | invRevGe a _ =>
    by_cases ha : PrivatePorts.bank a=40 <;> simp [style,PlanGeometry.corridor,ha] <;> exact ⟨_,rfl,rfl,rfl⟩

end ArtGallery.Orthogonal.BoundaryPoint.CompiledAddresses
end
