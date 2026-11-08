module

public import ArtGallery.Orthogonal.BoundaryPoint.CatalogPlan

/-! # Numeric master and port identifiers preserve the typed slot names -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SlotKeys
open PhysicalLayout FlattenNetwork PrimitiveNetwork PrivatePorts SourcePortPlan

theorem local_lt {ι} (p : Net ι) (s : locals p) : localIndex p s<localCount p := by
  induction p with
  | atom a => exact nomatch s
  | bind p ih =>
    cases s with
    | inl => simp [localIndex,localCount]
    | inr i => simpa only [localIndex,localCount,Nat.add_lt_add_iff_left] using ih i
  | both p q ih jh =>
    cases s with
    | inl i => exact (ih i).trans_le (Nat.le_add_right _ _)
    | inr j => exact Nat.add_lt_add_left (jh j) _

theorem local_injective {ι} (p : Net ι) : Function.Injective (localIndex p) := by
  induction p with
  | atom => intro i; exact nomatch i
  | bind p ih =>
    rintro (i|i) (j|j) h
    · congr
    · simp only [localIndex] at h; omega
    · simp only [localIndex] at h; omega
    · exact congrArg Sum.inr (ih (Nat.add_left_cancel h))
  | both p q ih jh =>
    rintro (i|i) (j|j) h
    · exact congrArg Sum.inl (ih h)
    · change localIndex p i=localCount p+localIndex q j at h
      have := local_lt p i; omega
    · change localCount p+localIndex q i=localIndex p j at h
      have := local_lt p j; omega
    · exact congrArg Sum.inr (jh (Nat.add_left_cancel h))

theorem order_injective (e : ETRINV.Constraint) : Function.Injective (localOrder e) := by
  intro i j h
  cases e <;> simp only [localOrder] at h
  · exact h
  · split at h <;> split at h <;> omega
  · exact h

private theorem port_injective : Function.Injective portNumber := by
  rintro (a|a|a) (b|b|b) h <;> first | rfl | contradiction

private theorem same_bank {Φ : List ETRINV.Constraint} {s t : Label Φ} (h : key s=key t) :
    bank s=bank t := by
  have eq := congrArg (fun k : List Nat => k.headD 0) h
  simpa only [key,List.headD_cons] using eq

private theorem public_ids {Φ : List ETRINV.Constraint} {a b : Master Φ}
    (h : key (.master a : Label Φ)=key (.master b)) : a=b := by
  rcases a with i|⟨i,k⟩ <;> rcases b with j|⟨j,l⟩
  · simpa [key,bank] using h
  · simp [key,bank] at h
  · simp [key,bank] at h
  · have ht : i.val=j.val ∧ localOrder Φ[i] (localIndex _ k)=localOrder Φ[j] (localIndex _ l) := by
      simpa [key,bank] using h
    obtain rfl := Fin.ext ht.1
    obtain rfl := local_injective _ (order_injective _ ht.2)
    rfl

theorem injective {Φ : List ETRINV.Constraint} : Function.Injective (@key Φ) := by
  intro s t h
  have b := same_bank h
  cases s <;> cases t
  all_goals try first | exact congrArg Slot.master (public_ids h) | rfl
  all_goals try solve | simp [bank] at b
  case privatePort.privatePort r k u v =>
    have h' : r.val=u.val ∧ portNumber k=portNumber v := by
      have htail := congrArg List.tail h
      simpa [key] using htail
    obtain rfl := Fin.ext h'.1
    obtain rfl := port_injective h'.2
    rfl
  case middle.middle r k u v =>
    have h' : r.val=u.val ∧ portNumber k=portNumber v := by simpa [key,bank] using h
    obtain rfl := Fin.ext h'.1
    obtain rfl := port_injective h'.2
    rfl
  case reciprocal.reciprocal r k u j v w =>
    have h' : r.val=j.val ∧ portNumber k=portNumber v ∧ (if u then 1 else 0 : Nat)=(if w then 1 else 0) := by
      simpa [key,bank] using h
    obtain rfl := Fin.ext h'.1
    obtain rfl := port_injective h'.2.1
    cases u <;> cases w <;> simp_all
  case master.privatePort _ _ p => cases p <;> simp [bank] at b
  case privatePort.master _ p _ => cases p <;> simp [bank] at b
  case half.privatePort _ p => cases p <;> simp [bank] at b
  case privatePort.half _ p => cases p <;> simp [bank] at b
  case middle.privatePort _ _ _ p => cases p <;> simp [bank] at b
  case privatePort.middle _ p _ _ => cases p <;> simp [bank] at b
  case reciprocal.privatePort _ _ _ _ p => cases p <;> simp [bank] at b
  case privatePort.reciprocal _ p _ _ _ => cases p <;> simp [bank] at b

end ArtGallery.Orthogonal.BoundaryPoint.SlotKeys
end
