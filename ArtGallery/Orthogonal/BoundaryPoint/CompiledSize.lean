module

public import ArtGallery.Orthogonal.BoundaryPoint.CatalogRanks
public import ArtGallery.Orthogonal.BoundaryPoint.CandidateWord

/-! # Quantitative bounds for the actual numeric word map
The fixed clause schemas emit exactly 65 or 155 wings. Only used slot keys
are present in the hub. The size supplied to the chart programs is therefore
in the certified scale range for every nonempty source. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CompiledSize
open CatalogPlan CatalogLogic CatalogRanks ChartDrawing

def wings : ETRINV.Constraint → Nat | .add .. => 155 | _ => 65

theorem schema_length (e : ETRINV.Constraint) (i : Nat) : (expand i e).length=wings e := by
  cases e <;> change (List.map _ _).length=_
  all_goals rw [List.length_map]; simp only [wings]; decide +kernel

private theorem sum_between {α : Type} (l : List α) (f : α → Nat) {low high : Nat}
    (bounds : ∀ a∈l,low≤f a ∧ f a≤high) :
    low*l.length≤(l.map f).sum ∧ (l.map f).sum≤high*l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := bounds _ List.mem_cons_self
    have k := ih (fun b hb => bounds _ (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
    omega

theorem wing_count (eqs : List ETRINV.Constraint) :
    (compile eqs).1.length=(eqs.map wings).sum := by
  change ((expanded eqs).map _).length=_
  rw [List.length_map,expanded,List.length_flatMap]
  rw [show (eqs.zipIdx.map (fun p => (expand p.2 p.1).length))=eqs.map wings from ?_]
  simp only [schema_length]
  change eqs.zipIdx.map (wings ∘ Prod.fst)=eqs.map wings
  rw [← List.map_map,List.zipIdx_map_fst]

theorem row_bounds (eqs : List ETRINV.Constraint) :
    65*eqs.length≤(compile eqs).1.length ∧ (compile eqs).1.length≤155*eqs.length := by
  rw [wing_count]
  apply sum_between; intro e _; cases e <;> norm_num [wings]

def total (bs : List Nat) (ks : List Key) := (bs.map fun b => (bankKeys ks b).length).sum

private theorem total_cons (bs : List Nat) (ks : List Key) (k : Key) :
    total bs (k::ks)=total bs ks+bs.count (k.headD 0) := by
  induction bs with
  | nil => simp [total]
  | cons b bs ih =>
    change (bankKeys (k::ks) b).length+total bs (k::ks) =
      (bankKeys ks b).length+total bs ks+(b::bs).count (k.headD 0)
    rw [ih,List.count_cons]
    unfold bankKeys
    rw [List.filter_cons]
    by_cases e : k.headD 0=b
    · simp only [e,beq_self_eq_true,ite_true,List.length_cons]; omega
    · have e₁ : (k.headD 0==b)=false := by simpa using e
      have e₂ : (b==k.headD 0)=false := by simpa using Ne.symm e
      simp only [e₁,e₂,Bool.false_eq_true,ite_false,Nat.add_zero]; omega

private theorem total_bound (keys : List Key) : total banks keys≤keys.length := by
  induction keys with
  | nil => decide
  | cons k ks ih =>
    rw [total_cons]
    have small : banks.count (k.headD 0)≤1 :=
      (List.nodup_iff_count_le_one.mp (show banks.Nodup by decide)) _
    simp only [List.length_cons]; omega

theorem address_count (keys : List Key) : (address keys).length≤keys.length := by
  have exactLength : (address keys).length=total banks keys := by simp [address,total,List.length_flatMap]
  exact exactLength ▸ total_bound keys

private theorem erase_length (l acc : List Key) :
    (List.eraseDupsBy.loop (· == ·) l acc).length ≤ l.length+acc.length := by
  induction l generalizing acc with
  | nil => simp [List.eraseDupsBy.loop]
  | cons x xs ih =>
    rw [List.eraseDupsBy.loop]
    split
    · have h := ih acc; simp only [List.length_cons]; omega
    · have h := ih (x::acc); simp only [List.length_cons] at *; omega

theorem max_ports (n : Nat) : (profileBanks n).length≤3 := by unfold profileBanks; split <;> decide

theorem slot_count (eqs : List ETRINV.Constraint) :
    (compile eqs).2.length≤3*(compile eqs).1.length := by
  have keys := address_count (keysOf eqs)
  have first : (keysOf eqs).length≤((expanded eqs).flatMap Prod.snd).length := by
    simpa only [keysOf,List.eraseDups,List.eraseDupsBy,List.length_nil,Nat.add_zero] using
      erase_length ((expanded eqs).flatMap Prod.snd) []
  have count := (sum_between (expanded eqs) (fun r => r.2.length) (low:=0) (high:=3)
    (fun r hr => ⟨Nat.zero_le _,by simpa only [expanded_banks eqs r hr,List.length_map] using max_ports r.1⟩)).2
  rw [← List.length_flatMap (f:=Prod.snd)] at count
  change (address (keysOf eqs)).length≤3*((expanded eqs).map _).length
  rw [List.length_map]
  exact keys.trans (first.trans count)

def scale (eqs : List ETRINV.Constraint) := max (compile eqs).1.length (compile eqs).2.length

theorem scale_bounds {eqs : List ETRINV.Constraint} (h : eqs≠[]) : 65≤scale eqs ∧ scale eqs≤465*eqs.length := by
  have m := List.length_pos_iff.mpr h
  have r := row_bounds eqs
  have s := slot_count eqs
  unfold scale
  omega

theorem catalog_cost : catalog.all (fun t => decide (t.corridor.roles.length+t.room.roles.length+1≤20))=true := by
  decide +kernel

private theorem choose_cost {ts : List Template} (n j : Nat) (ranks : List Nat) (i : Nat)
    (h : ts.all (fun t => decide (t.corridor.roles.length+t.room.roles.length+1≤20))=true) :
    (choose ts (fun t => drawOne t n j ranks) i (none,0)).2≤20 := by
  induction ts generalizing i with
  | nil => exact Nat.zero_le _
  | cons t ts ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    obtain ⟨head,tail⟩ := h
    simp only [choose]; split
    · exact of_decide_eq_true head
    · exact ih _ tail

theorem cost (eqs : List ETRINV.Constraint) {v g}
    (emitted : CandidateWord.vertices eqs=some (v,g)) : g≤3565*eqs.length+1 := by
  let p := compile eqs
  let n := scale eqs
  have rc := (row_bounds eqs).2
  have sc := slot_count eqs
  have inside (r : Drawn) (hr : r∈batch n p.1) : 0≤r.2 ∧ r.2≤20 := by
    obtain ⟨⟨row,j⟩,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨Nat.zero_le _,choose_cost n j row.2 row.1 catalog_cost⟩
  have sum := (sum_between (batch n p.1) Prod.snd inside).2
  have len : (batch n p.1).length=p.1.length := by simp [batch]
  rw [len] at sum
  change ChartDrawing.vertices p=some (v,g) at emitted
  unfold ChartDrawing.vertices at emitted
  split at emitted
  · obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj emitted); omega
  · dsimp only at emitted
    split at emitted
    · obtain ⟨w,_,eq⟩ := Option.map_eq_some_iff.mp emitted
      have h : p.2.length+((batch n p.1).map Prod.snd).sum=g := (Prod.mk.inj eq).2
      change p.1.length≤155*eqs.length at rc
      change p.2.length≤3*p.1.length at sc
      omega
    · contradiction

end ArtGallery.Orthogonal.BoundaryPoint.CompiledSize
end
