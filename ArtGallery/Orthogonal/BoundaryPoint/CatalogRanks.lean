module

public import ArtGallery.Orthogonal.BoundaryPoint.CatalogLogic
public import ArtGallery.Orthogonal.BoundaryPoint.PlanGeometry

/-! # Arithmetic correctness after assignment of physical bank ranks
The number of lexicographically smaller used keys is a strictly increasing
rank in each bank. In particular, sharing a numeric port is equivalent to
sharing the corresponding used slot key. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CatalogRanks
open CatalogPlan CatalogLogic PhysicalLayout PrivatePorts DerivedAlgebra PlanGeometry

def profileBanks : Nat → List Nat
  | 0 | 1 => [40,200,520]
  | 2 => [40,200,1000] | 3 => [10,40,1000] | 4 => [10,200,1000]
  | 5 => [10,360,1000] | 6 => [10,520,1000]
  | 7 => [1,40] | 8 => [1,200] | 9 => [1,360] | 10 => [1,520]
  | 11 => [1,10] | 12 | 13 => [40,200] | _ => []

theorem style_banks {ι ρ} (l : Leaf (Slot ι ρ)) (hl : Supported l) :
    profileBanks (style l)=(args l).map bank := by
  cases l with
  | ordinary a b z => rcases hl with ⟨ha,hb,hz⟩; simp [style,profileBanks,args,ha,hb,hz]
  | shifted a b z => rcases hl with ⟨ha,hb,hz⟩; simp [style,profileBanks,args,ha,hb,hz]
  | lower a b z =>
    rcases hl with ⟨hz,⟨ha,hb⟩|⟨ha,hb⟩⟩
    · simp [style,profileBanks,args,ha,hb,hz]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with hb|hb|hb|hb <;> simp [style,profileBanks,args,ha,hb,hz]
  | invLe a b =>
    rcases hl with ⟨ha,hb⟩|⟨ha,hb⟩
    · simp [style,profileBanks,args,ha,hb]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with hb|hb|hb|hb <;> simp [style,profileBanks,args,ha,hb]
  | invRevGe a b =>
    rcases hl with ⟨ha,hb⟩|⟨ha,hb⟩ <;> simp [style,profileBanks,args,ha,hb]

theorem rename_bank (j : Nat) (args : List Nat) (k : Key) :
    (CatalogPlan.rename j args k).headD 0=k.headD 0 := by
  unfold CatalogPlan.rename
  split
  · rfl
  · split
    next h => split <;> exact h.symm
    · rfl

theorem expanded_banks (eqs : List ETRINV.Constraint) (r : Nat × List Key) (hr : r∈expanded eqs) :
    profileBanks r.1=r.2.map (fun k => k.headD 0) := by
  obtain ⟨⟨e,j⟩,_,hh⟩ := List.mem_flatMap.mp hr
  change r∈expand j e at hh
  rw [expand_eq] at hh
  obtain ⟨row,hm,rfl⟩ := List.mem_map.mp hh
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hm
  simp only [List.map_map,Function.comp_def,rename_bank]
  exact style_banks l (supported hl)

theorem less_iff (a b : Key) : less a b=true ↔ a<b := by
  induction a generalizing b with
  | nil => cases b <;> simp [less]
  | cons x xs ih =>
    cases b with
    | nil => simp [less]
    | cons y ys =>
      by_cases h : x=y
      · subst y
        simpa [less,List.find?_cons] using ih ys
      · simp [less,List.find?_cons,h,List.cons_lt_cons_iff]

private theorem less_self (k : Key) : less k k=false := by
  cases h : less k k with
  | false => rfl
  | true => exact ((lt_irrefl k) ((less_iff k k).1 h)).elim

private theorem strict_filter {α : Type} {P Q : α → Bool} (xs : List α)
    (imp : ∀ k, P k=true → Q k=true) {w : α} (hw : w∈xs) (no : P w=false) (yes : Q w=true) :
    (xs.filter P).length < (xs.filter Q).length := by
  have eq : (xs.filter Q).filter P=xs.filter P := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro k _
    cases h : P k with
    | false => simp
    | true => simp [imp k h]
  have sub : List.Sublist (xs.filter P) (xs.filter Q) := by
    rw [← eq]; apply List.filter_sublist
  apply lt_of_le_of_ne sub.length_le
  intro equal
  have m := List.mem_filter.mpr ⟨hw,yes⟩
  rw [← sub.eq_of_length equal] at m
  have bad := (List.mem_filter.mp m).2
  simp [no] at bad

abbrev Addr := Nat × Nat
def loc (keys : List Key) (k : Key) : Addr := (k.headD 0,CatalogPlan.rank keys k)
def keysOf (eqs : List ETRINV.Constraint) := ((expanded eqs).flatMap Prod.snd).eraseDups

theorem strictly_ranked {keys : List Key} {a b : Key} (ha : a∈keys) (hb : a.headD 0=b.headD 0)
    (hlt : a<b) : CatalogPlan.rank keys a<CatalogPlan.rank keys b := by
  let xs := bankKeys keys (a.headD 0)
  have hm : a∈xs := by simp [xs,bankKeys,ha]
  have lo : less a a=false := less_self a
  have hi := (less_iff a b).2 hlt
  have tight := strict_filter (P:=fun k => less k a) (Q:=fun k => less k b) xs
    (fun k h => (less_iff k b).2 (((less_iff k a).1 h).trans hlt)) hm lo hi
  simpa only [CatalogPlan.rank,← hb] using tight

theorem distinct {keys : List Key} {a b : Key} (ha : a∈keys) (hb : b∈keys)
    (he : loc keys a=loc keys b) : a=b := by
  have bank := congrArg Prod.fst he
  have ranks := congrArg Prod.snd he
  rcases lt_trichotomy a b with h|h|h
  · exact ((strictly_ranked ha bank h).ne ranks).elim
  · exact h
  · exact ((strictly_ranked hb bank.symm h).ne ranks.symm).elim

theorem rank_address {keys : List Key} {k : Key} (hk : k∈keys) (hb : k.headD 0∈banks) :
    loc keys k ∈ address keys := by
  let xs := bankKeys keys (k.headD 0)
  have mem : k∈xs := by simp [xs,bankKeys,hk]
  have lo : less k k=false := less_self k
  have tight := strict_filter (P:=fun a => less a k) (Q:=fun _ => true) xs
    (fun _ _ => rfl) mem lo rfl
  have bound : CatalogPlan.rank keys k<xs.length := by simpa [xs,CatalogPlan.rank] using tight
  exact List.mem_flatMap.mpr ⟨_,hb,List.mem_map.mpr ⟨_,List.mem_range.mpr bound,rfl⟩⟩

private theorem supported_bank (tag b : Nat) (h : b∈profileBanks tag) : b∈banks := by
  unfold profileBanks at h
  split at h <;> simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at * <;> omega

theorem address_used (eqs : List ETRINV.Constraint) (k : Key) (hk : k∈keysOf eqs) :
    loc (keysOf eqs) k∈(compile eqs).2 := by
  apply rank_address hk
  obtain ⟨r,hr,hmem⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hk)
  apply supported_bank r.1
  rw [expanded_banks eqs r hr]
  exact List.mem_map.mpr ⟨k,hmem,rfl⟩

def Physical (p : Input) (v : Addr → ℝ) : Prop :=
  ∀ r∈p.1, relation r.1 (((profileBanks r.1).zip r.2).map v)

private theorem zip_maps {α β γ : Type} (l : List α) (f : α → β) (g : α → γ) :
    (l.map f).zip (l.map g)=l.map (fun a => (f a,g a)) := by induction l <;> simp [*]

theorem physical_iff (eqs : List ETRINV.Constraint) (v : Addr → ℝ) :
    Physical (compile eqs) v ↔ All (expanded eqs) (fun k => v (loc (keysOf eqs) k)) := by
  change (∀ r∈(expanded eqs).map (fun q => (q.1,q.2.map (CatalogPlan.rank (keysOf eqs)))),
    relation r.1 (((profileBanks r.1).zip r.2).map v)) ↔ _
  simp only [List.forall_mem_map,All]
  apply forall_congr'; intro r
  apply imp_congr_right; intro hr
  rw [expanded_banks eqs r hr,zip_maps,List.map_map]
  rfl

noncomputable def liftKeys (keys : List Key) (v : Key → ℝ) (a : Addr) : ℝ :=
  open Classical in if h : ∃ k, k∈keys ∧ loc keys k=a then v h.choose else 1

theorem lift_range {keys : List Key} {v : Key → ℝ} (hv : ∀ k, InRange (v k)) (a : Addr) :
    InRange (liftKeys keys v a) := by unfold liftKeys; split <;> first | apply hv | norm_num [InRange]

theorem lift_at {keys : List Key} {v : Key → ℝ} {k : Key} (hk : k∈keys) :
    liftKeys keys v (loc keys k)=v k := by
  unfold liftKeys
  split
  next h => exact congrArg v (distinct h.choose_spec.1 hk h.choose_spec.2)
  next h => exact (h ⟨k,hk,rfl⟩).elim

theorem compile_correct (eqs : List ETRINV.Constraint) :
    (∃ v : Addr → ℝ, (∀ a, InRange (v a)) ∧ Physical (compile eqs) v) ↔ ETRINV.Satisfiable eqs := by
  constructor
  · rintro ⟨v,hv,rows⟩
    let atKey := fun k => v (loc (keysOf eqs) k)
    let x := fun i => atKey (publicKey i)
    have hx (i) : InRange (x i) := hv _
    exact ⟨x,hx,(expanded_at eqs x hx).1 ⟨atKey,(fun _ => hv _),fun _ => rfl,(physical_iff eqs v).1 rows⟩⟩
  · rintro ⟨x,hx,h⟩
    obtain ⟨v,hv,_,rows⟩ := (expanded_at eqs x hx).2 h
    refine ⟨liftKeys (keysOf eqs) v,lift_range hv,(physical_iff eqs _).2 ?_⟩
    intro r hr
    have eq : r.2.map (fun k => liftKeys (keysOf eqs) v (loc (keysOf eqs) k))=r.2.map v := by
      apply List.map_congr_left
      intro k hk
      apply lift_at
      exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨r,hr,hk⟩)
    rw [eq]; exact rows _ hr

end ArtGallery.Orthogonal.BoundaryPoint.CatalogRanks
end
