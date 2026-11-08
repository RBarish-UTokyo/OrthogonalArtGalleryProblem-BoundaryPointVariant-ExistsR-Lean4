module

public import ArtGallery.Orthogonal.BoundaryPoint.SlotKeys

/-! # Arithmetic semantics of the numeric source expansion
A gallery has public source actualVars, one shared half, and private names
local to an occurrence of a source clause. The proof glues independently
satisfying one-clause assignments along their shared public values. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CatalogLogic
open CatalogPlan PhysicalLayout PrivatePorts PrimitiveNetwork SourcePortPlan DerivedAlgebra

def relation (tag : Nat) (v : List ℝ) : Prop :=
  let x := v.getD 0 0
  let y := v.getD 1 0
  let z := v.getD 2 0
  if tag=0 then z≤x+y else if tag=1 then ShiftedAddGe x y z else
  if tag<7 then 2+z≤x+y else if tag=11 ∨ tag=13 then InvRevGe x y else InvLe x y

def All (rows : ClauseRows) (v : Key → ℝ) := ∀ r∈rows, relation r.1 (r.2.map v)

private theorem leaf {ι ρ} (l : Leaf (Slot ι ρ)) (v : Slot ι ρ → ℝ) :
    relation (style l) ((args l).map v) ↔ l.Holds v := by
  cases l with
  | ordinary | shifted => rfl
  | lower a b z =>
    by_cases h : bank a=40 <;> by_cases h₁ : bank b=40 <;>
      by_cases h₂ : bank b=200 <;> by_cases h₃ : bank b=360 <;>
      simp [style,relation,h,h₁,h₂,h₃,args,Leaf.Holds]
  | invLe a b =>
    by_cases h : bank a=40 <;> by_cases h₁ : bank b=40 <;>
      by_cases h₂ : bank b=200 <;> by_cases h₃ : bank b=360 <;>
      simp [style,relation,h,h₁,h₂,h₃,args,Leaf.Holds]
  | invRevGe a b =>
    by_cases h : bank a=40 <;> simp [style,relation,h,args,Leaf.Holds]

theorem schema_iff (e : ETRINV.Constraint) (v : Key → ℝ) :
    All (schema e) v ↔ allHold (fun s => v (key s)) (leaves [e]) := by
  unfold All schema allHold
  simp only [List.forall_mem_map,List.map_map,Function.comp_def]
  exact forall_congr' (fun l => imp_congr_right fun _ => leaf l _)

theorem install_iff (j : Nat) (vars : List Nat) (rows : ClauseRows) (v : Key → ℝ) :
    All (install j vars rows) v ↔ All rows (fun k => v (CatalogPlan.rename j vars k)) := by
  unfold All install
  simp only [List.forall_mem_map,List.map_map,Function.comp_def]

def model : ETRINV.Constraint → ETRINV.Constraint
  | .one _ => .one 0 | .add .. => .add 0 1 2 | .inv .. => .inv 0 1

def actualVars : ETRINV.Constraint → List Nat
  | .one x => [x] | .add x y z => [x,y,z] | .inv x y => [x,y]

theorem instantiate (e : ETRINV.Constraint) (x : Nat → ℝ) :
    (model e).Holds (fun i => x ((actualVars e).getD i 0)) ↔ e.Holds x := by cases e <;> rfl

theorem expand_eq (j : Nat) (e : ETRINV.Constraint) :
    expand j e=install j (actualVars e) (schema (model e)) := by cases e <;> rfl

def publicKey (i : Nat) : Key := [360,0,i]

theorem canonical {Φ : List ETRINV.Constraint} {x : Nat → ℝ} (hx : ∀ i, InRange (x i))
    (h : ∀ e∈Φ,e.Holds x) :
    ∃ v : Label Φ → ℝ, (∀ s, InRange (v s)) ∧
      (∀ i, v (.master (.inl i))=x i) ∧ v .half=1/2 ∧ allHold v (leaves Φ) := by
  obtain ⟨v,hr,hp,rows⟩ := (compile_correct_at Φ x hx).2 h
  let y := fun i => v (.master i)
  have hy : ∀ i, InRange (y i) := fun i => hr _
  have hall := (physical_correct (logical Φ) y hy).1 ⟨v,hr,fun _ => rfl,rows⟩
  exact ⟨extend _ y,extend_range _ y hy,hp,rfl,(extend_correct _ y hy).2 hall⟩

noncomputable def store {Φ : List ETRINV.Constraint} (v : Label Φ → ℝ) (k : Key) : ℝ :=
  open Classical in if h : ∃ s : Label Φ,key s=k then v h.choose else 1

theorem store_at {Φ : List ETRINV.Constraint} (v : Label Φ → ℝ) (s : Label Φ) :
    store v (key s)=v s := by
  classical
  unfold store
  split
  next h => exact congrArg v (SlotKeys.injective h.choose_spec)
  next h => exact (h ⟨s,rfl⟩).elim

theorem store_range {Φ : List ETRINV.Constraint} {v : Label Φ → ℝ} (hv : ∀ s, InRange (v s)) (k : Key) :
    InRange (store v k) := by unfold store; split <;> first | apply hv | norm_num [InRange]

theorem local_model {e : ETRINV.Constraint} {x : Nat → ℝ} (hx : ∀ i,InRange (x i)) (h : e.Holds x) :
    ∃ v : Key → ℝ, (∀ k, InRange (v k)) ∧
      (∀ i,v (publicKey i)=x ((actualVars e).getD i 0)) ∧ v [1000]=1/2 ∧ All (schema (model e)) v := by
  let val := fun i => x ((actualVars e).getD i 0)
  have he : ∀ c∈[model e],c.Holds val := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact (instantiate e _).2 h
  obtain ⟨v,hr,hpub,hhalf,rows⟩ := canonical (fun i => hx _) he
  refine ⟨store v,store_range hr,?_,?_,(schema_iff _ _).2 ?_⟩
  · intro i
    exact (store_at v (.master (.inl i))).trans (hpub i)
  · exact (store_at v .half).trans hhalf
  · simpa only [store_at] using rows

noncomputable def assemble (x : Nat → ℝ) (u : Nat → Key → ℝ) (k : Key) : ℝ :=
  if k.headD 0=1000 then 1/2 else
  if k.headD 0=360 then
    if k.getD 1 0=0 then x (k.getD 2 0) else u (k.getD 2 0) [360,1,0,k.getD 3 0]
  else u (k.getD 1 0) (k.headD 0 :: k.drop 2)

theorem assemble_range {x : Nat → ℝ} {u : Nat → Key → ℝ} (hx : ∀ i, InRange (x i))
    (hu : ∀ j k, InRange (u j k)) (k : Key) : InRange (assemble x u k) := by
  unfold assemble
  split
  · norm_num [InRange]
  · split
    · split
      · apply hx
      · apply hu
    · apply hu

theorem assembled_key {e : ETRINV.Constraint} (vars : List Nat) {x : Nat → ℝ} {u : Nat → Key → ℝ} {j : Nat}
    (hpub : ∀ i,u j (publicKey i)=x (vars.getD i 0)) (half : u j [1000]=1/2)
    (s : Label [e]) : assemble x u (CatalogPlan.rename j vars (key s)) = u j (key s) := by
  cases s with
  | master m =>
    cases m with
    | inl i => exact (hpub i).symm
    | inr pair =>
      obtain ⟨i,k⟩ := pair
      have eq : i.val=0 := by exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (show i.val < 1 from i.isLt))
      simp [CatalogPlan.rename,assemble,key,bank,eq]
  | half => exact half.symm
  | privatePort r k => cases k <;> rfl
  | middle => rfl
  | reciprocal => rfl

def expanded (eqs : List ETRINV.Constraint) : ClauseRows :=
  eqs.zipIdx.flatMap fun (e,j) => expand j e

theorem expanded_at (eqs : List ETRINV.Constraint) (x : Nat → ℝ) (hx : ∀ i,InRange (x i)) :
    (∃ v : Key → ℝ, (∀ k, InRange (v k)) ∧ (∀ i,v (publicKey i)=x i) ∧ All (expanded eqs) v) ↔
      ∀ e∈eqs,e.Holds x := by
  constructor
  · rintro ⟨v,hr,hpub,rows⟩ e he
    obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp he
    have occurrence : (eqs[j],j)∈eqs.zipIdx := by
      exact List.mem_iff_getElem.mpr ⟨j,by simpa using hj,by simp⟩
    have localRows : All (expand j eqs[j]) v := fun r h => rows r (List.mem_flatMap.mpr ⟨_,occurrence,h⟩)
    rw [expand_eq,install_iff,schema_iff] at localRows
    let lift := fun i => x ((actualVars eqs[j]).getD i 0)
    have heq := (compile_correct_at [model eqs[j]] lift (fun i => hx _)).1
      ⟨_,(fun s => hr _),(fun i => hpub _),localRows⟩
    rw [← ej]
    exact (instantiate _ _).1 (heq _ (by simp))
  · intro he
    have hh (i : Fin eqs.length) := local_model hx (he _ (List.getElem_mem i.isLt))
    choose v hr hp half ok using hh
    let u (j : Nat) := if h : j<eqs.length then v ⟨j,h⟩ else fun _ : Key => (1:ℝ)
    have reach (j : Nat) (h : j<eqs.length) : u j=v ⟨j,h⟩ := by simp [u,h]
    refine ⟨assemble x u, assemble_range hx (fun j k => ?_), fun i => rfl, ?_⟩
    · by_cases h : j<eqs.length
      · rw [reach j h]; apply hr
      · norm_num [u,h,InRange]
    · rintro row hrow
      obtain ⟨⟨e,j⟩,hm,hmem⟩ := List.mem_flatMap.mp hrow
      obtain ⟨hj,ee⟩ := List.mem_zipIdx' hm
      change row ∈ expand j e at hmem
      have member : row∈expand j eqs[j] := by simpa only [ee] using hmem
      let i : Fin eqs.length := ⟨j,hj⟩
      have eq (s : Label [model eqs[j]]) :=
        assembled_key (actualVars eqs[j]) (x:=x) (u:=u) (j:=j)
          (fun k => (congrFun (reach j hj) _).trans (hp i k))
          ((congrFun (reach j hj) _).trans (half i)) s
      have inner := (schema_iff _ _).1 (ok i)
      have same : (fun s : Label [model eqs[j]] => assemble x u (CatalogPlan.rename j (actualVars eqs[j]) (key s))) =
          (fun s => v i (key s)) := funext fun s => (eq s).trans (congrFun (reach j hj) _)
      have usable : All (expand j eqs[j]) (assemble x u) := by
        rw [expand_eq,install_iff,schema_iff,same]
        exact inner
      exact usable row member

end ArtGallery.Orthogonal.BoundaryPoint.CatalogLogic
end
