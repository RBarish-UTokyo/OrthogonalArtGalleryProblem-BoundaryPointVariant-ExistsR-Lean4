module

public import ArtGallery.Orthogonal.BoundaryPoint.FlattenNetwork

/-! # Source-to-private-port compiler for bounded ETR-INV

Every physical leaf has strictly increasing bank numbers, and there are at
most 209 leaves per source clause. The logical witnesses use fresh master
names local to the clause. Each physical port has its own private six-leaf
wire, with one shared lower-output slot for the entire plan.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SourcePortPlan

open DerivedAlgebra PrimitiveNetwork FlattenNetwork PrivatePorts

/-- Match the executable order in each clause. It puts the three complement
tests before the concluding upper and lower arithmetic inequalities. -/
def order {α : Type} : ETRINV.Constraint → List α → List α
  | .one _, [x, l, r, u, z] | .inv .., [x, l, r, u, z] => [r,u,l,x,z]
  | .add .., [x,l,r,u,l',r',u',l'',r'',u'',z] => [r,u,l,r',u',l',r'',u'',l'',x,z]
  | _, l => l

theorem mem_order {α} (e : ETRINV.Constraint) (l : List α) (a : α) :
    a ∈ order e l ↔ a ∈ l := by
  unfold order
  split <;> simp [or_comm, or_left_comm]

theorem length_order {α} (e : ETRINV.Constraint) (l : List α) :
    (order e l).length = l.length := by unfold order; split <;> rfl

abbrev Master (Φ : List ETRINV.Constraint) :=
  Nat ⊕ (Σ i : Fin Φ.length, locals (lowerConstraint Φ[i]))

def clause (Φ : List ETRINV.Constraint) (i : Fin Φ.length) : List (Atom (Master Φ)) :=
  order Φ[i] (emit (lowerConstraint Φ[i]) Sum.inl (fun j => Sum.inr ⟨i,j⟩))

def logical (Φ : List ETRINV.Constraint) : List (Atom (Master Φ)) :=
  (List.ofFn (clause Φ)).flatten

def leaves (Φ : List ETRINV.Constraint) := physical (logical Φ)

private theorem logical_rows (Φ : List ETRINV.Constraint) (v : Master Φ → ℝ) :
    (∀ a ∈ logical Φ, a.Holds v) ↔
    ∀ i : Fin Φ.length, assigned (lowerConstraint Φ[i]) (v ∘ Sum.inl)
      (fun j => v (.inr ⟨i,j⟩)) := by
  rw [logical, List.forall_mem_flatten]
  constructor
  · intro h i
    apply (emit_holds (lowerConstraint Φ[i]) Sum.inl (fun j => Sum.inr ⟨i,j⟩) v).1
    intro a ha
    exact h _ (List.mem_ofFn.2 ⟨i,rfl⟩) a ((mem_order _ _ a).2 ha)
  · intro h row hr a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hr
    let fresh : locals (lowerConstraint Φ[i]) → Master Φ := fun t => .inr ⟨i,t⟩
    have hem : a ∈ emit (lowerConstraint Φ[i]) Sum.inl fresh :=
      (mem_order Φ[i] _ a).1 ha
    exact (emit_holds (lowerConstraint Φ[i]) Sum.inl fresh v).2 (h i) a hem

theorem logical_correct (Φ : List ETRINV.Constraint) :
    (∃ v : Master Φ → ℝ, (∀ m, InRange (v m)) ∧ ∀ a ∈ logical Φ, a.Holds v) ↔
    ETRINV.Satisfiable Φ := by
  constructor
  · rintro ⟨v,hv,h⟩
    refine ⟨v ∘ Sum.inl, fun i => hv (.inl i), ?_⟩
    intro e he
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.1 he
    let i : Fin Φ.length := ⟨j,hj⟩
    apply (lowerConstraint_correct _ _ (fun j => hv (.inl j))).1
    apply (assigned_iff _ _).2
    exact ⟨(fun t => v (.inr ⟨i,t⟩)), fun t => hv (.inr ⟨i,t⟩), (logical_rows Φ v).1 h i⟩
  · rintro ⟨x,hx,h⟩
    have each (i : Fin Φ.length) := (assigned_iff (lowerConstraint Φ[i]) x).1
      ((lowerConstraint_correct Φ[i] x hx).2 (h _ (List.getElem_mem i.2)))
    choose y hr ha using each
    let v : Master Φ → ℝ := Sum.elim x (fun ij => y ij.1 ij.2)
    refine ⟨v, fun | .inl i => hx i | .inr ⟨i,j⟩ => hr i j, (logical_rows Φ v).2 ?_⟩
    exact ha

/-- Existential arithmetic feasibility of the complete physically ordered
leaf list is equivalent to satisfiability of the source equations. -/
theorem compile_correct (Φ : List ETRINV.Constraint) :
    (∃ v, (∀ s, InRange (v s)) ∧ allHold v (leaves Φ)) ↔ ETRINV.Satisfiable Φ := by
  rw [← logical_correct Φ]
  constructor
  · rintro ⟨v,hv,h⟩
    let x : Master Φ → ℝ := fun i => v (.master i)
    have hx : ∀ i, InRange (x i) := fun i => hv (.master i)
    exact ⟨x, hx, (physical_correct (logical Φ) x hx).1 ⟨v,hv,fun _ => rfl,h⟩⟩
  · rintro ⟨x,hx,h⟩
    exact ⟨extend (logical Φ) x, extend_range _ _ hx, (extend_correct _ _ hx).2 h⟩

/-- Projection onto the *prescribed* source values, not just feasibility
with some source valuation. This is the interface needed for pin soundness. -/
theorem compile_correct_at (Φ : List ETRINV.Constraint) (x : Nat → ℝ) (hx : ∀ i, InRange (x i)) :
    (∃ v, (∀ s, InRange (v s)) ∧ (∀ i, v (.master (.inl i)) = x i) ∧ allHold v (leaves Φ)) ↔
      ∀ e ∈ Φ, e.Holds x := by
  constructor
  · rintro ⟨v,hv,agree,all⟩ e he
    let y : Master Φ → ℝ := fun m => v (.master m)
    have hy : ∀ m, InRange (y m) := fun m => hv (.master m)
    have hh := (physical_correct (logical Φ) y hy).1 ⟨v,hv,fun _ => rfl,all⟩
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
    let i : Fin Φ.length := ⟨j,hj⟩
    have hsrc : y ∘ Sum.inl = x := funext agree
    change (Φ[i]).Holds x
    apply (lowerConstraint_correct Φ[i] x hx).1
    apply (assigned_iff _ _).2
    refine ⟨(fun t => y (.inr ⟨i,t⟩)),fun t => hy _,?_⟩
    simpa only [hsrc] using ((logical_rows Φ y).1 hh i)
  · intro h
    have each (i : Fin Φ.length) := (assigned_iff (lowerConstraint Φ[i]) x).1
      ((lowerConstraint_correct Φ[i] x hx).2 (h _ (List.getElem_mem i.2)))
    choose z hz hall using each
    let y : Master Φ → ℝ := Sum.elim x (fun ij => z ij.1 ij.2)
    have hy : ∀ m, InRange (y m) := fun | .inl i => hx i | .inr ⟨i,j⟩ => hz i j
    exact ⟨extend (logical Φ) y,extend_range _ _ hy,fun _ => rfl,
      (extend_correct _ _ hy).2 ((logical_rows Φ y).2 hall)⟩

private theorem flatten_length_le {α : Type} (l : List (List α)) (n : Nat)
    (h : ∀ row ∈ l, row.length ≤ n) : l.flatten.length ≤ n * l.length := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    have hr := h r (by simp)
    have hs := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem logical_length (Φ : List ETRINV.Constraint) : (logical Φ).length ≤ 11 * Φ.length := by
  apply le_trans (flatten_length_le _ 11 ?_)
  · simp
  · intro row hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hr
    rw [clause, length_order, emit_length]
    exact clause_size _

theorem compile_length (Φ : List ETRINV.Constraint) : (leaves Φ).length ≤ 209 * Φ.length :=
  calc (leaves Φ).length ≤ 19 * (logical Φ).length := physical_length _
       _ ≤ 19 * (11 * Φ.length) := Nat.mul_le_mul_left _ (logical_length Φ)
       _ = 209 * Φ.length := by rw [← Nat.mul_assoc]

theorem compile_ordered (Φ : List ETRINV.Constraint) : ∀ l ∈ leaves Φ, l.Ordered :=
  physical_ordered _

end ArtGallery.Orthogonal.BoundaryPoint.SourcePortPlan
end
