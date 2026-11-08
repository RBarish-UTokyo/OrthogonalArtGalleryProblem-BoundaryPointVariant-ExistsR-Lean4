module

public import ArtGallery.Spec
public import ArtGallery.Orthogonal.BoundaryPoint.DerivedAlgebra

/-! # Bounded ETR-INV preprocessing into addition and inversion leaves

A binder allocates one fresh bounded auxiliary value. Source variables remain
shared between clauses. The primitive count is at most eleven per source
constraint, before private-slot copies are inserted.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PrimitiveNetwork
open DerivedAlgebra

inductive Atom (ι : Type) where
  | ordinary (a b z : ι)
  | shifted (a b z : ι)
  | lower (a b : ι)
  | invLe (a b : ι)
  | invRevGe (a b : ι)

inductive Net : Type → Type 1 where
  | atom {ι} (a : Atom ι) : Net ι
  | both {ι} (p q : Net ι) : Net ι
  | bind {ι} (body : Net (Option ι)) : Net ι

def Atom.Holds {ι} (a : Atom ι) (v : ι → ℝ) : Prop :=
  match a with
  | .ordinary x y z => v z ≤ v x + v y
  | .shifted x y z => ShiftedAddGe (v x) (v y) (v z)
  | .lower x y => LowerComplement (v x) (v y)
  | .invLe x y => InvLe (v x) (v y)
  | .invRevGe x y => InvRevGe (v x) (v y)

def push {ι} (x : ℝ) (v : ι → ℝ) : Option ι → ℝ
  | none => x
  | some i => v i

def Net.Holds {ι} (p : Net ι) (v : ι → ℝ) : Prop :=
  match p with
  | .atom a => a.Holds v
  | .both s t => s.Holds v ∧ t.Holds v
  | .bind s => ∃ x : ℝ, InRange x ∧ s.Holds (push x v)

def Net.size {ι} : Net ι → Nat
  | .atom _ => 1
  | .both s t => s.size + t.size
  | .bind s => s.size

def comp {ι} (a b : ι) : Net ι := .both (.atom (.lower a b))
  (.bind (.both (.atom (.invRevGe none (some a))) (.atom (.invLe none (some b)))))

theorem comp_correct {ι} (a b : ι) (v : ι → ℝ) :
    (comp a b).Holds v ↔ Complement (v a) (v b) := Iff.rfl

def invGe {ι} (a b : ι) : Net ι :=
  .bind (.both (comp (some b) none) (.atom (.invRevGe (some a) none)))

theorem invGe_correct {ι} (a b : ι) (v : ι → ℝ) (hy : InRange (v b)) :
    (invGe a b).Holds v ↔ 1 ≤ v a * v b := derived_invGe_iff hy

def addLe {ι} (a b z : ι) : Net ι :=
  let lift := fun i : ι => some (some (some i))
  let x' := some (some none)
  let y' := some none
  let z' := none
  .bind (.bind (.bind (.both (comp (lift a) x') (.both (comp (lift b) y')
    (.both (comp (lift z) z') (.atom (.shifted x' y' z')))))))

theorem addLe_correct {ι} (a b z : ι) (v : ι → ℝ)
    (ha : InRange (v a)) (hb : InRange (v b)) (hz : InRange (v z)) :
    (addLe a b z).Holds v ↔ v a + v b ≤ v z := by
  rw [← derived_addLe_iff ha hb hz]
  constructor
  · rintro ⟨x', hx', y', hy', z', hz', h₁, h₂, h₃, hs⟩
    exact ⟨x', y', z', hx', hy', hz', h₁, h₂, h₃, hs⟩
  · rintro ⟨x', y', z', hx', hy', hz', h₁, h₂, h₃, hs⟩
    exact ⟨x', hx', y', hy', z', hz', h₁, h₂, h₃, hs⟩

def lowerConstraint : ETRINV.Constraint → Net Nat
  | .one a => .both (.atom (.invLe a a)) (invGe a a)
  | .inv a b => .both (.atom (.invLe a b)) (invGe a b)
  | .add a b z => .both (.atom (.ordinary a b z)) (addLe a b z)

theorem lowerConstraint_correct (e : ETRINV.Constraint) (v : Nat → ℝ)
    (h : ∀ i, InRange (v i)) : (lowerConstraint e).Holds v ↔ e.Holds v := by
  cases e with
  | one a =>
    change (v a * v a ≤ 1 ∧ (invGe a a).Holds v) ↔ v a = 1
    rw [invGe_correct a a v (h a)]
    constructor
    · rintro ⟨hu, hl⟩
      have heq := le_antisymm hu hl
      have prod : (v a - 1) * (v a + 1) = 0 := by nlinarith
      have hp := positive_of_inRange (h a)
      rcases mul_eq_zero.mp prod with h₁ | h₁ <;> linarith
    · intro ha
      simp [ha]
  | inv a b =>
    change (v a * v b ≤ 1 ∧ (invGe a b).Holds v) ↔ v a * v b = 1
    rw [invGe_correct a b v (h b)]
    exact ⟨fun h' => le_antisymm h'.1 h'.2, fun he => ⟨he.le, he.ge⟩⟩
  | add a b z =>
    change (v z ≤ v a + v b ∧ (addLe a b z).Holds v) ↔ v a + v b = v z
    rw [addLe_correct a b z v (h a) (h b) (h z)]
    exact ⟨fun h' => le_antisymm h'.2 h'.1, fun he => ⟨he.ge, he.le⟩⟩

def Feasible (nets : List (Net Nat)) : Prop :=
  ∃ v : Nat → ℝ, (∀ i, InRange (v i)) ∧ ∀ p ∈ nets, p.Holds v

theorem compile_correct (Φ : List ETRINV.Constraint) :
    Feasible (Φ.map lowerConstraint) ↔ ETRINV.Satisfiable Φ := by
  constructor
  · rintro ⟨v, hv, hΦ⟩
    refine ⟨v, hv, fun e he => (lowerConstraint_correct e v hv).1 ?_⟩
    exact hΦ _ (List.mem_map.mpr ⟨e, he, rfl⟩)
  · rintro ⟨v, hv, hΦ⟩
    refine ⟨v, hv, ?_⟩
    rintro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact (lowerConstraint_correct e v hv).2 (hΦ e he)

theorem clause_size (e : ETRINV.Constraint) : (lowerConstraint e).size ≤ 11 := by
  cases e <;> simp [lowerConstraint, Net.size, invGe, comp, addLe]

theorem compile_size (Φ : List ETRINV.Constraint) :
    ((Φ.map lowerConstraint).map Net.size).sum ≤ 11 * Φ.length := by
  induction Φ with
  | nil => simp
  | cons e es ih =>
    have he := clause_size e
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- The shared lower-output slot is bounded. Any physical complement wire that
succeeds forces its minimum and the exact complement equation simultaneously. -/
theorem shared_lower_output {x y c : ℝ} (hy : InRange y) (hc : InRange c) :
    (2 + c ≤ x + y ∧ UpperComplement x y) ↔ c = 1/2 ∧ y = complement x := by
  rw [upperComplement_iff hy]
  dsimp [InRange, complement] at *
  constructor
  · intro h'
    constructor <;> linarith [hc.1, h'.1, h'.2]
  · rintro ⟨rfl, rfl⟩
    constructor <;> linarith

end ArtGallery.Orthogonal.BoundaryPoint.PrimitiveNetwork
end
