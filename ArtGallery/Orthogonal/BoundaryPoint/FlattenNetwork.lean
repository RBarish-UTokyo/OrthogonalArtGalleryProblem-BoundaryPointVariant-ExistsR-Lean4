module

public import ArtGallery.Orthogonal.BoundaryPoint.PrivatePortPlan

/-! # Flatten existential primitive networks to lists with private names

Each binder has its own name in the syntax tree. A conjunction uses the
disjoint sum of the names of its two branches. Emission accepts arbitrary
embeddings of source names and allocated binder names into a common slot type.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.FlattenNetwork

open PrimitiveNetwork DerivedAlgebra

def locals {ι} : Net ι → Type
  | .atom _ => Empty
  | .both p q => locals p ⊕ locals q
  | .bind p => Unit ⊕ locals p

def rename {ι σ} (f : ι → σ) : Atom ι → Atom σ
  | .ordinary a b z => .ordinary (f a) (f b) (f z)
  | .shifted a b z => .shifted (f a) (f b) (f z)
  | .lower a b => .lower (f a) (f b)
  | .invLe a b => .invLe (f a) (f b)
  | .invRevGe a b => .invRevGe (f a) (f b)

theorem rename_holds {ι σ} (f : ι → σ) (a : Atom ι) (v : σ → ℝ) :
    (rename f a).Holds v ↔ a.Holds (v ∘ f) := by cases a <;> rfl

/-- Emits exactly the network's leaf occurrences, using the same name at
every occurrence of each bound or free variable. -/
def emit {ι σ} (p : Net ι) (inputs : ι → σ) (fresh : locals p → σ) : List (Atom σ) :=
  match p with
  | .atom a => [rename inputs a]
  | .both p q => emit p inputs (fresh ∘ Sum.inl) ++ emit q inputs (fresh ∘ Sum.inr)
  | .bind p => emit p (fun | none => fresh (.inl ()) | some i => inputs i) (fresh ∘ Sum.inr)

/-- Evaluate a network at fixed values of all its bound variables. -/
def assigned {ι} (p : Net ι) (x : ι → ℝ) (y : locals p → ℝ) : Prop :=
  match p with
  | .atom a => a.Holds x
  | .both p q => assigned p x (y ∘ Sum.inl) ∧ assigned q x (y ∘ Sum.inr)
  | .bind p => assigned p (push (y (.inl ())) x) (y ∘ Sum.inr)

theorem emit_length {ι σ} (p : Net ι) (f : ι → σ) (g : locals p → σ) :
    (emit p f g).length = p.size := by
  induction p with
  | atom a => rfl
  | both p q hp hq => simp [emit, Net.size, hp, hq]
  | bind p hp => exact hp _ _

theorem emit_holds {ι σ} (p : Net ι) (f : ι → σ) (g : locals p → σ) (v : σ → ℝ) :
    (∀ a ∈ emit p f g, a.Holds v) ↔ assigned p (v ∘ f) (v ∘ g) := by
  induction p with
  | atom a => simpa [emit, assigned] using rename_holds f a v
  | both p q hp hq =>
    rw [emit, List.forall_mem_append]
    exact and_congr (hp _ _) (hq _ _)
  | bind p hp =>
    rw [emit, assigned, hp]
    have h : (v ∘ (fun | none => g (.inl ()) | some i => f i)) =
        push (v (g (.inl ()))) (v ∘ f) := by funext i; cases i <;> rfl
    rw [h]
    rfl

theorem assigned_iff {ι} (p : Net ι) (x : ι → ℝ) :
    p.Holds x ↔ ∃ y : locals p → ℝ, (∀ i, InRange (y i)) ∧ assigned p x y := by
  induction p with
  | atom a =>
    exact ⟨fun h => ⟨Empty.elim, (fun i => Empty.elim i), h⟩, fun ⟨_,_,h⟩ => h⟩
  | both p q hp hq =>
    constructor
    · rintro ⟨a,b⟩
      obtain ⟨u,hu,hp'⟩ := (hp x).1 a
      obtain ⟨v,hv,hq'⟩ := (hq x).1 b
      exact ⟨Sum.elim u v, fun | .inl i => hu i | .inr i => hv i, hp', hq'⟩
    · rintro ⟨y,hy,hp',hq'⟩
      exact ⟨(hp x).2 ⟨y ∘ Sum.inl, fun i => hy (.inl i), hp'⟩,
        (hq x).2 ⟨y ∘ Sum.inr, fun i => hy (.inr i), hq'⟩⟩
  | bind p hp =>
    constructor
    · rintro ⟨z,hz,h⟩
      obtain ⟨u,hu,hp'⟩ := (hp (push z x)).1 h
      exact ⟨Sum.elim (fun _ => z) u, fun | .inl _ => hz | .inr i => hu i, hp'⟩
    · rintro ⟨y,hy,hp'⟩
      exact ⟨y (.inl ()), hy (.inl ()), (hp _).2 ⟨y ∘ Sum.inr, fun i => hy (.inr i), hp'⟩⟩

end ArtGallery.Orthogonal.BoundaryPoint.FlattenNetwork
end
