module

public import ArtGallery.Orthogonal.BoundaryPoint.PrimitiveNetwork

/-! # Bank-ordered private ports for primitive leaves

For each occurrence of an input there is a private port, an intermediate
complement, and two reciprocal slots. The output slot of every lower leaf is
the same global slot. Slot labels retain the row and port of their occurrence,
so repeated primitive inputs can still occupy distinct physical ports.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PrivatePorts

open DerivedAlgebra PrimitiveNetwork

inductive Port where | first | second | third

inductive Slot (ι row : Type) where
  | master (i : ι)
  | half
  | privatePort (r : row) (k : Port)
  | middle (r : row) (k : Port)
  | reciprocal (r : row) (k : Port) (forMaster : Bool)

def bank {ι row} : Slot ι row → Nat
  | .master _ => 360
  | .half => 1000
  | .privatePort _ .first => 40
  | .privatePort _ .second => 200
  | .privatePort _ .third => 520
  | .middle .. => 10
  | .reciprocal .. => 1

inductive Leaf (σ : Type) where
  | ordinary (a b z : σ)
  | shifted (a b z : σ)
  | lower (a b c : σ)
  | invLe (m x : σ)
  | invRevGe (m x : σ)

def Leaf.Holds {σ} (v : σ → ℝ) : Leaf σ → Prop
  | .ordinary a b z => v z ≤ v a + v b
  | .shifted a b z => ShiftedAddGe (v a) (v b) (v z)
  | .lower a b c => 2 + v c ≤ v a + v b
  | .invLe m x => InvLe (v m) (v x)
  | .invRevGe m x => InvRevGe (v m) (v x)

def Leaf.Ordered {ι row} : Leaf (Slot ι row) → Prop
  | .ordinary a b z | .shifted a b z | .lower a b z => bank a < bank b ∧ bank b < bank z
  | .invLe a b | .invRevGe a b => bank a < bank b

def wire {ι row} (r : row) (k : Port) (i : ι) : List (Leaf (Slot ι row)) :=
  [ .invRevGe (.reciprocal r k false) (.middle r k),
    .invLe (.reciprocal r k false) (.privatePort r k),
    .lower (.middle r k) (.privatePort r k) .half,
    .invRevGe (.reciprocal r k true) (.middle r k),
    .invLe (.reciprocal r k true) (.master i),
    .lower (.middle r k) (.master i) .half ]

theorem three_leaves_iff {m w x c : ℝ} (hm : InRange m) (hx : InRange x) (hc : InRange c) :
    (InvRevGe m w ∧ InvLe m x ∧ 2+c ≤ w+x) ↔
    c = 1/2 ∧ w = complement x ∧ m = 1/x := by
  constructor
  · rintro ⟨hr, hl, hc'⟩
    obtain ⟨he, hcomp⟩ := (shared_lower_output hx hc).1 ⟨hc', m, hm, hr, hl⟩
    have hw : w = complement x := by rw [hcomp, complement_complement]
    have hr' : 1 ≤ m*x := by simpa [InvRevGe, complement] using hcomp ▸ hr
    exact ⟨he, hw, (eq_div_iff (positive_of_inRange hx).ne').2 (le_antisymm hl hr')⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hprod := one_div_mul_cancel (positive_of_inRange hx).ne'
    dsimp [InvRevGe, InvLe, complement]
    constructor
    · convert hprod.ge using 1
      ring
    · exact ⟨hprod.le, by linarith⟩

def allHold {σ} (v : σ → ℝ) (leaves : List (Leaf σ)) : Prop :=
  ∀ l ∈ leaves, l.Holds v

theorem wire_iff {ι row} (r : row) (k : Port) (i : ι) (v : Slot ι row → ℝ)
    (hv : ∀ s, InRange (v s)) :
    allHold v (wire r k i) ↔
    v .half = 1/2 ∧ v (.privatePort r k) = v (.master i) ∧
    v (.middle r k) = complement (v (.master i)) ∧
    v (.reciprocal r k false) = 1/v (.master i) ∧ v (.reciprocal r k true) = 1/v (.master i) := by
  simp [allHold, wire, Leaf.Holds, -one_div]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
    obtain ⟨hh, hmid, hrec⟩ := (three_leaves_iff (hv (.reciprocal r k true)) (hv (.master i)) (hv .half)).1 ⟨h₄,h₅,h₆⟩
    obtain ⟨_, hp, hrec'⟩ := (three_leaves_iff (hv (.reciprocal r k false)) (hv (.privatePort r k)) (hv .half)).1 ⟨h₁,h₂,h₃⟩
    have he : v (.privatePort r k) = v (.master i) := by
      dsimp [complement] at hp hmid
      linarith
    exact ⟨hh, he, hmid, he ▸ hrec', hrec⟩
  · rintro ⟨hh,he,hmid,hrec',hrec⟩
    have a := (three_leaves_iff (hv (.reciprocal r k false)) (hv (.privatePort r k)) (hv .half)).2
      ⟨hh, he ▸ hmid, he ▸ hrec'⟩
    have b := (three_leaves_iff (hv (.reciprocal r k true)) (hv (.master i)) (hv .half)).2
      ⟨hh,hmid,hrec⟩
    exact ⟨a.1,a.2.1,a.2.2,b⟩

theorem wire_ordered {ι row} (r : row) (k : Port) (i : ι) :
    ∀ l ∈ wire r k i, l.Ordered := by
  cases k <;> simp [wire, Leaf.Ordered, bank]

end ArtGallery.Orthogonal.BoundaryPoint.PrivatePorts
end
