module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterForm

/-! # Checked linearization rules for the scaled register model
Products with a scalar times a scale power stay linear in the register
atoms. Other products can always retain their exact original register. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterOp
open MarginCert RegisterForm

def scalar : Form → Option (Nat × ℚ)
  | [] => some (0,0)
  | [((k,i),c)] => if i=0 then some (k,c) else none
  | _ => none

theorem scalar_value {f : Form} {k : Nat} {c s : ℚ} {A : Nat → ℚ}
    (one : A 0=1) (h : scalar f=some (k,c)) : value s A f=c*s^k := by
  rcases f with _|⟨⟨⟨a,i⟩,b⟩,ts⟩
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h); simp [value]
  · cases ts with
    | nil =>
      simp [scalar] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      simp [value,valTerm,one]
    | cons => contradiction

def product (a b : Form) : Option Form := match scalar a with
  | some (k,c) => some (scaled k c b)
  | none => (scalar b).map (fun m => scaled m.1 m.2 a)

def inverse (a : Form) : Option Form := do
  let f ← scalar a
  if f.1=0 then some (const f.2⁻¹) else none

theorem product_value {a b f : Form} {A : Nat → ℚ} {s : ℚ} (one : A 0=1)
    (h : product a b=some f) : value s A f=value s A a*value s A b := by
  unfold product at h; split at h
  next k c eq =>
    obtain rfl := Option.some.inj h
    rw [scaled_value,scalar_value one eq]
  next _ =>
    obtain ⟨⟨k,c⟩,eq,rfl⟩ := Option.map_eq_some_iff.mp h
    rw [scaled_value,scalar_value one eq,mul_comm (value s A a)]

theorem inverse_value {a f : Form} {A : Nat → ℚ} {s : ℚ} (one : A 0=1)
    (h : inverse a=some f) : value s A f=(value s A a)⁻¹ := by
  obtain ⟨⟨k,c⟩,eq,rest⟩ := Option.bind_eq_some_iff.mp h
  by_cases z : k=0
  · simp [z] at rest; subst f
    rw [const_value _ _ _ one,scalar_value one eq,z,pow_zero,mul_one]
  · simp [z] at rest

inductive Rule where
  | linear
  | fixed
  | upperLeft (drop : Nat)
  | upperRight (drop : Nat)
  | absPlus (drop : Nat)
  | absMinus (drop : Nat)

def linear (G : Nat → Form) : Op → Option Form
  | .lit c => some (const c)
  | .input i => if i=0 then some [((1,0),1)] else none
  | .neg i => some (scaled 0 (-1) (G i))
  | .plus i j => some (plus (G i) (G j))
  | .times i j => product (G i) (G j)
  | .recip i => inverse (G i)
  | _ => none

def applyRule (B : Nat → Box) (G : Nat → Form) (raw : Box) (op : Op) : Rule → Option Form
  | .linear => linear G op
  | .fixed => if raw.lo=raw.hi then some (const raw.lo) else none
  | .upperLeft k => match op with
    | .larger i j => if nonneg B (diff (G i) (G j)) k then some (G i) else none
    | _ => none
  | .upperRight k => match op with
    | .larger i j => if nonneg B (diff (G j) (G i)) k then some (G j) else none
    | _ => none
  | .absPlus k => match op with
    | .absVal i => if nonneg B (G i) k then some (G i) else none
    | _ => none
  | .absMinus k => match op with
    | .absVal i => if nonneg B (scaled 0 (-1) (G i)) k then some (scaled 0 (-1) (G i)) else none
    | _ => none

private theorem linear_sound {args vs : List ℚ} {A : Nat → ℚ} (one : A 0=1) (G : Nat → Form)
    (lookup : ∀ i,value (getRat args 0) A (G i)=getRat vs i) (op : Op) {f : Form}
    (h : linear G op=some f) : value (getRat args 0) A f=op.rat args vs := by
  cases op with
  | lit c => obtain rfl := Option.some.inj h; exact const_value _ _ _ one
  | input i =>
    by_cases eq : i=0
    · subst i; simp [linear] at h; subst f; simp [value,valTerm,one,Op.rat]
    · simp [linear,eq] at h
  | neg i => obtain rfl := Option.some.inj h; simp [scaled_value,lookup,Op.rat]
  | plus i j => obtain rfl := Option.some.inj h; simp [plus_value,lookup,Op.rat]
  | times i j => simpa only [lookup,Op.rat] using product_value (s:=getRat args 0) one h
  | recip i => simpa only [lookup,Op.rat] using inverse_value (s:=getRat args 0) one h
  | larger | absVal => contradiction

theorem sound {B A} (encl : Bounds B A) (one : A 0=1) {args vs : List ℚ}
    (hs : 0<getRat args 0) (hu : getRat args 0≤cap) (G : Nat → Form)
    (lookup : ∀ i,value (getRat args 0) A (G i)=getRat vs i)
    (b : Box) (op : Op) (bound : b.lo≤op.rat args vs ∧ op.rat args vs≤b.hi)
    (rule : Rule) {f : Form} (h : applyRule B G b op rule=some f) :
    value (getRat args 0) A f=op.rat args vs := by
  cases rule with
  | linear => exact linear_sound one G lookup op h
  | fixed =>
    by_cases z : b.lo=b.hi
    · simp [applyRule,z] at h; subst f
      rw [const_value _ _ _ one]
      linarith [bound.1,bound.2]
    · simp [applyRule,z] at h
  | upperLeft k =>
    cases op <;> try contradiction
    rename_i i j
    simp only [applyRule] at h; split at h
    next ok =>
      obtain rfl := Option.some.inj h
      have order := nonneg_value encl hs hu ok
      rw [diff_value,lookup,lookup] at order
      rw [lookup,Op.rat,max_eq_left (sub_nonneg.mp order)]
    · contradiction
  | upperRight k =>
    cases op <;> try contradiction
    rename_i i j
    simp only [applyRule] at h; split at h
    next ok =>
      obtain rfl := Option.some.inj h
      have order := nonneg_value encl hs hu ok
      rw [diff_value,lookup,lookup] at order
      rw [lookup,Op.rat,max_eq_right (sub_nonneg.mp order)]
    · contradiction
  | absPlus k =>
    cases op <;> try contradiction
    rename_i i
    simp only [applyRule] at h; split at h
    next ok =>
      obtain rfl := Option.some.inj h
      have order := nonneg_value encl hs hu ok
      rw [lookup] at order ⊢
      exact (abs_of_nonneg order).symm
    · contradiction
  | absMinus k =>
    cases op <;> try contradiction
    rename_i i
    simp only [applyRule] at h; split at h
    next ok =>
      obtain rfl := Option.some.inj h
      have order := nonneg_value encl hs hu ok
      simp only [scaled_value,pow_zero,mul_one,neg_one_mul,lookup] at order ⊢
      exact (abs_of_nonpos (by linarith)).symm
    · contradiction

end ArtGallery.Orthogonal.BoundaryPoint.RegisterOp
end
