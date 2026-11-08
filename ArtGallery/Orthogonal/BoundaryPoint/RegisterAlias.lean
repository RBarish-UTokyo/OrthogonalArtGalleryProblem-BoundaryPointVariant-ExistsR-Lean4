module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterOrder

/-! # Coincidences between independently computed pocket coordinates
When a pin pocket is narrowed, one endpoint can be computed as
`q + lambda * (q - q)`. The rule here refers to the actual straight-line
instructions and their relative operands. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterAlias
open MarginCert LinearRegister RegisterForm RegisterTable RegisterOrder ShapeRefs RoomCoordinates

def opAt (rs : List Row) (i : Nat) := rs[i]?.map Row.op

private theorem step {args rs xs i op} (h : Ledger args rs xs) (eq : opAt rs i=some op) :
    getRat xs i=op.rat args (xs.drop (i+1)) := by
  obtain ⟨r,hr,rfl⟩ := Option.map_eq_some_iff.mp eq
  exact original h hr

def opposite (rs : List Row) (a b : Nat) := match opAt rs b with
  | some (.neg k) => decide (a=b+1+k)
  | _ => false

def vanishes (rs : List Row) (i : Nat) := match opAt rs i with
  | some (.plus a b) => opposite rs (i+1+a) (i+1+b)
  | _ => false

def collapsed (rs : List Row) (i j : Nat) := match opAt rs i with
  | some (.plus a b) =>
    let k := i+1+b
    decide (i+1+a=j) && match opAt rs k with
      | some (.times _ v) => vanishes rs (k+1+v)
      | _ => false
  | _ => false

private theorem vanishes_sound {args rs xs} (h : Ledger args rs xs) {i : Nat} (ok : vanishes rs i=true) :
    getRat xs i=0 := by
  unfold vanishes at ok; split at ok
  next a b al =>
    unfold opposite at ok; split at ok
    next k neg =>
      obtain E := of_decide_eq_true ok
      rw [step h al,Op.rat,drop_lookup,drop_lookup,step h neg,Op.rat,drop_lookup,E,add_neg_cancel]
    · contradiction
  · contradiction

theorem collapsed_sound {args rs xs} (h : Ledger args rs xs) {i j : Nat} (ok : collapsed rs i j=true) :
    getRat xs i=getRat xs j := by
  unfold collapsed at ok; split at ok
  next a b al =>
    dsimp only at ok
    have test := (Bool.and_eq_true_iff.mp ok)
    obtain ⟨equal,product⟩ := test
    obtain rfl := of_decide_eq_true equal
    split at product
    next u v mul =>
      rw [step h al,Op.rat,drop_lookup,drop_lookup,step h mul,Op.rat,drop_lookup,drop_lookup,
        vanishes_sound h product,mul_zero,add_zero]
    · contradiction
  · contradiction

def direct (rs : List Row) : Ref → Ref → Bool
  | .origin,.origin => true
  | .register i,.register j => (i==j) || collapsed rs i j || collapsed rs j i
  | .level i,.level j => i==j
  | _,_ => false

private theorem direct_value {args rs xs} (h : Ledger args rs xs) (a : Axis) (p q : Ref) (ok : direct rs p q=true) :
    readRef xs a (getRat args 0) p=readRef xs a (getRat args 0) q := by
  cases p with
  | origin => cases q <;> first | rfl | contradiction
  | level i => cases q with
    | level j => obtain rfl := beq_iff_eq.mp ok; rfl
    | _ => contradiction
  | register i => cases q with
    | register j =>
      simp only [direct,Bool.or_eq_true,beq_iff_eq] at ok
      rcases ok with (rfl|h₁)|h₂
      · rfl
      · exact collapsed_sound h h₁
      · exact (collapsed_sound h h₂).symm
    | _ => contradiction

def equivalent (rs : List Row) (cache : List Entry) (a : Axis) (l r : Ref) :=
  direct rs l r || same (expression cache a l) (expression cache a r)

theorem equal {args xs rs bs cache} (m : Model args xs rs bs cache) (a : Axis) {l r : Ref}
    (pass : equivalent rs cache a l r=true) : readRef xs a (getRat args 0) l=readRef xs a (getRat args 0) r := by
  rcases (show direct rs l r=true ∨ same (expression cache a l) (expression cache a r)=true from
    by simpa only [equivalent,Bool.or_eq_true] using pass) with direct|normalized
  · exact direct_value m.run a l r direct
  · simpa only [formula m] using same_value normalized (getRat args 0) (atomVal xs)

end ArtGallery.Orthogonal.BoundaryPoint.RegisterAlias
end
