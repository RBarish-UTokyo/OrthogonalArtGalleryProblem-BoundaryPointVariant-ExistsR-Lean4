module

public import ArtGallery.Orthogonal.BoundaryPoint.PrivatePorts

/-! # Private-port lowering for lists of primitive atoms

A row has six wiring leaves per input occurrence and one arithmetic leaf.
The row index and port index name the auxiliary slots. Master slots and the
lower-output slot are shared across every row.
-/

@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PrivatePorts

open DerivedAlgebra PrimitiveNetwork

def ports {ι} : Atom ι → List Port
  | .ordinary .. | .shifted .. => [.first,.second,.third]
  | .lower .. | .invLe .. | .invRevGe .. => [.first,.second]

/-- The third entry of a binary atom is unused by its row. -/
def input {ι} (a : Atom ι) (k : Port) : ι :=
  match a with
  | .ordinary x y z | .shifted x y z => match k with
    | .first => x | .second => y | .third => z
  | .lower x y | .invLe x y | .invRevGe x y => match k with
    | .first => x | .second => y | .third => y

def payload {ι row} (r : row) : Atom ι → Leaf (Slot ι row)
  | .ordinary .. => .ordinary (.privatePort r .first) (.privatePort r .second) (.privatePort r .third)
  | .shifted .. => .shifted (.privatePort r .first) (.privatePort r .second) (.privatePort r .third)
  | .lower .. => .lower (.privatePort r .first) (.privatePort r .second) .half
  | .invLe .. => .invLe (.privatePort r .first) (.privatePort r .second)
  | .invRevGe .. => .invRevGe (.privatePort r .first) (.privatePort r .second)

def lowerRow {ι row} (r : row) (a : Atom ι) : List (Leaf (Slot ι row)) :=
  ((ports a).flatMap fun k => wire r k (input a k)) ++ [payload r a]

private theorem allHold_row {ι row} (r : row) (a : Atom ι) (v : Slot ι row → ℝ) :
    allHold v (lowerRow r a) ↔
    (∀ k ∈ ports a, allHold v (wire r k (input a k))) ∧ (payload r a).Holds v := by
  simp only [allHold, lowerRow, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_singleton]

private theorem payload_iff {ι row} (r : row) (a : Atom ι) (v : Slot ι row → ℝ)
    (hc : v .half = 1/2)
    (hp : ∀ k ∈ ports a, v (.privatePort r k) = v (.master (input a k))) :
    (payload r a).Holds v ↔ a.Holds (fun i => v (.master i)) := by
  cases a <;> simp_all [payload, Leaf.Holds, Atom.Holds, ports, input, LowerComplement]
  norm_num

theorem row_sound {ι row} (r : row) (a : Atom ι) (v : Slot ι row → ℝ)
    (hv : ∀ s, InRange (v s)) (hall : allHold v (lowerRow r a)) :
    a.Holds (fun i => v (.master i)) := by
  obtain ⟨hw, hp⟩ := (allHold_row r a v).1 hall
  have h k (hk : k ∈ ports a) := (wire_iff r k (input a k) v hv).1 (hw k hk)
  have hfirst : Port.first ∈ ports a := by cases a <;> simp [ports]
  exact (payload_iff r a v (h .first hfirst).1 (fun k hk => (h k hk).2.1)).1 hp

theorem row_length {ι row} (r : row) (a : Atom ι) :
    (lowerRow r a).length = 6 * (ports a).length + 1 := by cases a <;> rfl

theorem row_ordered {ι row} (r : row) (a : Atom ι) : ∀ l ∈ lowerRow r a, l.Ordered := by
  intro l hl
  rcases List.mem_append.1 hl with hw | hp
  · obtain ⟨k, _, hk⟩ := List.mem_flatMap.1 hw
    exact wire_ordered _ _ _ _ hk
  · obtain rfl := List.mem_singleton.1 hp
    cases a <;> simp [payload, Leaf.Ordered, bank]

/-- Distinct private slots are named by their occurrence in the input list.
The shared constant is present even if the list has no rows. -/
def physical {ι} (atoms : List (Atom ι)) : List (Leaf (Slot ι (Fin atoms.length))) :=
  (List.ofFn fun r : Fin atoms.length => lowerRow r atoms[r]).flatten

theorem physical_rows {ι} (atoms : List (Atom ι)) (v : Slot ι (Fin atoms.length) → ℝ) :
    allHold v (physical atoms) ↔ ∀ r : Fin atoms.length, allHold v (lowerRow r atoms[r]) := by
  simp only [allHold, physical, List.forall_mem_flatten]
  constructor
  · intro h i
    exact h _ (List.mem_ofFn.2 ⟨i,rfl⟩)
  · intro h row hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hr
    exact h i

theorem physical_ordered {ι} (atoms : List (Atom ι)) : ∀ l ∈ physical atoms, l.Ordered := by
  intro l hl
  obtain ⟨row, hr, hl'⟩ := List.mem_flatten.1 hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hr
  exact row_ordered _ _ _ hl'

private theorem flatten_bound {α : Type} (rows : List (List α))
    (h : ∀ r ∈ rows, r.length ≤ 19) : rows.flatten.length ≤ 19 * rows.length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    have hu := h r (by simp)
    have hv := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem physical_length {ι} (atoms : List (Atom ι)) :
    (physical atoms).length ≤ 19 * atoms.length := by
  unfold physical
  apply le_trans (flatten_bound _ ?_)
  · simp
  · intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hr
    rw [row_length]
    cases atoms[i] <;> norm_num [ports]

noncomputable def extend {ι} (atoms : List (Atom ι)) (x : ι → ℝ) :
    Slot ι (Fin atoms.length) → ℝ
  | .master i => x i
  | .half => 1/2
  | .privatePort r k => x (input atoms[r] k)
  | .middle r k => complement (x (input atoms[r] k))
  | .reciprocal r k _ => 1 / x (input atoms[r] k)

theorem extend_range {ι} (atoms : List (Atom ι)) (x : ι → ℝ) (hx : ∀ i, InRange (x i)) :
    ∀ s, InRange (extend atoms x s) := by
  intro s
  cases s with
  | master i => exact hx i
  | half => norm_num [extend, InRange]
  | privatePort r k => exact hx _
  | middle r k => exact complement_inRange (hx _)
  | reciprocal r k i => exact reciprocal_inRange (hx _)

theorem extend_correct {ι} (atoms : List (Atom ι)) (x : ι → ℝ) (hx : ∀ i, InRange (x i)) :
    allHold (extend atoms x) (physical atoms) ↔ ∀ a ∈ atoms, a.Holds x := by
  rw [physical_rows]
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    exact row_sound (⟨i,hi⟩ : Fin atoms.length) _ _ (extend_range atoms x hx) (h _)
  · intro h i
    apply (allHold_row i atoms[i] (extend atoms x)).2
    constructor
    · intro k _
      exact (wire_iff _ _ _ _ (extend_range atoms x hx)).2 ⟨rfl,rfl,rfl,rfl,rfl⟩
    · apply (payload_iff i atoms[i] _ rfl (fun _ _ => rfl)).2
      exact h _ (List.getElem_mem i.2)

/-- Soundness decodes arbitrary physical assignments, including arbitrary
choices at the auxiliary slots. Completeness uses the explicit extension. -/
theorem physical_correct {ι} (atoms : List (Atom ι)) (x : ι → ℝ) (hx : ∀ i, InRange (x i)) :
    (∃ v : Slot ι (Fin atoms.length) → ℝ, (∀ s, InRange (v s)) ∧
      (∀ i, v (.master i) = x i) ∧ allHold v (physical atoms)) ↔
    ∀ a ∈ atoms, a.Holds x := by
  constructor
  · rintro ⟨v,hv,hm,h⟩ a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.1 ha
    have he := row_sound (⟨i,hi⟩ : Fin atoms.length) _ v hv ((physical_rows atoms v).1 h _)
    simpa only [Fin.getElem_fin, show (fun i => v (.master i)) = x from funext hm] using he
  · intro h
    exact ⟨extend atoms x, extend_range atoms x hx, fun _ => rfl, (extend_correct atoms x hx).2 h⟩

end ArtGallery.Orthogonal.BoundaryPoint.PrivatePorts
end
