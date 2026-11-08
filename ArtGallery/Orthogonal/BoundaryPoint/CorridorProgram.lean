module

public import ArtGallery.Orthogonal.BoundaryPoint.MarginEval

/-! # Rational rectangle and guard data for a compiled staircase

Rectangles use left, right, bottom and top coordinates. Each role lists the
canonical point, the two permitted segment ends, and its three witnesses.
Reading a fixed set of registers from a fixed arithmetic program is PT.
-/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CorridorProgram
open MarginCert Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

abbrev Rect (α : Type) := α × α × α × α
abbrev Data (α : Type) := List (Rect α) × List (List (α × α))

structure Layout where
  baseRows : List Row
  rest : List Row
  cells : List (Rect Nat)
  roles : List (List (Nat × Nat))

def readRect (xs : List ℚ) (z : Rect Nat) : Rect ℚ :=
  (getRat xs z.1,getRat xs z.2.1,getRat xs z.2.2.1,getRat xs z.2.2.2)

def readRole (xs : List ℚ) (js : List (Nat × Nat)) : List (ℚ × ℚ) :=
  js.map fun j => (getRat xs j.1,getRat xs j.2)

def Layout.coords (s : Layout) (args : List ℚ) : Data ℚ :=
  let xs := execRat args (execRat args [] s.baseRows) s.rest
  (s.cells.map (readRect xs),s.roles.map (readRole xs))

section Computation
variable {α : Type} [Code α]

private theorem read_rect_pt (j : Rect Nat) {xs : α → List ℚ} (hx : PT xs) :
    PT (fun a => readRect (xs a) j) := by unfold readRect; fun_prop

private theorem read_role_pt (js : List (Nat × Nat)) {xs : α → List ℚ} (hx : PT xs) :
    PT (fun a => readRole (xs a) js) := by
  induction js with
  | nil => exact PT.const []
  | cons j js ih => exact PT.cons (PT.pair (lookup_pt hx (PT.const _)) (lookup_pt hx (PT.const _))) ih

theorem coords_pt (s : Layout) {args : α → List ℚ} (ha : PT args) :
    PT (fun a => s.coords (args a)) := by
  let xs := fun a => execRat (args a) (execRat (args a) [] s.baseRows) s.rest
  have hx : PT xs := exec_pt _ ha (exec_pt _ ha (PT.const _))
  have hc (l : List (Rect Nat)) : PT (fun a => l.map (readRect (xs a))) := by
    induction l with
    | nil => exact PT.const []
    | cons j l ih => exact PT.cons (read_rect_pt j hx) ih
  have hr (l : List (List (Nat × Nat))) : PT (fun a => l.map (readRole (xs a))) := by
    induction l with
    | nil => exact PT.const []
    | cons j l ih => exact PT.cons (read_role_pt j hx) ih
  exact PT.pair (hc s.cells) (hr s.roles)

end Computation
end ArtGallery.Orthogonal.BoundaryPoint.CorridorProgram
end
