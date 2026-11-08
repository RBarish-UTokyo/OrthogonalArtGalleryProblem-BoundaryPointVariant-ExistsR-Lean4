module

public import ArtGallery.Orthogonal.BoundaryPoint.MarginCert
public import ArtGallery.Stade.PTimeRat

/-! # Exact rational execution of fixed construction programs

A program has fixed length for its port profile. Its evaluation is
polynomial-time in the supplied rational inputs in the repository's machine
model, and its rational registers cast to the real semantics used for the
margin checks. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.MarginCert

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

def getRat (xs : List ℚ) (i : Nat) : ℚ := xs[i]?.getD 0

def Op.rat (args xs : List ℚ) : Op → ℚ
  | .input i => getRat args i
  | .lit q => q
  | .neg i => -getRat xs i
  | .plus i j => getRat xs i + getRat xs j
  | .times i j => getRat xs i * getRat xs j
  | .recip i => (getRat xs i)⁻¹
  | .absVal i => |getRat xs i|
  | .larger i j => max (getRat xs i) (getRat xs j)

def execRat (args : List ℚ) : List ℚ → List Row → List ℚ
  | xs, [] => xs
  | xs, r::rs => execRat args (r.op.rat args xs :: xs) rs

noncomputable def execReal (args : List ℝ) : List ℝ → List Row → List ℝ
  | xs, [] => xs
  | xs, r::rs => execReal args (r.op.val args xs :: xs) rs

private theorem cast_lookup (xs : List ℚ) (i : Nat) :
    (getRat xs i : ℝ) = getReal (xs.map (fun x : ℚ => (x:ℝ))) i := by
  unfold getRat getReal
  rw [List.getElem?_map]
  cases xs[i]? <;> simp

theorem cast_op (op : Op) (a xs : List ℚ) : (op.rat a xs : ℝ) =
    op.val (a.map (fun q : ℚ => (q:ℝ))) (xs.map (fun q : ℚ => (q:ℝ))) := by
  cases op <;> simp [Op.val,Op.rat,cast_lookup]

theorem cast_exec (a xs : List ℚ) (rs : List Row) :
    (execRat a xs rs).map (fun q : ℚ => (q:ℝ)) =
    execReal (a.map (fun q : ℚ => (q:ℝ))) (xs.map (fun q : ℚ => (q:ℝ))) rs := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih =>
    simpa only [execRat,execReal,List.map_cons,cast_op] using ih (r.op.rat a xs :: xs)

private theorem negNum (q : ℚ) : q.num < 0 ↔ q < 0 := by
  rw [← not_le,← not_le (a := 0) (b := q),Rat.num_nonneg]

private theorem max_eq_num (a b : ℚ) : max a b = if (a-b).num < 0 then b else a := by
  split
  · rename_i h
    exact max_eq_right (by linarith [(negNum _).mp h])
  · rename_i h
    exact max_eq_left (by linarith [le_of_not_gt (fun hn => h ((negNum _).mpr hn))])

private theorem abs_eq_num (a : ℚ) : |a| = if a.num < 0 then -a else a := by
  split
  · rename_i h
    exact abs_of_neg ((negNum _).mp h)
  · rename_i h
    exact abs_of_nonneg (le_of_not_gt (fun hn => h ((negNum _).mpr hn)))

section Computation
variable {α : Type} [Code α]
@[fun_prop] theorem lookup_pt {xs : α → List ℚ} {i : α → Nat} (hx : PT xs) (hi : PT i) :
    PT (fun a => getRat (xs a) (i a)) := by unfold getRat; fun_prop

theorem op_pt (op : Op) {args xs : α → List ℚ} (ha : PT args) (hx : PT xs) :
    PT (fun a => op.rat (args a) (xs a)) := by
  cases op <;> simp only [Op.rat,max_eq_num,abs_eq_num] <;> fun_prop

theorem exec_pt (rs : List Row) {args xs : α → List ℚ} (ha : PT args) (hx : PT xs) :
    PT (fun a => execRat (args a) (xs a) rs) := by
  induction rs generalizing xs with
  | nil => exact hx
  | cons r rs ih => exact ih (PT.cons (op_pt r.op ha hx) hx)

end Computation
end ArtGallery.Orthogonal.BoundaryPoint.MarginCert
end
