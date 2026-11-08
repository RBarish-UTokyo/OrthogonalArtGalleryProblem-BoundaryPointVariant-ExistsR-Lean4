module

public import ArtGallery.Orthogonal.BoundaryPoint.CorridorProgram

/-! # Selected registers of a physical coordinate program
The interval checker encloses every register. A short backwards slice can
also prove an exact affine expression in the first argument. In particular
it can distinguish a positive thin-channel height from its zero-scale limit. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.LinearRegister
open MarginCert

abbrev Aff := ℚ × ℚ
def val (s : ℚ) (f : Aff) := f.1+f.2*s

def addA (a b : Aff) : Aff := (a.1+b.1,a.2+b.2)
def negA (a : Aff) : Aff := (-a.1,-a.2)
def mulA (a b : Aff) : Option Aff :=
  if a.2=0 then some (a.1*b.1,a.1*b.2)
  else if b.2=0 then some (a.1*b.1,a.2*b.1) else none

def readOp (lookup : Nat → Option Aff) : Op → Option Aff
  | .input i => if i=0 then some (0,1) else none
  | .lit c => some (c,0)
  | .plus i j => do return addA (← lookup i) (← lookup j)
  | .neg i => (lookup i).map negA
  | .times i j => do mulA (← lookup i) (← lookup j)
  | .recip i => do
    let a ← lookup i
    if a.2=0 then some (a.1⁻¹,0) else none
  | _ => none

def read : Nat → List Row → Nat → Option Aff
  | 0,_,_ => none
  | fuel+1,rows,i => match rows.drop i with
    | [] => none
    | r::rs => readOp (read fuel rs) r.op

theorem mul_sound {a b c : Aff} {s : ℚ} (h : mulA a b=some c) :
    val s c=val s a*val s b := by
  unfold mulA at h; split at h
  next zero =>
    obtain rfl := Option.some.inj h
    simp [val,zero]; ring
  · split at h
    next zero => obtain rfl := Option.some.inj h; simp [val,zero]; ring
    · contradiction

private theorem op_sound {args xs : List ℚ} {f : Nat → Option Aff}
    (invariant : ∀ i a,f i=some a → getRat xs i=val (getRat args 0) a)
    (op : Op) {out : Aff} (h : readOp f op=some out) : op.rat args xs=val (getRat args 0) out := by
  cases op with
  | input i =>
    by_cases z : i=0
    · subst i
      simp [readOp] at h
      subst out; simp [Op.rat,val]
    · simp [readOp,z] at h
  | lit c => obtain rfl := Option.some.inj h; simp [Op.rat,val]
  | plus i j =>
    cases a : f i with
    | none => simp [readOp,a] at h
    | some x =>
      cases b : f j with
      | none => simp [readOp,a,b] at h
      | some y =>
        simp [readOp,a,b] at h; subst out
        simp only [Op.rat,invariant _ _ a,invariant _ _ b,addA,val]; ring
  | neg i =>
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Op.rat,invariant _ _ ha,negA,val]; ring
  | times i j =>
    cases a : f i with
    | none => simp [readOp,a] at h
    | some x =>
      cases b : f j with
      | none => simp [readOp,a,b] at h
      | some y =>
        simp [readOp,a,b] at h
        exact (congrArg₂ (·*·) (invariant _ _ a) (invariant _ _ b)).trans (mul_sound h).symm
  | recip i =>
    cases a : f i with
    | none => simp [readOp,a] at h
    | some x =>
      by_cases b : x.2=0
      · simp [readOp,a,b] at h; subst out; simp [Op.rat,invariant _ _ a,val,b]
      · simp [readOp,a,b] at h
  | absVal | larger => contradiction

inductive Ledger (args : List ℚ) : List Row → List ℚ → Prop
  | nil : Ledger args [] []
  | cons {rs xs} (r : Row) (h : Ledger args rs xs) : Ledger args (r::rs) (r.op.rat args xs::xs)

theorem exec_ledger {args : List ℚ} {rs : List Row} {xs : List ℚ} (h : Ledger args rs xs) (p : List Row) :
    Ledger args (p.reverse++rs) (execRat args xs p) := by
  induction p generalizing rs xs with
  | nil => simpa only [List.reverse_nil,List.nil_append,execRat] using h
  | cons r p ih => simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,execRat] using ih (h.cons r)

private theorem dropped {args rs xs} (h : Ledger args rs xs) (i : Nat) :
    Ledger args (rs.drop i) (xs.drop i) := by
  induction h generalizing i with
  | nil => simp; constructor
  | cons r h ih => cases i <;> simp only [List.drop_zero,List.drop_succ_cons] <;> first | exact h.cons _ | exact ih _

theorem read_value {args : List ℚ} {rows xs} (h : Ledger args rows xs) (fuel i : Nat) {a : Aff}
    (good : read fuel rows i=some a) : getRat xs i=val (getRat args 0) a := by
  induction fuel generalizing rows xs i a with
  | zero => contradiction
  | succ fuel ih =>
    rw [read] at good
    cases eq : rows.drop i with
    | nil => simp [eq] at good
    | cons r tail =>
      simp only [eq] at good
      have data := dropped h i
      rw [eq] at data
      generalize hs : xs.drop i=rest at data
      cases data with
      | cons _ prev =>
        have headEq := congrArg List.head? hs
        simp only [List.head?_drop,List.head?_cons] at headEq
        unfold getRat; rw [headEq]; apply op_sound (fun j b he => ih prev j he) _ good

theorem stack_bound {ab : List Box} {av : List ℝ} (args : Encloses ab av) (rs : List Row)
    {bs : List Box} {vs : List ℝ} (prev : Encloses bs vs) (checks : ok ab bs rs=true) :
    Encloses (stack bs rs) (execReal av vs rs) := by
  induction rs generalizing bs vs with
  | nil => exact prev
  | cons r rs ih =>
    simp only [ok,Bool.and_eq_true] at checks
    exact ih (prev.cons (Op.sound args prev checks.1.1)) checks.2

theorem lookup_bound {a xs : List ℚ} {bs : List Box} {rs : List Row} {ab : List Box}
    (args : Encloses ab (a.map ((↑) : ℚ → ℝ))) (prev : Encloses bs (xs.map ((↑) : ℚ → ℝ)))
    (check : ok ab bs rs=true) (i : Nat) :
    let b := getBox (stack bs rs) i
    let v := getRat (execRat a xs rs) i
    b.lo≤v ∧ v≤b.hi := by
  have t := stack_bound args rs prev check i
  rw [← cast_exec] at t
  let vs := execRat a xs rs
  have lookup : getReal (vs.map ((↑) : ℚ → ℝ)) i=(getRat vs i:ℝ) := by
    unfold getReal getRat; rw [List.getElem?_map]; cases vs[i]? <;> simp
  rw [show execRat a xs rs=vs by rfl,lookup] at t
  exact ⟨Rat.cast_le.mp t.1,Rat.cast_le.mp t.2⟩

theorem stack_append (bs : List Box) (a b : List Row) :
    stack bs (a++b)=stack (stack bs a) b := by
  induction a generalizing bs with
  | nil => rfl
  | cons r a ih => exact ih _

theorem exec_append (args xs : List ℚ) (a b : List Row) :
    execRat args xs (a++b)=execRat args (execRat args xs a) b := by
  induction a generalizing xs with
  | nil => rfl
  | cons r a ih => exact ih _

end ArtGallery.Orthogonal.BoundaryPoint.LinearRegister
end
