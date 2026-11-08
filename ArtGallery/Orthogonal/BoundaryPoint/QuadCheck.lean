module

public import ArtGallery.Orthogonal.BoundaryPoint.SepCert

/-! # Certified signs of quadratic expressions in chart coordinates

A sum of products of two linear expressions in the grid coordinates of a chart (with powers of
the reciprocal size `s`) is positive at every admissible size when its expanded register form
passes the box test `RegisterForm.positive` (as determinants do in `SepCert`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.QuadCheck
open RegisterForm RegisterPoly MarginCert SepCert

inductive Atom
  | x (i : Nat)
  | y (j : Nat)
  | one
  deriving DecidableEq

structure LinTerm where
  c : ℚ
  p : Nat
  a : Atom

abbrev Lin := List LinTerm
abbrev Quad := List (Lin × Lin)

def Atom.form (C : Chart) : Atom → Form
  | .x i => C.fx.getD i []
  | .y j => C.fy.getD j []
  | .one => RegisterForm.atom 0

def Atom.ok (C : Chart) : Atom → Bool
  | .x i => decide (i<C.nx)
  | .y j => decide (j<C.ny)
  | .one => true

def Atom.real (X Y : List ℝ) : Atom → ℝ
  | .x i => X.getD i 0
  | .y j => Y.getD j 0
  | .one => 1

def Lin.form (C : Chart) (l : Lin) : Form := l.foldr (fun t acc => plus (scaled t.p t.c (t.a.form C)) acc) []

def Lin.real (X Y : List ℝ) (s : ℝ) (l : Lin) : ℝ := (l.map fun t => (t.c:ℝ)*s^t.p*t.a.real X Y).sum

def Lin.ok (C : Chart) (l : Lin) : Bool := l.all fun t => t.a.ok C

def Quad.form (C : Chart) (q : Quad) : Form := q.foldr (fun pr acc => plus (mul (pr.1.form C) (pr.2.form C)) acc) []

def Quad.real (X Y : List ℝ) (s : ℝ) (q : Quad) : ℝ := (q.map fun pr => pr.1.real X Y s*pr.2.real X Y s).sum

def Quad.ok (C : Chart) (q : Quad) (k : Nat) : Bool :=
  q.all (fun pr => pr.1.ok C && pr.2.ok C) && RegisterForm.positive (B2 C.B) (q.form C) k

/-- The weak check: the expanded form is certified nonnegative. -/
def Quad.okN (C : Chart) (q : Quad) (k : Nat) : Bool :=
  q.all (fun pr => pr.1.ok C && pr.2.ok C) && RegisterForm.nonneg (B2 C.B) (q.form C) k

section
variable {C : Chart} {X Y : List ℝ} {s : ℚ} {A : Nat → ℚ}

theorem atom_real (G : Good C X Y s A) (one : A 0=1) {a : Atom} (h : a.ok C=true) :
    ((value s A (a.form C):ℚ):ℝ)=a.real X Y := by
  cases a with
  | x i => simp only [Atom.ok,decide_eq_true_eq] at h; simp only [Atom.form,Atom.real]; rw [G.vx i h]
  | y j => simp only [Atom.ok,decide_eq_true_eq] at h; simp only [Atom.form,Atom.real]; rw [G.vy j h]
  | one => simp [Atom.form,Atom.real,RegisterForm.atom,value,valTerm,one]

theorem lin_real (G : Good C X Y s A) (one : A 0=1) : ∀ {l : Lin}, l.ok C=true →
    ((value s A (l.form C):ℚ):ℝ)=l.real X Y s
  | [],_ => by simp [Lin.form,Lin.real,value]
  | t::l,h => by
    simp only [Lin.ok,List.all_cons,Bool.and_eq_true] at h
    have ih := lin_real G one (l:=l) (by simpa [Lin.ok] using h.2)
    simp only [Lin.form,List.foldr_cons] at ih ⊢
    rw [plus_value,scaled_value]
    push_cast
    rw [atom_real G one h.1]
    simp only [Lin.real,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]

theorem quad_value (q : Quad) :
    value s (A2 A) (q.form C)=(q.map fun pr => value s A (pr.1.form C)*value s A (pr.2.form C)).sum := by
  induction q with
  | nil => simp [Quad.form,value]
  | cons pr q ih =>
    simp only [Quad.form,List.foldr_cons] at ih ⊢
    rw [plus_value,mul_value,ih]; simp

/-- A certified quadratic expression in chart coordinates is positive. -/
theorem Quad.sound (G : Good C X Y s A) (one : A 0=1) {q : Quad} {k : Nat} (h : q.ok C k=true) :
    0<q.real X Y (s:ℝ) := by
  simp only [Quad.ok,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨hl,hp⟩ := h
  have pos := RegisterPoly.positive G.bounds G.pos G.small hp
  rw [quad_value] at pos
  have cast : ((((q.map fun pr => value s A (pr.1.form C)*value s A (pr.2.form C)).sum):ℚ):ℝ)=q.real X Y s := by
    simp only [Quad.real]
    push_cast
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro pr hpr
    have := hl pr hpr
    show (((value s A (pr.1.form C)*value s A (pr.2.form C)):ℚ):ℝ)=_
    push_cast
    rw [lin_real G one this.1,lin_real G one this.2]
  rw [← cast]
  exact_mod_cast pos

/-- A weakly certified quadratic expression in chart coordinates is nonnegative. -/
theorem Quad.sound_nonneg (G : Good C X Y s A) (one : A 0=1) {q : Quad} {k : Nat} (h : q.okN C k=true) :
    0≤q.real X Y (s:ℝ) := by
  simp only [Quad.okN,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨hl,hp⟩ := h
  have pos := RegisterPoly.nonneg G.bounds G.pos G.small hp
  rw [quad_value] at pos
  have cast : ((((q.map fun pr => value s A (pr.1.form C)*value s A (pr.2.form C)).sum):ℚ):ℝ)=q.real X Y s := by
    simp only [Quad.real]
    push_cast
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro pr hpr
    have := hl pr hpr
    show (((value s A (pr.1.form C)*value s A (pr.2.form C)):ℚ):ℝ)=_
    push_cast
    rw [lin_real G one this.1,lin_real G one this.2]
  rw [← cast]
  exact_mod_cast pos

end

end ArtGallery.Orthogonal.BoundaryPoint.QuadCheck
end
