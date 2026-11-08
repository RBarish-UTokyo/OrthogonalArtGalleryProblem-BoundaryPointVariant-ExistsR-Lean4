module

public import ArtGallery.Orthogonal.BoundaryPoint.LinearRegister

/-! # Sparse, scaled linear combinations of physical staircase registers
A term is a rational coefficient times a nonnegative power of the positive
reciprocal size, times a named register. Atom zero is the constant one. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterForm
open MarginCert

abbrev Key := Nat × Nat
abbrev Term := Key × ℚ
abbrev Form := List Term

def valTerm (s : ℚ) (A : Nat → ℚ) (t : Term) : ℚ := t.2 * s^t.1.1 * A t.1.2
def value (s : ℚ) (A : Nat → ℚ) : Form → ℚ
  | [] => 0
  | t::f => valTerm s A t+value s A f

def singleton (key : Key) (c : ℚ) : Form := if c=0 then [] else [(key,c)]
def atom (i : Nat) : Form := [((0,i),1)]
def const (c : ℚ) : Form := singleton (0,0) c

def insert (k : Key) (c : ℚ) : Form → Form
  | [] => singleton k c
  | t::ts =>
    if k=t.1 then if c+t.2=0 then ts else (k,c+t.2)::ts
    else t::insert k c ts

def plus : Form → Form → Form
  | [],b => b
  | t::a,b => insert t.1 t.2 (plus a b)

def scaled (k : Nat) (c : ℚ) (f : Form) : Form :=
  if c=0 then [] else f.map fun t => ((k+t.1.1,t.1.2),c*t.2)

def diff (a b : Form) : Form := plus a (scaled 0 (-1) b)

theorem singleton_value (k : Key) (c s : ℚ) (A : Nat → ℚ) :
    value s A (singleton k c)=c*s^k.1*A k.2 := by
  unfold singleton; split <;> simp_all [value,valTerm]

theorem const_value (c s : ℚ) (A : Nat → ℚ) (one : A 0=1) : value s A (const c)=c := by
  simp only [const,singleton_value,pow_zero,mul_one,one]

theorem insert_value (k : Key) (c s : ℚ) (A : Nat → ℚ) (f : Form) :
    value s A (insert k c f)=c*s^k.1*A k.2+value s A f := by
  induction f with
  | nil => simp [insert,singleton_value,value]
  | cons t f ih =>
    by_cases key : k=t.1
    · subst k
      by_cases zero : c+t.2=0
      · simp only [insert,ite_true,zero,value,valTerm]
        rw [show c= -t.2 by linarith]; ring
      · simp only [insert,ite_true,zero,ite_false,value,valTerm]; ring
    · simp only [insert,key,ite_false,value,ih]; ring

theorem plus_value (s : ℚ) (A : Nat → ℚ) (a b : Form) :
    value s A (plus a b)=value s A a+value s A b := by
  induction a with
  | nil => simp [plus,value]
  | cons t a ih => simp only [plus,insert_value,value,ih,valTerm]; ring

theorem scaled_value (k : Nat) (c s : ℚ) (A : Nat → ℚ) (f : Form) :
    value s A (scaled k c f)=c*s^k*value s A f := by
  by_cases zero : c=0
  · simp [zero,scaled,value]
  · induction f with
    | nil => simp [scaled,zero,value]
    | cons t f ih =>
      simp only [scaled,zero,ite_false,List.map_cons,value,valTerm,pow_add] at *
      rw [ih]; ring

theorem diff_value (s : ℚ) (A : Nat → ℚ) (a b : Form) :
    value s A (diff a b)=value s A a-value s A b := by
  simp [diff,plus_value,scaled_value,sub_eq_add_neg]

/-- Syntactic equality after cancelling terms with the same register and scale power. -/
def same (a b : Form) : Bool := (diff a b).isEmpty

theorem same_value {a b : Form} (pass : same a b=true) (s : ℚ) (A : Nat → ℚ) :
    value s A a=value s A b := by
  have nil : diff a b=[] := List.isEmpty_iff.mp pass
  have h := diff_value s A a b
  rw [nil,value] at h; linarith

def cap : ℚ := 1/65

def dropPower (k : Nat) (f : Form) : Form :=
  f.map fun t => ((t.1.1-k,t.1.2),t.2)

def divides (k : Nat) (f : Form) := f.all fun t => decide (k≤t.1.1)

theorem factored {k : Nat} {f : Form} (pass : divides k f=true) (s : ℚ) (A : Nat → ℚ) :
    value s A f=s^k*value s A (dropPower k f) := by
  induction f with
  | nil => simp [dropPower,value]
  | cons t f ih =>
    have ck : k≤t.1.1 ∧ divides k f=true := by
      simpa only [divides,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] using pass
    have step := ih ck.2
    have pow : s^t.1.1=s^k*s^(t.1.1-k) := by rw [←pow_add,Nat.add_sub_of_le ck.1]
    simp only [dropPower,List.map_cons,value,valTerm] at ⊢ step
    rw [pow,step]; ring

def boxTerm (bounds : Nat → Box) (t : Term) : Box :=
  let b := bounds t.1.2
  let l := min (t.2*b.lo) (t.2*b.hi)
  let h := max (t.2*b.lo) (t.2*b.hi)
  if t.1.1=0 then ⟨l,h⟩ else
    ⟨min 0 (l*cap^t.1.1),max 0 (h*cap^t.1.1)⟩

def boxForm (bounds : Nat → Box) : Form → Box
  | [] => ⟨0,0⟩
  | t::f =>
    let a := boxTerm bounds t
    let b := boxForm bounds f
    ⟨a.lo+b.lo,a.hi+b.hi⟩

def Bounds (B : Nat → Box) (A : Nat → ℚ) : Prop := ∀ i,(B i).lo≤A i ∧ A i≤(B i).hi

private theorem bounded_mul {c a l h : ℚ} (hl : l≤a) (hh : a≤h) :
    min (c*l) (c*h) ≤ c*a ∧ c*a ≤ max (c*l) (c*h) := by
  rcases le_total 0 c with hp|hn
  · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_left hl hp),
      (mul_le_mul_of_nonneg_left hh hp).trans (le_max_right ..)⟩
  · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hh hn),
      (mul_le_mul_of_nonpos_left hl hn).trans (le_max_left ..)⟩

theorem term_bound {B A} (encl : Bounds B A) {s : ℚ} (hs : 0≤s) (hu : s≤cap) (t : Term) :
    (boxTerm B t).lo≤valTerm s A t ∧ valTerm s A t≤(boxTerm B t).hi := by
  let c := t.2
  let l := min (c*(B t.1.2).lo) (c*(B t.1.2).hi)
  let h := max (c*(B t.1.2).lo) (c*(B t.1.2).hi)
  have ch : l≤c*A t.1.2 ∧ c*A t.1.2≤h := bounded_mul (encl _).1 (encl _).2
  by_cases zero : t.1.1=0
  · simpa only [boxTerm,zero,ite_true,valTerm,pow_zero,mul_one,l,h,c] using ch
  · let m := s^t.1.1
    let M := cap^t.1.1
    have lm : 0≤m := pow_nonneg hs _
    have um : m≤M := pow_le_pow_left₀ hs hu _
    have left := (bounded_mul (c:=l) lm um).1
    have right := (bounded_mul (c:=h) lm um).2
    simp only [mul_zero] at left right
    simp only [boxTerm,zero,ite_false,valTerm]
    rw [mul_right_comm]
    exact ⟨left.trans (mul_le_mul_of_nonneg_right ch.1 lm),
      (mul_le_mul_of_nonneg_right ch.2 lm).trans right⟩

theorem form_bound {B A} (encl : Bounds B A) {s : ℚ} (hs : 0≤s) (hu : s≤cap) (f : Form) :
    (boxForm B f).lo≤value s A f ∧ value s A f≤(boxForm B f).hi := by
  induction f with
  | nil => exact ⟨le_refl _,le_refl _⟩
  | cons t f ih =>
    have v := term_bound encl hs hu t
    exact ⟨add_le_add v.1 ih.1,add_le_add v.2 ih.2⟩

def nonneg (B : Nat → Box) (f : Form) (k : Nat) :=
  divides k f && decide (0≤(boxForm B (dropPower k f)).lo)

def positive (B : Nat → Box) (f : Form) (k : Nat) :=
  divides k f && decide (0<(boxForm B (dropPower k f)).lo)

theorem nonneg_value {B A} (encl : Bounds B A) {s : ℚ} (hs : 0<s) (hu : s≤cap) {f : Form} {k : Nat}
    (pass : nonneg B f k=true) : 0≤value s A f := by
  have h : divides k f=true ∧ 0≤(boxForm B (dropPower k f)).lo := by
    simpa only [nonneg,Bool.and_eq_true,decide_eq_true_eq] using pass
  rw [factored h.1]
  exact mul_nonneg (pow_nonneg hs.le _) (h.2.trans (form_bound encl hs.le hu _).1)

theorem positive_value {B A} (encl : Bounds B A) {s : ℚ} (hs : 0<s) (hu : s≤cap) {f : Form} {k : Nat}
    (pass : positive B f k=true) : 0<value s A f := by
  have h : divides k f=true ∧ 0<(boxForm B (dropPower k f)).lo := by
    simpa only [positive,Bool.and_eq_true,decide_eq_true_eq] using pass
  rw [factored h.1]
  exact mul_pos (pow_pos hs _) (h.2.trans_le (form_bound encl hs.le hu _).1)

end ArtGallery.Orthogonal.BoundaryPoint.RegisterForm
end
