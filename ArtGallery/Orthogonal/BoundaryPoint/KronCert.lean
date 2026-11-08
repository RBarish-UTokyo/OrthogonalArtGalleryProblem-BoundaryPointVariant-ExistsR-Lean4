module

public import ArtGallery.Geometry.Det
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Polynomial identities from one integer evaluation

Dense integer polynomials in one, two or three variables are nested coefficient
lists. Evaluation in any commutative ring respects addition and multiplication.
If a polynomial has coefficient norm below half of a base `B` and degrees below
the strides, its value at the Kronecker point `(B^(U*T), B^U, B)` determines all
coefficients. A single integer computation therefore proves a polynomial identity
at every real point.

Large polynomials are written sparse and packed (`SP`): the terms are fixed-width
fields of one numeral, and their Kronecker value with base `2^W` is assembled by
shifts, balanced so that every intermediate integer is only as long as the exponent
span of its terms. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.KronCert

abbrev P1 := List Int
abbrev P2 := List P1
abbrev P3 := List P2

section Ops
def add1 : P1 → P1 → P1
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::add1 p q
def neg1 (p : P1) : P1 := p.map (fun a => -a)
def smul1 (a : Int) (p : P1) : P1 := p.map (fun b => a*b)
def mul1 : P1 → P1 → P1
  | [],_ => []
  | a::p,q => add1 (smul1 a q) (0::mul1 p q)

def add2 : P2 → P2 → P2
  | [],q => q
  | p,[] => p
  | a::p,b::q => add1 a b::add2 p q
def neg2 (p : P2) : P2 := p.map neg1
def smul2 (a : P1) (p : P2) : P2 := p.map (mul1 a)
def mul2 : P2 → P2 → P2
  | [],_ => []
  | a::p,q => add2 (smul2 a q) ([]::mul2 p q)

def add3 : P3 → P3 → P3
  | [],q => q
  | p,[] => p
  | a::p,b::q => add2 a b::add3 p q
def neg3 (p : P3) : P3 := p.map neg2
def smul3 (a : P2) (p : P3) : P3 := p.map (mul2 a)
def mul3 : P3 → P3 → P3
  | [],_ => []
  | a::p,q => add3 (smul3 a q) ([]::mul3 p q)
def sub3 (p q : P3) : P3 := add3 p (neg3 q)
end Ops

section Eval
variable {α : Type} [CommRing α]

def ev1 (z : α) : P1 → α
  | [] => 0
  | c::p => (c:α)+z*ev1 z p
def ev2 (y z : α) : P2 → α
  | [] => 0
  | c::p => ev1 z c+y*ev2 y z p
def ev3 (x y z : α) : P3 → α
  | [] => 0
  | c::p => ev2 y z c+x*ev3 x y z p

theorem ev1_add (z : α) : ∀ p q : P1, ev1 z (add1 p q)=ev1 z p+ev1 z q
  | [],q => by simp [add1,ev1]
  | a::p,[] => by simp [add1,ev1]
  | a::p,b::q => by simp only [add1,ev1,ev1_add z p q]; push_cast; ring

theorem ev1_neg (z : α) : ∀ p : P1, ev1 z (neg1 p)= -ev1 z p
  | [] => by simp [neg1,ev1]
  | a::p => by
    have := ev1_neg z p
    simp only [neg1,List.map_cons,ev1] at this ⊢; rw [this]; push_cast; ring

theorem ev1_smul (z : α) (a : Int) : ∀ p : P1, ev1 z (smul1 a p)=(a:α)*ev1 z p
  | [] => by simp [smul1,ev1]
  | b::p => by
    have := ev1_smul z a p
    simp only [smul1,List.map_cons,ev1] at this ⊢; rw [this]; push_cast; ring

theorem ev1_mul (z : α) : ∀ p q : P1, ev1 z (mul1 p q)=ev1 z p*ev1 z q
  | [],q => by simp [mul1,ev1]
  | a::p,q => by
    simp only [mul1,ev1_add,ev1_smul,ev1,ev1_mul z p q]; push_cast; ring

theorem ev2_add (y z : α) : ∀ p q : P2, ev2 y z (add2 p q)=ev2 y z p+ev2 y z q
  | [],q => by simp [add2,ev2]
  | a::p,[] => by simp [add2,ev2]
  | a::p,b::q => by simp only [add2,ev2,ev2_add y z p q,ev1_add]; ring

theorem ev2_neg (y z : α) : ∀ p : P2, ev2 y z (neg2 p)= -ev2 y z p
  | [] => by simp [neg2,ev2]
  | a::p => by
    have := ev2_neg y z p
    simp only [neg2,List.map_cons,ev2] at this ⊢; rw [this,ev1_neg]; ring

theorem ev2_smul (y z : α) (a : P1) : ∀ p : P2, ev2 y z (smul2 a p)=ev1 z a*ev2 y z p
  | [] => by simp [smul2,ev2]
  | b::p => by
    have := ev2_smul y z a p
    simp only [smul2,List.map_cons,ev2] at this ⊢; rw [this,ev1_mul]; ring

theorem ev2_mul (y z : α) : ∀ p q : P2, ev2 y z (mul2 p q)=ev2 y z p*ev2 y z q
  | [],q => by simp [mul2,ev2]
  | a::p,q => by
    simp only [mul2,ev2_add,ev2_smul,ev2,ev2_mul y z p q,ev1]; ring

theorem ev3_add (x y z : α) : ∀ p q : P3, ev3 x y z (add3 p q)=ev3 x y z p+ev3 x y z q
  | [],q => by simp [add3,ev3]
  | a::p,[] => by simp [add3,ev3]
  | a::p,b::q => by simp only [add3,ev3,ev3_add x y z p q,ev2_add]; ring

theorem ev3_neg (x y z : α) : ∀ p : P3, ev3 x y z (neg3 p)= -ev3 x y z p
  | [] => by simp [neg3,ev3]
  | a::p => by
    have := ev3_neg x y z p
    simp only [neg3,List.map_cons,ev3] at this ⊢; rw [this,ev2_neg]; ring

theorem ev3_smul (x y z : α) (a : P2) : ∀ p : P3, ev3 x y z (smul3 a p)=ev2 y z a*ev3 x y z p
  | [] => by simp [smul3,ev3]
  | b::p => by
    have := ev3_smul x y z a p
    simp only [smul3,List.map_cons,ev3] at this ⊢; rw [this,ev2_mul]; ring

theorem ev3_mul (x y z : α) : ∀ p q : P3, ev3 x y z (mul3 p q)=ev3 x y z p*ev3 x y z q
  | [],q => by simp [mul3,ev3]
  | a::p,q => by
    simp only [mul3,ev3_add,ev3_smul,ev3,ev3_mul x y z p q,ev2]; ring

theorem ev3_sub (x y z : α) (p q : P3) : ev3 x y z (sub3 p q)=ev3 x y z p-ev3 x y z q := by
  rw [sub3,ev3_add,ev3_neg]; ring

theorem ev1_cast (z : Int) (p : P1) : ((ev1 z p : Int) : ℝ)=ev1 (z:ℝ) p := by
  induction p with
  | nil => simp [ev1]
  | cons a p ih => simp only [ev1]; push_cast; rw [ih]

theorem ev2_cast (y z : Int) (p : P2) : ((ev2 y z p : Int) : ℝ)=ev2 (y:ℝ) (z:ℝ) p := by
  induction p with
  | nil => simp [ev2]
  | cons a p ih => simp only [ev2]; push_cast; rw [ih,ev1_cast]

theorem ev3_cast (x y z : Int) (p : P3) : ((ev3 x y z p : Int) : ℝ)=ev3 (x:ℝ) (y:ℝ) (z:ℝ) p := by
  induction p with
  | nil => simp [ev3]
  | cons a p ih => simp only [ev3]; push_cast; rw [ih,ev2_cast]
end Eval

section Norm
/-- Coefficient norms and degree bounds. -/
def l1 (p : P1) : Nat := (p.map Int.natAbs).sum
def l2 (p : P2) : Nat := (p.map l1).sum
def l3 (p : P3) : Nat := (p.map l2).sum

/-- All inner lists have length at most `n`. -/
def wide2 (n : Nat) (p : P2) : Bool := p.all (fun c => decide (c.length≤n))
def wide3 (t u : Nat) (p : P3) : Bool := p.all (fun c => decide (c.length≤t) && wide2 u c)
end Norm

section Unique

private theorem l1_cons (a : Int) (p : P1) : (l1 (a::p):Int)=(a.natAbs:Int)+l1 p := by simp [l1]
private theorem l2_cons (a : P1) (p : P2) : (l2 (a::p):Int)=(l1 a:Int)+l2 p := by simp [l2]
private theorem l3_cons (a : P2) (p : P3) : (l3 (a::p):Int)=(l2 a:Int)+l3 p := by simp [l3]

/-- A multiple of `M` of absolute value below `M/2` is zero. -/
private theorem small_multiple {M x : Int} (hM : 0<M) (dvd : M∣x) (h : 2*|x|<M) : x=0 := by
  obtain ⟨k,rfl⟩ := dvd
  rcases lt_trichotomy k 0 with hk|hk|hk
  · exfalso; rw [abs_mul,abs_of_pos hM,abs_of_neg hk] at h; nlinarith
  · rw [hk]; ring
  · exfalso; rw [abs_mul,abs_of_pos hM,abs_of_pos hk] at h; nlinarith

theorem bound1 {B : Int} (hB : 1≤B) : ∀ p : P1, 2*(l1 p:Int)<B → 2*|ev1 B p|<B^p.length
  | [],_ => by simp [ev1]
  | a::p,h => by
    have ih := bound1 hB p (by have := l1_cons a p; have : (0:Int)≤a.natAbs := (by positivity); omega)
    simp only [ev1,List.length_cons,pow_succ,Int.cast_id]
    have ha : 2*|a|<B := by have := l1_cons a p; rw [Int.abs_eq_natAbs]; have : (0:Int)≤l1 p := (by positivity); omega
    have tri : |a+B*ev1 B p|≤|a|+B*|ev1 B p| := by
      calc |a+B*ev1 B p|≤|a|+|B*ev1 B p| := abs_add_le _ _
        _=|a|+B*|ev1 B p| := by rw [abs_mul,abs_of_pos (show (0:Int)<B by omega)]
    have ih' : 2*|ev1 B p|≤B^p.length-1 := by omega
    have m := mul_le_mul_of_nonneg_left ih' (show (0:Int)≤B by omega)
    nlinarith

theorem zero1 {B : Int} (hB : 1≤B) : ∀ p : P1, 2*(l1 p:Int)<B → ev1 B p=0 → ∀ (z : ℝ), ev1 z p=0
  | [],_,_,z => by simp [ev1]
  | a::p,hl,he,z => by
    have hl' : 2*(l1 p:Int)<B := by have := l1_cons a p; have : (0:Int)≤a.natAbs := (by positivity); omega
    simp only [ev1,Int.cast_id] at he
    simp only [ev1]
    have ha : a=0 := by
      apply small_multiple (M:=B) (by omega) ⟨-ev1 B p,by linarith⟩
      have := l1_cons a p; rw [Int.abs_eq_natAbs]; have : (0:Int)≤l1 p := (by positivity); omega
    subst ha
    have hp : ev1 B p=0 := by
      have : B*ev1 B p=0 := by simpa using he
      rcases mul_eq_zero.mp this with h|h
      · omega
      · exact h
    rw [zero1 hB p hl' hp z]; simp

theorem bound2 {B : Int} (hB : 1≤B) (U : Nat) : ∀ p : P2, 2*(l2 p:Int)<B → wide2 U p=true →
    2*|ev2 (B^U) B p|<(B^U)^p.length
  | [],_,_ => by simp [ev2]
  | a::p,h,w => by
    simp only [wide2,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at w
    have hp : 2*(l2 p:Int)<B := by have := l2_cons a p; have : (0:Int)≤l1 a := (by positivity); omega
    have ha : 2*(l1 a:Int)<B := by have := l2_cons a p; have : (0:Int)≤l2 p := (by positivity); omega
    have ih := bound2 hB U p hp (by simpa [wide2] using w.2)
    have ba := bound1 hB a ha
    have mono : B^a.length≤B^U := pow_le_pow_right₀ hB w.1
    simp only [ev2,List.length_cons,pow_succ]
    have Y : 1≤B^U := one_le_pow₀ hB
    have tri : |ev1 B a+B^U*ev2 (B^U) B p|≤|ev1 B a|+B^U*|ev2 (B^U) B p| := by
      calc _≤|ev1 B a|+|B^U*ev2 (B^U) B p| := abs_add_le _ _
        _=_ := by rw [abs_mul,abs_of_pos (show (0:Int)<B^U by omega)]
    have ih' : 2*|ev2 (B^U) B p|≤(B^U)^p.length-1 := by omega
    have m := mul_le_mul_of_nonneg_left ih' (show (0:Int)≤B^U by omega)
    have ba' : 2*|ev1 B a|≤B^U-1 := by omega
    nlinarith

theorem zero2 {B : Int} (hB : 1≤B) (U : Nat) : ∀ p : P2, 2*(l2 p:Int)<B → wide2 U p=true →
    ev2 (B^U) B p=0 → ∀ (y z : ℝ), ev2 y z p=0
  | [],_,_,_,y,z => by simp [ev2]
  | a::p,h,w,he,y,z => by
    simp only [wide2,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at w
    have hp : 2*(l2 p:Int)<B := by have := l2_cons a p; have : (0:Int)≤l1 a := (by positivity); omega
    have ha : 2*(l1 a:Int)<B := by have := l2_cons a p; have : (0:Int)≤l2 p := (by positivity); omega
    simp only [ev2] at he ⊢
    have Y : 1≤B^U := one_le_pow₀ hB
    have ea : ev1 B a=0 := by
      apply small_multiple (M:=B^U) (by omega) ⟨-ev2 (B^U) B p,by linarith⟩
      exact lt_of_lt_of_le (bound1 hB a ha) (pow_le_pow_right₀ hB w.1)
    have ep : ev2 (B^U) B p=0 := by
      have : B^U*ev2 (B^U) B p=0 := by rw [ea] at he; simpa using he
      rcases mul_eq_zero.mp this with h|h
      · omega
      · exact h
    rw [zero1 hB a ha ea z,zero2 hB U p hp (by simpa [wide2] using w.2) ep y z]; ring

theorem zero3 {B : Int} (hB : 1≤B) (T U : Nat) : ∀ p : P3, 2*(l3 p:Int)<B → wide3 T U p=true →
    ev3 ((B^U)^T) (B^U) B p=0 → ∀ (x y z : ℝ), ev3 x y z p=0
  | [],_,_,_,x,y,z => by simp [ev3]
  | a::p,h,w,he,x,y,z => by
    simp only [wide3,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at w
    have hp : 2*(l3 p:Int)<B := by have := l3_cons a p; have : (0:Int)≤l2 a := (by positivity); omega
    have ha : 2*(l2 a:Int)<B := by have := l3_cons a p; have : (0:Int)≤l3 p := (by positivity); omega
    simp only [ev3] at he ⊢
    have Y : 1≤(B^U)^T := one_le_pow₀ (one_le_pow₀ hB)
    have ea : ev2 (B^U) B a=0 := by
      apply small_multiple (M:=(B^U)^T) (by omega) ⟨-ev3 ((B^U)^T) (B^U) B p,by linarith⟩
      exact lt_of_lt_of_le (bound2 hB U a ha w.1.2) (pow_le_pow_right₀ (one_le_pow₀ hB) w.1.1)
    have ep : ev3 ((B^U)^T) (B^U) B p=0 := by
      have : (B^U)^T*ev3 ((B^U)^T) (B^U) B p=0 := by rw [ea] at he; simpa using he
      rcases mul_eq_zero.mp this with h|h
      · omega
      · exact h
    rw [zero2 hB U a ha w.1.2 ea y z,zero3 hB T U p hp (by simpa [wide3] using w.2) ep x y z]; ring

end Unique

section Bounds

theorem l1_add : ∀ p q : P1, l1 (add1 p q)≤l1 p+l1 q
  | [],q => by simp [add1,l1]
  | a::p,[] => by simp [add1,l1]
  | a::p,b::q => by
    have := l1_add p q
    simp only [add1,l1,List.map_cons,List.sum_cons] at this ⊢
    have := Int.natAbs_add_le a b; omega

theorem l1_neg (p : P1) : l1 (neg1 p)=l1 p := by
  simp [l1,neg1,Function.comp_def]

theorem l1_smul (a : Int) (p : P1) : l1 (smul1 a p)=a.natAbs*l1 p := by
  induction p with
  | nil => simp [l1,smul1]
  | cons b p ih => simp only [l1,smul1,List.map_cons,List.sum_cons,Int.natAbs_mul] at ih ⊢; rw [ih]; ring

theorem l1_mul : ∀ p q : P1, l1 (mul1 p q)≤l1 p*l1 q
  | [],q => by simp [mul1,l1]
  | a::p,q => by
    have h := l1_mul p q
    have e := l1_add (smul1 a q) (0::mul1 p q)
    simp only [mul1,l1_smul] at e ⊢
    have : l1 (0::mul1 p q)=l1 (mul1 p q) := by simp [l1]
    have c : l1 (a::p)=a.natAbs+l1 p := by simp [l1]
    rw [c]; nlinarith

theorem l2_add : ∀ p q : P2, l2 (add2 p q)≤l2 p+l2 q
  | [],q => by simp [add2,l2]
  | a::p,[] => by simp [add2,l2]
  | a::p,b::q => by
    have := l2_add p q; have := l1_add a b
    simp only [add2,l2,List.map_cons,List.sum_cons] at * ; omega

theorem l2_neg (p : P2) : l2 (neg2 p)=l2 p := by
  induction p with
  | nil => simp [l2,neg2]
  | cons a p ih => simp only [l2,neg2,List.map_cons,List.sum_cons,l1_neg] at ih ⊢; rw [ih]

theorem l2_smul (a : P1) (p : P2) : l2 (smul2 a p)≤l1 a*l2 p := by
  induction p with
  | nil => simp [l2,smul2]
  | cons b p ih =>
    simp only [l2,smul2,List.map_cons,List.sum_cons] at ih ⊢
    have := l1_mul a b; nlinarith

theorem l2_mul : ∀ p q : P2, l2 (mul2 p q)≤l2 p*l2 q
  | [],q => by simp [mul2,l2]
  | a::p,q => by
    have h := l2_mul p q
    have e := l2_add (smul2 a q) ([]::mul2 p q)
    have sm := l2_smul a q
    simp only [mul2] at e ⊢
    have : l2 ([]::mul2 p q)=l2 (mul2 p q) := by simp [l2,l1]
    have c : l2 (a::p)=l1 a+l2 p := by simp [l2]
    rw [c]; nlinarith

theorem l3_add : ∀ p q : P3, l3 (add3 p q)≤l3 p+l3 q
  | [],q => by simp [add3,l3]
  | a::p,[] => by simp [add3,l3]
  | a::p,b::q => by
    have := l3_add p q; have := l2_add a b
    simp only [add3,l3,List.map_cons,List.sum_cons] at * ; omega

theorem l3_neg (p : P3) : l3 (neg3 p)=l3 p := by
  induction p with
  | nil => simp [l3,neg3]
  | cons a p ih => simp only [l3,neg3,List.map_cons,List.sum_cons,l2_neg] at ih ⊢; rw [ih]

theorem l3_smul (a : P2) (p : P3) : l3 (smul3 a p)≤l2 a*l3 p := by
  induction p with
  | nil => simp [l3,smul3]
  | cons b p ih =>
    simp only [l3,smul3,List.map_cons,List.sum_cons] at ih ⊢
    have := l2_mul a b; nlinarith

theorem l3_mul : ∀ p q : P3, l3 (mul3 p q)≤l3 p*l3 q
  | [],q => by simp [mul3,l3]
  | a::p,q => by
    have h := l3_mul p q
    have e := l3_add (smul3 a q) ([]::mul3 p q)
    have sm := l3_smul a q
    simp only [mul3] at e ⊢
    have : l3 ([]::mul3 p q)=l3 (mul3 p q) := by simp [l3,l2]
    have c : l3 (a::p)=l2 a+l3 p := by simp [l3]
    rw [c]; nlinarith

/-! Widths: lengths of the inner coefficient lists. -/
theorem len_add1 : ∀ p q : P1, (add1 p q).length≤max p.length q.length
  | [],q => by simp [add1]
  | a::p,[] => by simp [add1]
  | a::p,b::q => by have := len_add1 p q; simp only [add1,List.length_cons]; omega

theorem len_mul1 : ∀ p q : P1, (mul1 p q).length≤p.length+q.length
  | [],q => by simp [mul1]
  | a::p,q => by
    have h := len_mul1 p q
    have e := len_add1 (smul1 a q) (0::mul1 p q)
    simp only [mul1,smul1,List.length_map,List.length_cons] at e ⊢; omega

theorem wide2_cons {n : Nat} (a : P1) (p : P2) : wide2 n (a::p)=true ↔ a.length≤n ∧ wide2 n p=true := by
  simp [wide2]

theorem wide3_cons {t u : Nat} (a : P2) (p : P3) :
    wide3 t u (a::p)=true ↔ (a.length≤t ∧ wide2 u a=true) ∧ wide3 t u p=true := by
  simp [wide3,wide2]

theorem wide2_add {n : Nat} : ∀ p q : P2, wide2 n p=true → wide2 n q=true → wide2 n (add2 p q)=true
  | [],q,_,h => by simpa [add2] using h
  | a::p,[],h,_ => by simpa [add2] using h
  | a::p,b::q,hp,hq => by
    rw [wide2_cons] at hp hq
    rw [add2,wide2_cons]
    exact ⟨le_trans (len_add1 a b) (max_le hp.1 hq.1),wide2_add p q hp.2 hq.2⟩

theorem wide2_mono {n m : Nat} (h : n≤m) (p : P2) (hp : wide2 n p=true) : wide2 m p=true := by
  simp only [wide2,List.all_eq_true,decide_eq_true_eq] at hp ⊢
  exact fun c hc => le_trans (hp c hc) h

theorem wide2_mul {n m : Nat} : ∀ p q : P2, wide2 n p=true → wide2 m q=true → wide2 (n+m) (mul2 p q)=true
  | [],q,_,_ => by simp [mul2,wide2]
  | a::p,q,hp,hq => by
    rw [wide2_cons] at hp
    have ih := wide2_mul p q hp.2 hq
    have sm : wide2 (n+m) (smul2 a q)=true := by
      simp only [wide2,smul2,List.all_map,List.all_eq_true,Function.comp_apply,decide_eq_true_eq] at hq ⊢
      intro c hc; exact le_trans (len_mul1 a c) (by have := hq c hc; omega)
    rw [mul2]
    apply wide2_add _ _ sm
    rw [wide2_cons]
    exact ⟨Nat.zero_le _,ih⟩

theorem len_add2 : ∀ p q : P2, (add2 p q).length≤max p.length q.length
  | [],q => by simp [add2]
  | a::p,[] => by simp [add2]
  | a::p,b::q => by have := len_add2 p q; simp only [add2,List.length_cons]; omega

theorem len_mul2 : ∀ p q : P2, (mul2 p q).length≤p.length+q.length
  | [],q => by simp [mul2]
  | a::p,q => by
    have h := len_mul2 p q
    have e := len_add2 (smul2 a q) ([]::mul2 p q)
    simp only [mul2,smul2,List.length_map,List.length_cons] at e ⊢; omega

theorem wide3_add {t u : Nat} : ∀ p q : P3, wide3 t u p=true → wide3 t u q=true → wide3 t u (add3 p q)=true
  | [],q,_,h => by simpa [add3] using h
  | a::p,[],h,_ => by simpa [add3] using h
  | a::p,b::q,hp,hq => by
    rw [wide3_cons] at hp hq
    rw [add3,wide3_cons]
    exact ⟨⟨le_trans (len_add2 a b) (max_le hp.1.1 hq.1.1),wide2_add a b hp.1.2 hq.1.2⟩,wide3_add p q hp.2 hq.2⟩

theorem wide3_mul {t u t' u' : Nat} : ∀ p q : P3, wide3 t u p=true → wide3 t' u' q=true →
    wide3 (t+t') (u+u') (mul3 p q)=true
  | [],q,_,_ => by simp [mul3,wide3]
  | a::p,q,hp,hq => by
    rw [wide3_cons] at hp
    have ih := wide3_mul p q hp.2 hq
    have sm : wide3 (t+t') (u+u') (smul3 a q)=true := by
      simp only [wide3,smul3,List.all_map,List.all_eq_true,Function.comp_apply,Bool.and_eq_true,
        decide_eq_true_eq] at hq ⊢
      intro c hc
      exact ⟨le_trans (len_mul2 a c) (by have := (hq c hc).1; omega),wide2_mul a c hp.1.2 (hq c hc).2⟩
    rw [mul3]
    apply wide3_add _ _ sm
    rw [wide3_cons]
    exact ⟨⟨Nat.zero_le _,by simp [wide2]⟩,ih⟩

/-! Tight widths of products: a product of widths `t` and `t'` has width at most
`t - 1 + max t' 1` (one less than the sum when both factors are nonempty). -/
theorem len_mul1' : ∀ p q : P1, (mul1 p q).length≤p.length-1+max q.length 1
  | [],q => by simp [mul1]
  | a::p,q => by
    rw [mul1]
    have e := len_add1 (smul1 a q) (0::mul1 p q)
    have hs : (smul1 a q).length=q.length := by simp [smul1]
    have h := len_mul1' p q
    have hl : (0::mul1 p q).length=(mul1 p q).length+1 := rfl
    have hM1 : q.length≤max q.length 1 := le_max_left _ _
    have hM2 : 1≤max q.length 1 := le_max_right _ _
    generalize max q.length 1=M at *
    rcases p with _|⟨b,p⟩
    · have h0 : (0::mul1 [] q).length=1 := rfl
      refine le_trans e (max_le ?_ ?_)
      · rw [hs]; simp only [List.length_cons,List.length_nil]; omega
      · rw [h0]; simp only [List.length_cons,List.length_nil]; omega
    · simp only [List.length_cons] at h ⊢
      refine le_trans e (max_le ?_ ?_)
      · rw [hs]; omega
      · rw [hl]; omega

theorem len_mul2' : ∀ p q : P2, (mul2 p q).length≤p.length-1+max q.length 1
  | [],q => by simp [mul2]
  | a::p,q => by
    rw [mul2]
    have e := len_add2 (smul2 a q) ([]::mul2 p q)
    have hs : (smul2 a q).length=q.length := by simp [smul2]
    have h := len_mul2' p q
    have hl : ([]::mul2 p q).length=(mul2 p q).length+1 := rfl
    have hM1 : q.length≤max q.length 1 := le_max_left _ _
    have hM2 : 1≤max q.length 1 := le_max_right _ _
    generalize max q.length 1=M at *
    rcases p with _|⟨b,p⟩
    · have h0 : ([]::mul2 [] q).length=1 := rfl
      refine le_trans e (max_le ?_ ?_)
      · rw [hs]; simp only [List.length_cons,List.length_nil]; omega
      · rw [h0]; simp only [List.length_cons,List.length_nil]; omega
    · simp only [List.length_cons] at h ⊢
      refine le_trans e (max_le ?_ ?_)
      · rw [hs]; omega
      · rw [hl]; omega

theorem wide2_mul' {n m : Nat} : ∀ p q : P2, wide2 n p=true → wide2 m q=true →
    wide2 (n-1+max m 1) (mul2 p q)=true
  | [],q,_,_ => by simp [mul2,wide2]
  | a::p,q,hp,hq => by
    rw [wide2_cons] at hp
    have ih := wide2_mul' p q hp.2 hq
    have sm : wide2 (n-1+max m 1) (smul2 a q)=true := by
      simp only [wide2,smul2,List.all_map,List.all_eq_true,Function.comp_apply,decide_eq_true_eq] at hq ⊢
      intro c hc
      have l := len_mul1' a c
      have h1 := hq c hc
      have : max c.length 1≤max m 1 := max_le_max h1 le_rfl
      omega
    rw [mul2]
    apply wide2_add _ _ sm
    rw [wide2_cons]
    exact ⟨Nat.zero_le _,ih⟩

theorem wide3_mul' {t u t' u' : Nat} : ∀ p q : P3, wide3 t u p=true → wide3 t' u' q=true →
    wide3 (t-1+max t' 1) (u-1+max u' 1) (mul3 p q)=true
  | [],q,_,_ => by simp [mul3,wide3]
  | a::p,q,hp,hq => by
    rw [wide3_cons] at hp
    have ih := wide3_mul' p q hp.2 hq
    have sm : wide3 (t-1+max t' 1) (u-1+max u' 1) (smul3 a q)=true := by
      simp only [wide3,smul3,List.all_map,List.all_eq_true,Function.comp_apply,Bool.and_eq_true,
        decide_eq_true_eq] at hq ⊢
      intro c hc
      have l := len_mul2' a c
      have h1 := (hq c hc).1
      have : max c.length 1≤max t' 1 := max_le_max h1 le_rfl
      exact ⟨by have := hp.1.1; omega,wide2_mul' a c hp.1.2 (hq c hc).2⟩
    rw [mul3]
    apply wide3_add _ _ sm
    rw [wide3_cons]
    exact ⟨⟨Nat.zero_le _,by simp [wide2]⟩,ih⟩

theorem wide3_neg {t u : Nat} (p : P3) (h : wide3 t u p=true) : wide3 t u (neg3 p)=true := by
  simp only [wide3,neg3,List.all_map,List.all_eq_true,Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
  intro c hc
  refine ⟨by simpa [neg2] using (h c hc).1,?_⟩
  have := (h c hc).2
  simp only [wide2,neg2,List.all_map,List.all_eq_true,Function.comp_apply,decide_eq_true_eq] at this ⊢
  intro d hd; simpa [neg1] using this d hd

end Bounds

section Sparse

/-! Monomials and sparse packed polynomials. -/
def mono1 (c : Int) : Nat → P1
  | 0 => [c]
  | k+1 => 0::mono1 c k
def mono2 (q : P1) : Nat → P2
  | 0 => [q]
  | j+1 => []::mono2 q j
def mono3 (q : P2) : Nat → P3
  | 0 => [q]
  | i+1 => []::mono3 q i

section
variable {α : Type} [CommRing α]
theorem ev1_mono (z : α) (c : Int) : ∀ k, ev1 z (mono1 c k)=(c:α)*z^k
  | 0 => by simp [mono1,ev1]
  | k+1 => by simp only [mono1,ev1,ev1_mono z c k]; push_cast; ring
theorem ev2_mono (y z : α) (q : P1) : ∀ j, ev2 y z (mono2 q j)=ev1 z q*y^j
  | 0 => by simp [mono2,ev2]
  | j+1 => by simp only [mono2,ev2,ev2_mono y z q j,ev1]; ring
theorem ev3_mono (x y z : α) (q : P2) : ∀ i, ev3 x y z (mono3 q i)=ev2 y z q*x^i
  | 0 => by simp [mono3,ev3]
  | i+1 => by simp only [mono3,ev3,ev3_mono x y z q i,ev2]; ring
end

theorem l1_mono (c : Int) : ∀ k, l1 (mono1 c k)=c.natAbs
  | 0 => by simp [mono1,l1]
  | k+1 => by have := l1_mono c k; simp only [l1] at this ⊢; simpa [mono1] using this
theorem l2_mono (q : P1) : ∀ j, l2 (mono2 q j)=l1 q
  | 0 => by simp [mono2,l2]
  | j+1 => by have := l2_mono q j; simp only [l2] at this ⊢; simpa [mono2,l1] using this
theorem l3_mono (q : P2) : ∀ i, l3 (mono3 q i)=l2 q
  | 0 => by simp [mono3,l3]
  | i+1 => by have := l3_mono q i; simp only [l3] at this ⊢; simpa [mono3,l2] using this

theorem len_mono1 (c : Int) : ∀ k, (mono1 c k).length=k+1
  | 0 => rfl
  | k+1 => by simp [mono1,len_mono1 c k]
theorem len_mono2 (q : P1) : ∀ j, (mono2 q j).length=j+1
  | 0 => rfl
  | j+1 => by simp [mono2,len_mono2 q j]
theorem wide2_mono2 {u : Nat} (q : P1) (hq : q.length≤u) : ∀ j, wide2 u (mono2 q j)=true
  | 0 => by simp [mono2,wide2,hq]
  | j+1 => by rw [mono2,wide2_cons]; exact ⟨Nat.zero_le _,wide2_mono2 q hq j⟩
theorem wide3_mono3 {t u : Nat} (q : P2) (hq : q.length≤t) (hw : wide2 u q=true) : ∀ i, wide3 t u (mono3 q i)=true
  | 0 => by rw [mono3,wide3_cons]; exact ⟨⟨hq,hw⟩,rfl⟩
  | i+1 => by rw [mono3,wide3_cons]; exact ⟨⟨Nat.zero_le _,rfl⟩,wide3_mono3 q hq hw i⟩

/-- A sparse packed polynomial: blocks of terms, each block `n` terms of `w+25` bits, low bits
first. A term `t` holds the `x`-degree (8 bits), the `y`-degree (8 bits, read modulo `J+1`), the
`z`-degree (8 bits, read modulo `K+1`), a sign bit and a `w`-bit magnitude. -/
structure SP where
  J : Nat
  K : Nat
  /-- Blocks `(w, n, d)`: `n` terms of `w+25` bits in the numeral `d`. -/
  bs : List (Nat × Nat × Nat)
deriving DecidableEq

/-- The data numeral from chunks of `C` bits, least significant chunk first. -/
def SP.join (C : Nat) : List Nat → Nat
  | [] => 0
  | c::cs => c|||(SP.join C cs<<<C)

namespace SP
def fi (t : Nat) : Nat := t%256
def fj (J t : Nat) : Nat := (t>>>8)%256%(J+1)
def fk (K t : Nat) : Nat := (t>>>16)%256%(K+1)
def fc (t : Nat) : Int := if (t>>>24)%2=1 then -((t>>>25:Nat):Int) else ((t>>>25:Nat):Int)
def term (J K t : Nat) : P3 := mono3 (mono2 (mono1 (fc t) (fk K t)) (fj J t)) (fi t)

def polyGo (w J K : Nat) : Nat → Nat → P3
  | 0,_ => []
  | n+1,d => add3 (term J K (d&&&(2^(w+25)-1))) (polyGo w J K n (d>>>(w+25)))

/-- The polynomial of the packed blocks (used in proofs only). -/
def polyB (J K : Nat) : List (Nat × Nat × Nat) → P3
  | [] => []
  | b::bs => add3 (polyGo b.1 J K b.2.1 b.2.2) (polyB J K bs)

def poly (s : SP) : P3 := polyB s.J s.K s.bs

/-- The value of a term at the Kronecker point with base `2^W` and strides `T`, `U`. -/
def tval (W T U J K t : Nat) : Int :=
  if (t>>>24)%2=1 then -(((t>>>25)<<<(W*(U*T*fi t+U*fj J t+fk K t)):Nat):Int)
  else (((t>>>25)<<<(W*(U*T*fi t+U*fj J t+fk K t)):Nat):Int)

def kronGo (w J K W T U : Nat) : Nat → Nat → Int
  | 0,_ => 0
  | n+1,d => tval W T U J K (d&&&(2^(w+25)-1))+kronGo w J K W T U n (d>>>(w+25))

theorem tval_eq (W T U J K t : Nat) :
    tval W T U J K t=ev3 ((((2:Int)^W)^U)^T) (((2:Int)^W)^U) ((2:Int)^W) (term J K t) := by
  have e : ((2:Int)^(W*(U*T*fi t+U*fj J t+fk K t)))=
      ((2:Int)^W)^fk K t*(((2:Int)^W)^U)^fj J t*((((2:Int)^W)^U)^T)^fi t := by
    rw [show W*(U*T*fi t+U*fj J t+fk K t)=W*fk K t+W*U*fj J t+W*U*T*fi t by ring]
    simp only [pow_add,pow_mul]
  simp only [tval,term,ev3_mono,ev2_mono,ev1_mono,fc,Int.cast_id,Nat.shiftLeft_eq]
  split <;> push_cast <;> rw [e] <;> ring

theorem kronGo_eq (w J K W T U : Nat) : ∀ n d,
    kronGo w J K W T U n d=ev3 ((((2:Int)^W)^U)^T) (((2:Int)^W)^U) ((2:Int)^W) (polyGo w J K n d)
  | 0,_ => by simp [kronGo,polyGo,ev3]
  | n+1,d => by rw [kronGo,polyGo,ev3_add,tval_eq,kronGo_eq]

/-! Divide and conquer: each node holds its value relative to its least exponent, so the
intermediate integers of a node are only as long as its exponent span. -/
def eOf (T U J K t : Nat) : Nat := U*T*fi t+U*fj J t+fk K t

/-- `v*2^s` with a shift. -/
def ishl : Int → Nat → Int
  | .ofNat a,s => .ofNat (a<<<s)
  | .negSucc a,s => -(((a+1)<<<s:Nat):Int)

theorem ishl_eq (v : Int) (s : Nat) : ishl v s=v*2^s := by
  cases v with
  | ofNat a => simp only [ishl,Nat.shiftLeft_eq]; rfl
  | negSucc a => simp only [ishl,Nat.shiftLeft_eq,Int.negSucc_eq]; push_cast; ring

/-- Positive and negative magnitude of a term. -/
def pm (t : Nat) : Nat := if (t>>>24)%2=1 then 0 else t>>>25
def nm (t : Nat) : Nat := if (t>>>24)%2=1 then t>>>25 else 0

theorem fc_pm (t : Nat) : fc t=(pm t:Int)-(nm t:Int) := by
  unfold fc pm nm; split <;> simp

/-- Nodes carry their least exponent and the positive and negative parts relative to it. -/
def combine (W : Nat) (L R : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (min L.1 R.1,(L.2.1<<<(W*(L.1-min L.1 R.1)))+(R.2.1<<<(W*(R.1-min L.1 R.1))),
    (L.2.2<<<(W*(L.1-min L.1 R.1)))+(R.2.2<<<(W*(R.1-min L.1 R.1))))

def dcGo (w J K W T U : Nat) : Nat → Nat → Nat → Nat × Nat × Nat
  | _,0,_ => (0,0,0)
  | _,1,d => (eOf T U J K (d&&&(2^(w+25)-1)),pm (d&&&(2^(w+25)-1)),nm (d&&&(2^(w+25)-1)))
  | 0,n+2,d => (0,(kronGo w J K W T U (n+2) d).toNat,(-kronGo w J K W T U (n+2) d).toNat)
  | f+1,n+2,d => combine W (dcGo w J K W T U f ((n+2)/2) d)
      (dcGo w J K W T U f (n+2-(n+2)/2) (d>>>((w+25)*((n+2)/2))))

/-- The Kronecker value of a packed polynomial. -/
def kronDC (w J K W T U n d : Nat) : Int :=
  (((dcGo w J K W T U 64 n d).2.1<<<(W*(dcGo w J K W T U 64 n d).1):Nat):Int)-
    (((dcGo w J K W T U 64 n d).2.2<<<(W*(dcGo w J K W T U 64 n d).1):Nat):Int)

theorem tval_fc (W T U J K t : Nat) : tval W T U J K t=fc t*2^(W*eOf T U J K t) := by
  unfold tval fc eOf; split <;> simp only [Nat.shiftLeft_eq] <;> push_cast <;> ring

theorem kronGo_add (w J K W T U : Nat) : ∀ a b d,
    kronGo w J K W T U (a+b) d=kronGo w J K W T U a d+kronGo w J K W T U b (d>>>((w+25)*a))
  | 0,b,d => by simp [kronGo]
  | a+1,b,d => by
    rw [show a+1+b=(a+b)+1 by omega,kronGo,kronGo,kronGo_add w J K W T U a b,← Nat.shiftRight_add,
      show w+25+(w+25)*a=(w+25)*(a+1) by ring]; ring

theorem dcGo_eq (w J K W T U : Nat) : ∀ f n d,
    (((dcGo w J K W T U f n d).2.1:Int)-(dcGo w J K W T U f n d).2.2)*2^(W*(dcGo w J K W T U f n d).1)=
      kronGo w J K W T U n d
  | _,0,_ => by simp [dcGo,kronGo]
  | f,1,d => by
    cases f <;> simp only [dcGo,kronGo,tval_fc,add_zero,fc_pm]
  | 0,n+2,d => by simp only [dcGo]; rw [Int.toNat_sub_toNat_neg]; simp
  | f+1,n+2,d => by
    have hL := dcGo_eq w J K W T U f ((n+2)/2) d
    have hR := dcGo_eq w J K W T U f (n+2-(n+2)/2) (d>>>((w+25)*((n+2)/2)))
    rw [dcGo,show n+2=(n+2)/2+(n+2-(n+2)/2) by omega,kronGo_add,← hL,← hR]
    rw [show (n+2)/2+(n+2-(n+2)/2)-((n+2)/2+(n+2-(n+2)/2))/2=n+2-(n+2)/2 by omega,
      show ((n+2)/2+(n+2-(n+2)/2))/2=(n+2)/2 by omega]
    unfold combine
    generalize dcGo w J K W T U f ((n+2)/2) d=L
    generalize dcGo w J K W T U f (n+2-(n+2)/2) (d>>>((w+25)*((n+2)/2)))=R
    obtain ⟨e1,p1,q1⟩ := L; obtain ⟨e2,p2,q2⟩ := R
    simp only [Nat.shiftLeft_eq]; push_cast
    have h1 : (2:Int)^(W*e1)=2^(W*(e1-min e1 e2))*2^(W*min e1 e2) := by
      rw [← pow_add,← Nat.mul_add]; congr 2; omega
    have h2 : (2:Int)^(W*e2)=2^(W*(e2-min e1 e2))*2^(W*min e1 e2) := by
      rw [← pow_add,← Nat.mul_add]; congr 2; omega
    rw [h1,h2]; ring

theorem kronDC_eq (w J K W T U n d : Nat) : kronDC w J K W T U n d=kronGo w J K W T U n d := by
  rw [kronDC,← dcGo_eq w J K W T U 64]; simp only [Nat.shiftLeft_eq]; push_cast; ring

/-! The same balanced evaluation written with the kernel's native `Nat` operations and an explicit
recursor: the kernel then spends a few reduction steps per term instead of unfolding notation
instances and structural-recursion encodings (about three times faster on large forms). -/
def eOfN (T U J K t : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (Nat.mul U T) (Nat.mod t 256))
    (Nat.mul U (Nat.mod (Nat.mod (Nat.shiftRight t 8) 256) (Nat.succ J))))
    (Nat.mod (Nat.mod (Nat.shiftRight t 16) 256) (Nat.succ K))

def leafF (J K T U t : Nat) : Nat × Nat × Nat :=
  bif Nat.beq (Nat.mod (Nat.shiftRight t 24) 2) 1 then (eOfN T U J K t,0,Nat.shiftRight t 25)
  else (eOfN T U J K t,Nat.shiftRight t 25,0)

def combF (W : Nat) (L R : Nat × Nat × Nat) : Nat × Nat × Nat :=
  bif Nat.ble L.1 R.1 then
    (L.1,Nat.add L.2.1 (Nat.shiftLeft R.2.1 (Nat.mul W (Nat.sub R.1 L.1))),
      Nat.add L.2.2 (Nat.shiftLeft R.2.2 (Nat.mul W (Nat.sub R.1 L.1))))
  else
    (R.1,Nat.add R.2.1 (Nat.shiftLeft L.2.1 (Nat.mul W (Nat.sub L.1 R.1))),
      Nat.add R.2.2 (Nat.shiftLeft L.2.2 (Nat.mul W (Nat.sub L.1 R.1))))

/-- The step of `dcF`: split `n` packed terms in halves and combine. -/
def dcStep (w J K W T U : Nat) (ih : Nat → Nat → Nat × Nat × Nat) (n d : Nat) : Nat × Nat × Nat :=
  bif Nat.ble n 1 then
    (bif Nat.beq n 0 then (0,0,0) else leafF J K T U (Nat.land d (Nat.sub (Nat.pow 2 (Nat.add w 25)) 1)))
  else combF W (ih (Nat.div n 2) d) (ih (Nat.sub n (Nat.div n 2)) (Nat.shiftRight d (Nat.mul (Nat.add w 25) (Nat.div n 2))))

@[implemented_by dcGo]
def dcF (w J K W T U f : Nat) : Nat → Nat → Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat × Nat) (fun n d => dcGo w J K W T U 0 n d)
    (fun _ ih n d => dcStep w J K W T U ih n d) f

theorem eOfN_eq (T U J K t : Nat) : eOfN T U J K t=eOf T U J K t := rfl

theorem leafF_eq (J K T U t : Nat) : leafF J K T U t=(eOf T U J K t,pm t,nm t) := by
  unfold leafF pm nm
  rw [eOfN_eq]
  by_cases h : (t>>>24)%2=1
  · have : Nat.beq (Nat.mod (Nat.shiftRight t 24) 2) 1=true := Nat.beq_eq_true_eq _ _ ▸ h
    simp only [this,Bool.cond_true,h,ite_true]; rfl
  · have : Nat.beq (Nat.mod (Nat.shiftRight t 24) 2) 1=false := by
      cases e : Nat.beq (Nat.mod (Nat.shiftRight t 24) 2) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    simp only [this,Bool.cond_false,h,ite_false]; rfl

theorem combF_eq (W : Nat) (L R : Nat × Nat × Nat) : combF W L R=combine W L R := by
  obtain ⟨e1,p1,q1⟩ := L; obtain ⟨e2,p2,q2⟩ := R
  unfold combF combine
  by_cases h : e1≤e2
  · have hb : Nat.ble e1 e2=true := Nat.ble_eq.mpr h
    simp only [hb,Bool.cond_true,Nat.min_eq_left h,Nat.sub_self,Nat.mul_zero,Nat.shiftLeft_zero]; rfl
  · have hb : Nat.ble e1 e2=false := by
      cases e : Nat.ble e1 e2
      · rfl
      · exact absurd (Nat.ble_eq.mp e) h
    have hm : min e1 e2=e2 := Nat.min_eq_right (by omega)
    simp only [hb,Bool.cond_false,hm,Nat.sub_self,Nat.mul_zero,Nat.shiftLeft_zero]
    show (e2,_,_)=(e2,_,_)
    rw [Nat.add_comm (p1<<<_),Nat.add_comm (q1<<<_)]; rfl

theorem dcF_eq (w J K W T U : Nat) : ∀ f n d, dcF w J K W T U f n d=dcGo w J K W T U f n d
  | 0,n,d => rfl
  | f+1,0,d => by show dcStep w J K W T U (dcF w J K W T U f) 0 d=_; rfl
  | f+1,1,d => by
    show dcStep w J K W T U (dcF w J K W T U f) 1 d=_
    simp only [dcStep,dcGo]
    rw [show Nat.ble 1 1=true from rfl,show Nat.beq 1 0=false from rfl,Bool.cond_true,Bool.cond_false,leafF_eq]; rfl
  | f+1,n+2,d => by
    show dcStep w J K W T U (dcF w J K W T U f) (n+2) d=_
    have hb : Nat.ble (n+2) 1=false := by
      cases e : Nat.ble (n+2) 1
      · rfl
      · have := Nat.ble_eq.mp e; omega
    simp only [dcStep,hb,Bool.cond_false,dcGo,dcF_eq w J K W T U f,combF_eq]; rfl

/-- `kronDC` evaluated with `dcF`. -/
def kronF (w J K W T U n d : Nat) : Int :=
  Int.sub (Int.ofNat (Nat.shiftLeft (dcF w J K W T U 64 n d).2.1 (Nat.mul W (dcF w J K W T U 64 n d).1)))
    (Int.ofNat (Nat.shiftLeft (dcF w J K W T U 64 n d).2.2 (Nat.mul W (dcF w J K W T U 64 n d).1)))

theorem kronF_eq (w J K W T U n d : Nat) : kronF w J K W T U n d=kronGo w J K W T U n d := by
  rw [← kronDC_eq]; unfold kronF kronDC; simp only [dcF_eq]; rfl


/-! Generic term loops: a linear specification and a balanced evaluation. -/
def sumGo (F : Nat) (g : Nat → Int) : Nat → Nat → Int
  | 0,_ => 0
  | n+1,d => g (d&&&(2^F-1))+sumGo F g n (d>>>F)

def sumDC (F : Nat) (g : Nat → Int) : Nat → Nat → Nat → Int
  | _,0,_ => 0
  | _,1,d => g (d&&&(2^F-1))
  | 0,n+2,d => sumGo F g (n+2) d
  | f+1,n+2,d => sumDC F g f ((n+2)/2) d+sumDC F g f (n+2-(n+2)/2) (d>>>(F*((n+2)/2)))

theorem sumGo_add (F : Nat) (g : Nat → Int) : ∀ a b d, sumGo F g (a+b) d=sumGo F g a d+sumGo F g b (d>>>(F*a))
  | 0,b,d => by simp [sumGo]
  | a+1,b,d => by
    rw [show a+1+b=(a+b)+1 by omega,sumGo,sumGo,sumGo_add F g a b,← Nat.shiftRight_add,
      show F+F*a=F*(a+1) by ring]; ring

theorem sumDC_eq (F : Nat) (g : Nat → Int) : ∀ f n d, sumDC F g f n d=sumGo F g n d
  | _,0,_ => by simp [sumDC,sumGo]
  | f,1,d => by cases f <;> simp [sumDC,sumGo]
  | 0,n+2,d => by simp [sumDC]
  | f+1,n+2,d => by
    rw [sumDC,sumDC_eq F g f,sumDC_eq F g f,← sumGo_add]; congr 1; omega

def nsumGo (F : Nat) (g : Nat → Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,d => g (d&&&(2^F-1))+nsumGo F g n (d>>>F)

def nsumDC (F : Nat) (g : Nat → Nat) : Nat → Nat → Nat → Nat
  | _,0,_ => 0
  | _,1,d => g (d&&&(2^F-1))
  | 0,n+2,d => nsumGo F g (n+2) d
  | f+1,n+2,d => nsumDC F g f ((n+2)/2) d+nsumDC F g f (n+2-(n+2)/2) (d>>>(F*((n+2)/2)))

theorem nsumGo_add (F : Nat) (g : Nat → Nat) : ∀ a b d, nsumGo F g (a+b) d=nsumGo F g a d+nsumGo F g b (d>>>(F*a))
  | 0,b,d => by simp [nsumGo]
  | a+1,b,d => by
    rw [show a+1+b=(a+b)+1 by omega,nsumGo,nsumGo,nsumGo_add F g a b,← Nat.shiftRight_add,
      show F+F*a=F*(a+1) by ring]; ring

theorem nsumDC_eq (F : Nat) (g : Nat → Nat) : ∀ f n d, nsumDC F g f n d=nsumGo F g n d
  | _,0,_ => by simp [nsumDC,nsumGo]
  | f,1,d => by cases f <;> simp [nsumDC,nsumGo]
  | 0,n+2,d => by simp [nsumDC]
  | f+1,n+2,d => by
    rw [nsumDC,nsumDC_eq F g f,nsumDC_eq F g f,← nsumGo_add]; congr 1; omega

/-- `nsumDC` with native `Nat` operations and an explicit recursor (fewer kernel steps per term). -/
def nsumStep (F : Nat) (g : Nat → Nat) (ih : Nat → Nat → Nat) (n d : Nat) : Nat :=
  bif Nat.ble n 1 then (bif Nat.beq n 0 then 0 else g (Nat.land d (Nat.sub (Nat.pow 2 F) 1)))
  else Nat.add (ih (Nat.div n 2) d) (ih (Nat.sub n (Nat.div n 2)) (Nat.shiftRight d (Nat.mul F (Nat.div n 2))))

@[implemented_by nsumDC]
def nsumF (F : Nat) (g : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun n d => nsumDC F g 0 n d)
    (fun _ ih n d => nsumStep F g ih n d) f

theorem nsumF_eq (F : Nat) (g : Nat → Nat) : ∀ f n d, nsumF F g f n d=nsumDC F g f n d
  | 0,n,d => rfl
  | f+1,0,d => by show nsumStep F g (nsumF F g f) 0 d=_; rfl
  | f+1,1,d => by show nsumStep F g (nsumF F g f) 1 d=_; rfl
  | f+1,n+2,d => by
    show nsumStep F g (nsumF F g f) (n+2) d=_
    have hb : Nat.ble (n+2) 1=false := by
      cases e : Nat.ble (n+2) 1
      · rfl
      · have := Nat.ble_eq.mp e; omega
    simp only [nsumStep,hb,Bool.cond_false,nsumDC,nsumF_eq F g f]; rfl

/-- Least and largest `x`-degree of the terms, balanced (heuristics only). -/
def minDC (F : Nat) : Nat → Nat → Nat → Nat
  | _,0,_ => 255
  | _,1,d => fi (d&&&(2^F-1))
  | 0,_+2,_ => 0
  | f+1,n+2,d => min (minDC F f ((n+2)/2) d) (minDC F f (n+2-(n+2)/2) (d>>>(F*((n+2)/2))))
def maxDC (F : Nat) : Nat → Nat → Nat → Nat
  | _,0,_ => 0
  | _,1,d => fi (d&&&(2^F-1))
  | 0,_+2,_ => 255
  | f+1,n+2,d => max (maxDC F f ((n+2)/2) d) (maxDC F f (n+2-(n+2)/2) (d>>>(F*((n+2)/2))))

theorem l3_term (J K t : Nat) : l3 (term J K t)=t>>>25 := by
  simp only [term,l3_mono,l2_mono,l1_mono,fc]; split <;> simp only [Int.natAbs_neg,Int.natAbs_natCast]

theorem mag_le (w d : Nat) : (d&&&(2^(w+25)-1))>>>25≤2^w := by
  rw [Nat.shiftRight_eq_div_pow]
  have h1 : d&&&(2^(w+25)-1)≤2^(w+25) := le_trans Nat.and_le_right (Nat.sub_le _ _)
  have h2 : 2^(w+25)/2^25=2^w := by rw [pow_add,Nat.mul_div_cancel _ (by positivity)]
  rw [← h2]; exact Nat.div_le_div_right h1

theorem l3_polyGo (w J K : Nat) : ∀ n d, l3 (polyGo w J K n d)≤n*2^w
  | 0,_ => by simp [polyGo,l3]
  | n+1,d => by
    rw [polyGo]
    calc _≤_ := l3_add _ _
      _≤2^w+n*2^w := Nat.add_le_add (by rw [l3_term]; exact mag_le w d) (l3_polyGo w J K n _)
      _=(n+1)*2^w := by ring

theorem wide_term (J K t : Nat) : wide3 (J+1) (K+1) (term J K t)=true := by
  apply wide3_mono3
  · rw [len_mono2]; exact Nat.mod_lt _ (Nat.succ_pos _)
  · apply wide2_mono2; rw [len_mono1]; exact Nat.mod_lt _ (Nat.succ_pos _)

theorem wide_polyGo (w J K : Nat) : ∀ n d, wide3 (J+1) (K+1) (polyGo w J K n d)=true
  | 0,_ => by simp [polyGo,wide3]
  | n+1,d => wide3_add _ _ (wide_term J K _) (wide_polyGo w J K n _)

def kronB (J K W T U : Nat) : List (Nat × Nat × Nat) → Int
  | [] => 0
  | b::bs => kronF b.1 J K W T U b.2.1 b.2.2+kronB J K W T U bs

def normB : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | b::bs => b.2.1*2^b.1+normB bs

theorem kronB_eq (J K W T U : Nat) : ∀ bs,
    kronB J K W T U bs=ev3 ((((2:Int)^W)^U)^T) (((2:Int)^W)^U) ((2:Int)^W) (polyB J K bs)
  | [] => by simp [kronB,polyB,ev3]
  | b::bs => by rw [kronB,polyB,ev3_add,kronF_eq,kronGo_eq,kronB_eq J K W T U bs]

theorem l3_polyB (J K : Nat) : ∀ bs, l3 (polyB J K bs)≤normB bs
  | [] => by simp [polyB,l3]
  | b::bs => by
    rw [polyB,normB]
    exact le_trans (l3_add _ _) (Nat.add_le_add (l3_polyGo _ _ _ _ _) (l3_polyB J K bs))

theorem wide_polyB (J K : Nat) : ∀ bs, wide3 (J+1) (K+1) (polyB J K bs)=true
  | [] => by simp [polyB,wide3]
  | b::bs => wide3_add _ _ (wide_polyGo _ _ _ _ _) (wide_polyB J K bs)

end SP

end Sparse

section Expr

/-- Expressions over explicit polynomials, dense or sparse packed. -/
inductive Ex
  | lit (p : P3)
  | sp (s : SP)
  | add (a b : Ex)
  | sub (a b : Ex)
  | mul (a b : Ex)
deriving DecidableEq

def Ex.poly : Ex → P3
  | .lit p => p
  | .sp s => s.poly
  | .add a b => add3 a.poly b.poly
  | .sub a b => sub3 a.poly b.poly
  | .mul a b => mul3 a.poly b.poly

/-- Value at the Kronecker point with base `2^W`, computed with integers only. -/
def Ex.kron (W T U : Nat) : Ex → Int
  | .lit p => ev3 ((2^(W*U*T):Nat):Int) ((2^(W*U):Nat):Int) ((2^W:Nat):Int) p
  | .sp s => SP.kronB s.J s.K W T U s.bs
  | .add a b => a.kron W T U+b.kron W T U
  | .sub a b => a.kron W T U-b.kron W T U
  | .mul a b => a.kron W T U*b.kron W T U

def Ex.norm : Ex → Nat
  | .lit p => l3 p
  | .sp s => SP.normB s.bs
  | .add a b => a.norm+b.norm
  | .sub a b => a.norm+b.norm
  | .mul a b => a.norm*b.norm

/-- Width bounds of the two inner variables. -/
def Ex.wT : Ex → Nat
  | .lit p => (p.map List.length).foldr max 0
  | .sp s => s.J+1
  | .add a b => max a.wT b.wT
  | .sub a b => max a.wT b.wT
  | .mul a b => a.wT-1+max b.wT 1

def Ex.wU : Ex → Nat
  | .lit p => (p.map fun c => (c.map List.length).foldr max 0).foldr max 0
  | .sp s => s.K+1
  | .add a b => max a.wU b.wU
  | .sub a b => max a.wU b.wU
  | .mul a b => a.wU-1+max b.wU 1

def Ex.ev (x y z : ℝ) : Ex → ℝ
  | .lit p => ev3 x y z p
  | .sp s => ev3 x y z s.poly
  | .add a b => a.ev x y z+b.ev x y z
  | .sub a b => a.ev x y z-b.ev x y z
  | .mul a b => a.ev x y z*b.ev x y z

theorem Ex.ev_poly (x y z : ℝ) : ∀ e : Ex, ev3 x y z e.poly=e.ev x y z
  | .lit p => rfl
  | .sp s => rfl
  | .add a b => by simp only [Ex.poly,Ex.ev,ev3_add,Ex.ev_poly x y z a,Ex.ev_poly x y z b]
  | .sub a b => by simp only [Ex.poly,Ex.ev,ev3_sub,Ex.ev_poly x y z a,Ex.ev_poly x y z b]
  | .mul a b => by simp only [Ex.poly,Ex.ev,ev3_mul,Ex.ev_poly x y z a,Ex.ev_poly x y z b]

theorem Ex.kron_poly (W T U : Nat) : ∀ e : Ex,
    ev3 ((((2:Int)^W)^U)^T) (((2:Int)^W)^U) ((2:Int)^W) e.poly=e.kron W T U
  | .lit p => by
    simp only [Ex.poly,Ex.kron,Nat.cast_pow,Nat.cast_ofNat,← pow_mul]
  | .sp s => by rw [Ex.kron,SP.kronB_eq]; rfl
  | .add a b => by simp only [Ex.poly,Ex.kron,ev3_add,Ex.kron_poly W T U a,Ex.kron_poly W T U b]
  | .sub a b => by simp only [Ex.poly,Ex.kron,ev3_sub,Ex.kron_poly W T U a,Ex.kron_poly W T U b]
  | .mul a b => by simp only [Ex.poly,Ex.kron,ev3_mul,Ex.kron_poly W T U a,Ex.kron_poly W T U b]

theorem Ex.norm_poly : ∀ e : Ex, l3 e.poly≤e.norm
  | .lit p => le_refl _
  | .sp s => SP.l3_polyB _ _ _
  | .add a b => le_trans (l3_add _ _) (Nat.add_le_add (Ex.norm_poly a) (Ex.norm_poly b))
  | .sub a b => by
    simp only [Ex.poly,sub3,Ex.norm]
    have := l3_add a.poly (neg3 b.poly); rw [l3_neg] at this
    exact le_trans this (Nat.add_le_add (Ex.norm_poly a) (Ex.norm_poly b))
  | .mul a b => le_trans (l3_mul _ _) (Nat.mul_le_mul (Ex.norm_poly a) (Ex.norm_poly b))

private theorem foldr_max_le {l : List Nat} {x : Nat} (h : x∈l) : x≤l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl|h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem Ex.wide_poly : ∀ e : Ex, wide3 e.wT e.wU e.poly=true
  | .lit p => by
    simp only [wide3,wide2,List.all_eq_true,Bool.and_eq_true,Ex.poly,Ex.wT,Ex.wU]
    intro c hc
    refine ⟨decide_eq_true (foldr_max_le (List.mem_map.mpr ⟨c,hc,rfl⟩)),fun d hd => decide_eq_true ?_⟩
    exact le_trans (foldr_max_le (List.mem_map.mpr ⟨d,hd,rfl⟩))
      (foldr_max_le (l:=p.map fun c => (c.map List.length).foldr max 0) (List.mem_map.mpr ⟨c,hc,rfl⟩))
  | .sp s => SP.wide_polyB _ _ _
  | .add a b => by
    simp only [Ex.poly,Ex.wT,Ex.wU]
    apply wide3_add
    · exact wide3_mono (le_max_left _ _) (le_max_left _ _) _ (Ex.wide_poly a)
    · exact wide3_mono (le_max_right _ _) (le_max_right _ _) _ (Ex.wide_poly b)
  | .sub a b => by
    simp only [Ex.poly,Ex.wT,Ex.wU,sub3]
    apply wide3_add
    · exact wide3_mono (le_max_left _ _) (le_max_left _ _) _ (Ex.wide_poly a)
    · exact wide3_neg _ (wide3_mono (le_max_right _ _) (le_max_right _ _) _ (Ex.wide_poly b))
  | .mul a b => wide3_mul' _ _ (Ex.wide_poly a) (Ex.wide_poly b)
where
  wide3_mono {t u t' u' : Nat} (ht : t≤t') (hu : u≤u') (p : P3) (h : wide3 t u p=true) : wide3 t' u' p=true := by
    simp only [wide3,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
    exact fun c hc => ⟨le_trans (h c hc).1 ht,wide2_mono hu c (h c hc).2⟩

/-- The certificate check for an identity `e = 0` at every real point, with base `2^W`. -/
def Ex.check (W : Nat) (e : Ex) : Bool :=
  decide (2*e.norm<2^W) && decide (e.kron W e.wT e.wU=0)

theorem Ex.sound {W : Nat} {e : Ex} (h : e.check W=true) (x y z : ℝ) : e.ev x y z=0 := by
  simp only [Ex.check,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨hn,hk⟩ := h
  rw [←Ex.ev_poly]
  have hB : (1:Int)≤2^W := one_le_pow₀ (by norm_num)
  have hl : 2*(l3 e.poly:Int)<2^W := by
    have := Ex.norm_poly e
    have : 2*l3 e.poly<2^W := by omega
    exact_mod_cast this
  apply zero3 hB e.wT e.wU e.poly hl (Ex.wide_poly e)
  rw [Ex.kron_poly]; exact hk

/-- An exponent `W` with `x<2^W`, by doubling and then bisection (only a heuristic: the check
verifies the bound itself). -/
def clogUp : Nat → Nat → Nat → Nat
  | 0,_,W => W
  | f+1,x,W => if x<2^W then W else clogUp f x (2*W)
def clogBin : Nat → Nat → Nat → Nat → Nat
  | 0,_,_,hi => hi
  | f+1,x,lo,hi => if hi≤lo+1 then hi else
    if x<2^((lo+hi)/2) then clogBin f x lo ((lo+hi)/2) else clogBin f x ((lo+hi)/2) hi
def clogFrom (x hi : Nat) : Nat := clogBin 64 x (hi/2) hi
def clog (x : Nat) : Nat := clogFrom x (clogUp 64 x 1)

/-- The check at the least sufficient base. -/
def Ex.auto (e : Ex) : Bool := e.check (clog (2*e.norm))

theorem Ex.auto_sound {e : Ex} (h : e.auto=true) (x y z : ℝ) : e.ev x y z=0 := Ex.sound h x y z

/-- The check at an explicit base `2^W` and inner widths `T`, `U` (at least the actual widths). -/
def Ex.checkAt (W T U : Nat) (e : Ex) : Bool :=
  decide (2*e.norm<2^W) && decide (e.wT≤T) && decide (e.wU≤U) && decide (e.kron W T U=0)

theorem Ex.checkAt_sound {W T U : Nat} {e : Ex} (h : e.checkAt W T U=true) (x y z : ℝ) : e.ev x y z=0 := by
  simp only [Ex.checkAt,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn,ht⟩,hu⟩,hk⟩ := h
  rw [←Ex.ev_poly]
  have hB : (1:Int)≤2^W := one_le_pow₀ (by norm_num)
  have hl : 2*(l3 e.poly:Int)<2^W := by
    have := Ex.norm_poly e
    have : 2*l3 e.poly<2^W := by omega
    exact_mod_cast this
  apply zero3 hB T U e.poly hl (Ex.wide_poly.wide3_mono ht hu _ (Ex.wide_poly e))
  rw [Ex.kron_poly]; exact hk

/-- Two identities checked at one common base and common widths: a form occurring in both is
evaluated once (the kernel caches equal closed terms within a declaration). -/
def Ex.auto2 (a b : Ex) : Bool :=
  a.checkAt (clog (2*max a.norm b.norm)) (max a.wT b.wT) (max a.wU b.wU) &&
    b.checkAt (clog (2*max a.norm b.norm)) (max a.wT b.wT) (max a.wU b.wU)

theorem Ex.auto2_sound {a b : Ex} (h : Ex.auto2 a b=true) :
    (∀ x y z : ℝ, a.ev x y z=0) ∧ (∀ x y z : ℝ, b.ev x y z=0) := by
  simp only [Ex.auto2,Bool.and_eq_true] at h
  exact ⟨Ex.checkAt_sound h.1,Ex.checkAt_sound h.2⟩

end Expr

end ArtGallery.Orthogonal.BoundaryPoint.KronCert
end
