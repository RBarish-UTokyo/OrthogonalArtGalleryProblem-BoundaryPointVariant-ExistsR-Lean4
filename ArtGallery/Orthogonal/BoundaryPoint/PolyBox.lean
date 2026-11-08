module

public import ArtGallery.Orthogonal.BoundaryPoint.KronCert

/-! # Signs of dense polynomials over the parameter box

A dense polynomial in `(x,y,z)` is bounded below by interval arithmetic along its
Horner scheme, for `0<x≤c`, `bl≤y≤bh` with `0≤bl` and `0≤z≤1`. Leading
coefficient blocks that vanish identically are divided out (`x>0`), so a
polynomial `x^k*(q+x*r)` is certified positive when the lower bound of `q`
dominates the possible negative part of `x*r`. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PolyBox
open KronCert

/-- Lower and upper bounds over `0≤z≤1`. -/
def lo1 : P1 → ℚ
  | [] => 0
  | a::p => a+min 0 (lo1 p)
def hi1 : P1 → ℚ
  | [] => 0
  | a::p => a+max 0 (hi1 p)

/-- Bounds over `bl≤y≤bh`, `0≤z≤1`. -/
def lo2 (bl bh : ℚ) : P2 → ℚ
  | [] => 0
  | p::q => lo1 p+min (bl*lo2 bl bh q) (bh*lo2 bl bh q)
def hi2 (bl bh : ℚ) : P2 → ℚ
  | [] => 0
  | p::q => hi1 p+max (bl*hi2 bl bh q) (bh*hi2 bl bh q)

/-- Lower bound over `0≤x≤c`. -/
def lo3 (c bl bh : ℚ) : P3 → ℚ
  | [] => 0
  | p::q => lo2 bl bh p+min 0 (c*lo3 c bl bh q)

def zero2 (p : P2) : Bool := p.all (·.all (·==0))

/-- Certified positivity for `0<x≤c`. -/
def pos3 (c bl bh : ℚ) : P3 → Bool
  | [] => false
  | p::q => if zero2 p then pos3 c bl bh q else decide (0<lo2 bl bh p+min 0 (c*lo3 c bl bh q))

section Sound
variable {x y z : ℝ} {c bl bh : ℚ}

theorem bound1 (z0 : 0≤z) (z1 : z≤1) : ∀ p : P1, (lo1 p:ℝ)≤ev1 z p ∧ ev1 z p≤hi1 p
  | [] => by simp [lo1,hi1,ev1]
  | a::p => by
    obtain ⟨l,h⟩ := bound1 z0 z1 p
    simp only [lo1,hi1,ev1]; push_cast
    constructor
    · have : (min 0 (lo1 p:ℝ))≤z*ev1 z p := by
        rcases le_total 0 (lo1 p:ℝ) with q|q
        · rw [min_eq_left q]; exact mul_nonneg z0 (q.trans l)
        · rw [min_eq_right q]; nlinarith
      linarith
    · have : z*ev1 z p≤max 0 (hi1 p:ℝ) := by
        rcases le_total 0 (hi1 p:ℝ) with q|q
        · rw [max_eq_right q]; nlinarith
        · rw [max_eq_left q]; nlinarith
      linarith

theorem bound2 (z0 : 0≤z) (z1 : z≤1) (y0 : (bl:ℝ)≤y) (y1 : y≤bh) (b0 : 0≤bl) :
    ∀ p : P2, (lo2 bl bh p:ℝ)≤ev2 y z p ∧ ev2 y z p≤hi2 bl bh p
  | [] => by simp [lo2,hi2,ev2]
  | a::p => by
    obtain ⟨l,h⟩ := bound2 z0 z1 y0 y1 b0 p
    obtain ⟨l1,h1⟩ := bound1 z0 z1 a
    have yb : (0:ℝ)≤bl := by exact_mod_cast b0
    have y0' : 0≤y := yb.trans y0
    simp only [lo2,hi2,ev2]; push_cast
    constructor
    · have : min ((bl:ℝ)*lo2 bl bh p) ((bh:ℝ)*lo2 bl bh p)≤y*ev2 y z p := by
        rcases le_total 0 (lo2 bl bh p:ℝ) with q|q
        · exact (min_le_left _ _).trans (by nlinarith)
        · exact (min_le_right _ _).trans (by nlinarith)
      linarith
    · have : y*ev2 y z p≤max ((bl:ℝ)*hi2 bl bh p) ((bh:ℝ)*hi2 bl bh p) := by
        rcases le_total 0 (hi2 bl bh p:ℝ) with q|q
        · exact (by nlinarith : y*ev2 y z p≤bh*hi2 bl bh p).trans (le_max_right _ _)
        · exact (by nlinarith : y*ev2 y z p≤bl*hi2 bl bh p).trans (le_max_left _ _)
      linarith

theorem bound3 (x0 : 0≤x) (x1 : x≤c) (z0 : 0≤z) (z1 : z≤1) (y0 : (bl:ℝ)≤y) (y1 : y≤bh) (b0 : 0≤bl) :
    ∀ p : P3, (lo3 c bl bh p:ℝ)≤ev3 x y z p
  | [] => by simp [lo3,ev3]
  | a::p => by
    have l := bound3 x0 x1 z0 z1 y0 y1 b0 p
    have l2 := (bound2 z0 z1 y0 y1 b0 a).1
    simp only [lo3,ev3]; push_cast
    have : min 0 ((c:ℝ)*lo3 c bl bh p)≤x*ev3 x y z p := by
      rcases le_total 0 (lo3 c bl bh p:ℝ) with q|q
      · exact (min_le_left _ _).trans (mul_nonneg x0 (q.trans l))
      · exact (min_le_right _ _).trans (by nlinarith)
    linarith

theorem zero1_ev : ∀ {a : P1}, a.all (·==0)=true → ∀ z : ℝ, ev1 z a=0
  | [],_,_ => rfl
  | c::a,h,z => by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
    simp only [ev1,h.1,zero1_ev h.2 z]; simp

theorem zero2_ev : ∀ {p : P2}, zero2 p=true → ∀ y z : ℝ, ev2 y z p=0
  | [],_,_,_ => rfl
  | a::p,h,y,z => by
    simp only [zero2,List.all_cons,Bool.and_eq_true] at h
    have := zero2_ev (p:=p) (by simpa [zero2] using h.2) y z
    simp only [ev2,zero1_ev h.1 z,this]; simp

theorem pos3_sound (x0 : 0<x) (x1 : x≤c) (z0 : 0≤z) (z1 : z≤1) (y0 : (bl:ℝ)≤y) (y1 : y≤bh) (b0 : 0≤bl) :
    ∀ p : P3, pos3 c bl bh p=true → 0<ev3 x y z p
  | [],h => by simp [pos3] at h
  | a::p,h => by
    simp only [pos3] at h
    split at h
    · next hz =>
      simp only [ev3,zero2_ev hz]
      have := pos3_sound x0 x1 z0 z1 y0 y1 b0 p h
      simpa using mul_pos x0 this
    · have hq := decide_eq_true_eq.mp h
      have l := bound3 x0.le x1 z0 z1 y0 y1 b0 p
      have l2 := (bound2 z0 z1 y0 y1 b0 a).1
      simp only [ev3]
      have : min 0 ((c:ℝ)*lo3 c bl bh p)≤x*ev3 x y z p := by
        rcases le_total 0 (lo3 c bl bh p:ℝ) with q|q
        · exact (min_le_left _ _).trans (mul_nonneg x0.le (q.trans l))
        · exact (min_le_right _ _).trans (by nlinarith)
      have hq' : (0:ℝ)<(lo2 bl bh a:ℝ)+min 0 ((c:ℝ)*(lo3 c bl bh p:ℝ)) := by
        have : ((lo2 bl bh a+min 0 (c*lo3 c bl bh p) : ℚ) : ℝ)=(lo2 bl bh a:ℝ)+min 0 ((c:ℝ)*(lo3 c bl bh p:ℝ)) := by
          push_cast; rfl
        rw [←this]; exact_mod_cast hq
      linarith

end Sound

/-- The parameter box of a channel. -/
structure Box (c bl bh : ℚ) (x y z : ℝ) : Prop where
  x0 : 0<x
  x1 : x≤c
  y0 : (bl:ℝ)≤y
  y1 : y≤bh
  z0 : 0≤z
  z1 : z≤1
  b0 : 0≤bl

theorem Box.pos {c bl bh : ℚ} {x y z : ℝ} (B : Box c bl bh x y z) {p : P3} (h : pos3 c bl bh p=true) :
    0<ev3 x y z p := pos3_sound B.x0 B.x1 B.z0 B.z1 B.y0 B.y1 B.b0 p h


/-- Multiplication of every coefficient by a sign. -/
def sc3 (σ : Int) (p : P3) : P3 := p.map (·.map (·.map (σ*·)))

theorem ev3_sc3 (σ : Int) (x y z : ℝ) (p : P3) : ev3 x y z (sc3 σ p)=σ*ev3 x y z p := by
  have h1 (q : P1) : ev1 z (q.map (σ*·))=σ*ev1 z q := by
    induction q with
    | nil => simp [ev1]
    | cons a q ih => simp only [List.map_cons,ev1,ih]; push_cast; ring
  have h2 (q : P2) : ev2 y z (q.map (·.map (σ*·)))=σ*ev2 y z q := by
    induction q with
    | nil => simp [ev2]
    | cons a q ih => simp only [List.map_cons,ev2,ih,h1]; ring
  induction p with
  | nil => simp [sc3,ev3]
  | cons a p ih =>
    simp only [sc3,List.map_cons,ev3] at ih ⊢
    rw [ih,h2]; ring

section Sparse
open SP
/-! ## Positivity on the parameter box by sparse dominance

On `0<x≤c`, `bl≤y≤bh`, `0≤z≤1` with `0≤bl`, every term has `x`-degree at least `m` (checked), so
the polynomial is `x^m*g`. Each positive term of `g` of degree zero in `x` and `z` is at least
`a*bl^j`, other positive terms are nonnegative, and each negative term is at least
`-|a|*c^i*bh^j`. Scaled by the positive integer `cd^I*ld^J*hd^J` these bounds are integers. -/

/-- A term counts as negative when its sign bit differs from `neg`. -/
def sneg (neg : Bool) (t : Nat) : Bool := if (t>>>24)%2=1 then !neg else neg

/-- The signed coefficient of a term, negated when `neg`. -/
def sco (neg : Bool) (t : Nat) : Int := if sneg neg t then -((t>>>25:Nat):Int) else ((t>>>25:Nat):Int)

/-- Scaled lower bound of one term: positive part (terms of degree `m` in `x` and `0` in `z`) and
negative part. -/
def lbP (neg : Bool) (m I J K ln ld cd hd t : Nat) : Nat :=
  if fi t=m ∧ fk K t=0 ∧ sneg neg t=false then (t>>>25)*(ln^fj J t*ld^(J-fj J t)*cd^I*hd^J) else 0
def lbN (neg : Bool) (m I J cn cd hn hd ld t : Nat) : Nat :=
  if sneg neg t=true then (t>>>25)*(cn^(fi t-m)*cd^(I-(fi t-m))*hn^fj J t*hd^(J-fj J t)*ld^J) else 0

/-- `sneg`, `lbP`, `lbN` with boolean tests (fewer kernel steps per term). -/
def snegF (neg : Bool) (t : Nat) : Bool := bif Nat.beq ((t>>>24)%2) 1 then !neg else neg
def lbPF (neg : Bool) (m I J K ln ld cd hd t : Nat) : Nat :=
  bif Nat.beq (fi t) m && Nat.beq (fk K t) 0 && !snegF neg t then (t>>>25)*(ln^fj J t*ld^(J-fj J t)*cd^I*hd^J) else 0
def lbNF (neg : Bool) (m I J cn cd hn hd ld t : Nat) : Nat :=
  bif snegF neg t then (t>>>25)*(cn^(fi t-m)*cd^(I-(fi t-m))*hn^fj J t*hd^(J-fj J t)*ld^J) else 0

theorem snegF_eq (neg : Bool) (t : Nat) : snegF neg t=sneg neg t := by
  unfold snegF sneg
  by_cases h : (t>>>24)%2=1
  · rw [if_pos h,show Nat.beq ((t>>>24)%2) 1=true from Nat.beq_eq_true_eq _ _ ▸ h]; rfl
  · rw [if_neg h]
    have : Nat.beq ((t>>>24)%2) 1=false := by
      cases e : Nat.beq ((t>>>24)%2) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [this]; rfl

theorem lbPF_eq (neg : Bool) (m I J K ln ld cd hd : Nat) : lbPF neg m I J K ln ld cd hd=lbP neg m I J K ln ld cd hd := by
  funext t; unfold lbPF lbP; rw [snegF_eq]
  by_cases h : fi t=m ∧ fk K t=0 ∧ sneg neg t=false
  · rw [if_pos h]; obtain ⟨h1,h2,h3⟩ := h; simp [h1,h2,h3]
  · rw [if_neg h]
    cases e : (Nat.beq (fi t) m && Nat.beq (fk K t) 0 && !sneg neg t)
    · rfl
    · simp only [Bool.and_eq_true,Bool.not_eq_true'] at e
      exact absurd ⟨Nat.eq_of_beq_eq_true e.1.1,Nat.eq_of_beq_eq_true e.1.2,e.2⟩ h

theorem lbNF_eq (neg : Bool) (m I J cn cd hn hd ld : Nat) : lbNF neg m I J cn cd hn hd ld=lbN neg m I J cn cd hn hd ld := by
  funext t; unfold lbNF lbN; rw [snegF_eq]
  cases sneg neg t <;> rfl

/-- Every term has `x`-degree in `[m, m+I]`. -/
def degGo (w : Nat) (m I : Nat) : Nat → Nat → Bool
  | 0,_ => true
  | n+1,d => decide (m≤fi (d&&&(2^(w+25)-1))) && decide (fi (d&&&(2^(w+25)-1))≤m+I) && degGo w m I n (d>>>(w+25))

def degB (m I : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => true
  | b::bs => degGo b.1 m I b.2.1 b.2.2 && degB m I bs

/-- Positive and negative parts over the blocks. -/
def lbPB (neg : Bool) (m I J K ln ld cd hd : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | b::bs => nsumF (b.1+25) (lbPF neg m I J K ln ld cd hd) 64 b.2.1 b.2.2+lbPB neg m I J K ln ld cd hd bs
def lbNB (neg : Bool) (m I J cn cd hn hd ld : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | b::bs => nsumF (b.1+25) (lbNF neg m I J cn cd hn hd ld) 64 b.2.1 b.2.2+lbNB neg m I J cn cd hn hd ld bs

/-- Least and largest `x`-degree over the blocks (heuristics: `degB` checks the choice). -/
def minB : List (Nat × Nat × Nat) → Nat
  | [] => 255
  | b::bs => min (minDC (b.1+25) 64 b.2.1 b.2.2) (minB bs)
def maxB : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | b::bs => max (maxDC (b.1+25) 64 b.2.1 b.2.2) (maxB bs)

/-- The positivity check at given degree bounds. -/
def spPosAt (c bl bh : ℚ) (neg : Bool) (s : SP) (m I : Nat) : Bool :=
  degB m I s.bs && decide (0≤bl) &&
    decide (lbNB neg m I s.J c.num.toNat c.den bh.num.toNat bh.den bl.den s.bs<
      lbPB neg m I s.J s.K bl.num.toNat bl.den c.den bh.den s.bs)

def spPos (c bl bh : ℚ) (neg : Bool) (s : SP) : Bool :=
  spPosAt c bl bh neg s (minB s.bs) (maxB s.bs-minB s.bs)

section PosSound
variable {x y z : ℝ} {c bl bh : ℚ}

private theorem qcast {q : ℚ} (h : 0≤q) : (q:ℝ)=(q.num.toNat:ℝ)/(q.den:ℝ) := by
  have e : ((q.num.toNat:Int):ℝ)=(q.num:ℝ) := by
    congr 1; exact Int.toNat_of_nonneg (Rat.num_nonneg.mpr h)
  rw [show ((q.num.toNat:Nat):ℝ)=((q.num.toNat:Int):ℝ) by norm_cast,e]
  exact_mod_cast (Rat.num_div_den q).symm

/-- A lower bound `ln/ld ≤ v` with `0≤ln` gives `ln^j ≤ (ld*v)^j`; an upper bound gives the
reverse for `0≤v`. -/
private theorem lo_pow {v : ℝ} {ln ld : Nat} (hd : 0<ld) (h : (ln:ℝ)/ld≤v) (j : Nat) :
    (ln:ℝ)^j≤(ld*v)^j := by
  apply pow_le_pow_left₀ (by positivity)
  rwa [div_le_iff₀ (by exact_mod_cast hd),mul_comm] at h
private theorem hi_pow {v : ℝ} {hn hd : Nat} (hd0 : 0<hd) (v0 : 0≤v) (h : v≤(hn:ℝ)/hd) (j : Nat) :
    (hd*v)^j≤(hn:ℝ)^j := by
  apply pow_le_pow_left₀ (by positivity)
  rwa [le_div_iff₀ (by exact_mod_cast hd0),mul_comm] at h

theorem ev_term (x y z : ℝ) (J K t : Nat) : ev3 x y z (term J K t)=(fc t:ℝ)*z^fk K t*y^fj J t*x^fi t := by
  simp only [term,ev3_mono,ev2_mono,ev1_mono]

private theorem pos_case {S y ln ld C H : ℝ} (hS : 0≤S) (ld0 : 0<ld) (ln0 : 0≤ln) (hy : ln/ld≤y)
    {j J : Nat} (hj : j≤J) (C0 : 0≤C) (H0 : 0≤H) :
    S*(ln^j*ld^(J-j)*C*H)≤C*ld^J*H*(S*y^j) := by
  have Dj : ld^J=ld^(J-j)*ld^j := by rw [← pow_add]; congr 1; omega
  have hl : ln^j≤ld^j*y^j := by
    rw [← mul_pow]; apply pow_le_pow_left₀ ln0
    rwa [div_le_iff₀ ld0,mul_comm] at hy
  calc S*(ln^j*ld^(J-j)*C*H)=(S*C*H*ld^(J-j))*ln^j := by ring
    _≤(S*C*H*ld^(J-j))*(ld^j*y^j) := by gcongr
    _=_ := by rw [Dj]; ring

private theorem neg_case {S x y z cn cd hn hd ld : ℝ} (hS : S≤0) (cd0 : 0<cd) (hd0 : 0<hd) (ld0 : 0≤ld)
    (x0 : 0≤x) (hx : x≤cn/cd) (y0 : 0≤y) (hy : y≤hn/hd) (z0 : 0≤z) (z1 : z≤1)
    {a I j J k : Nat} (ha : a≤I) (hj : j≤J) :
    S*(cn^a*cd^(I-a)*hn^j*hd^(J-j)*ld^J)≤cd^I*ld^J*hd^J*(S*z^k*y^j*x^a) := by
  have Ca : cd^I=cd^(I-a)*cd^a := by rw [← pow_add]; congr 1; omega
  have Hj : hd^J=hd^(J-j)*hd^j := by rw [← pow_add]; congr 1; omega
  have px : (cd*x)^a≤cn^a := pow_le_pow_left₀ (by positivity) (by rwa [le_div_iff₀ cd0,mul_comm] at hx) a
  have py : (hd*y)^j≤hn^j := pow_le_pow_left₀ (by positivity) (by rwa [le_div_iff₀ hd0,mul_comm] at hy) j
  have zk0 : 0≤z^k := pow_nonneg z0 k
  have zk1 : z^k≤1 := pow_le_one₀ z0 z1
  have prod : (cd*x)^a*(hd*y)^j*z^k≤cn^a*hn^j := by
    calc _≤(cd*x)^a*(hd*y)^j*1 := by gcongr
      _≤_ := by rw [mul_one]; gcongr; exact le_trans (by positivity) px
  have Q0 : 0≤cd^(I-a)*hd^(J-j)*ld^J := by positivity
  have := mul_le_mul_of_nonpos_left prod (mul_nonpos_of_nonpos_of_nonneg hS Q0)
  calc S*(cn^a*cd^(I-a)*hn^j*hd^(J-j)*ld^J)=(S*(cd^(I-a)*hd^(J-j)*ld^J))*(cn^a*hn^j) := by ring
    _≤(S*(cd^(I-a)*hd^(J-j)*ld^J))*((cd*x)^a*(hd*y)^j*z^k) := this
    _=_ := by rw [Ca,Hj,mul_pow,mul_pow]; ring

theorem lbt_le (B : Box c bl bh x y z) {neg : Bool} {m I J K t : Nat}
    (hm : m≤fi t) (hI : fi t≤m+I) (hJ : fj J t≤J) :
    (((lbP neg m I J K bl.num.toNat bl.den c.den bh.den t:Int)-
        (lbN neg m I J c.num.toNat c.den bh.num.toNat bh.den bl.den t:Int):Int):ℝ)*x^m≤
      ((c.den:ℝ)^I*(bl.den:ℝ)^J*(bh.den:ℝ)^J)*((if neg then -1 else 1)*ev3 x y z (term J K t)) := by
  have bl0 : (0:ℚ)≤bl := B.b0
  have bl0' : (0:ℝ)≤bl := by exact_mod_cast bl0
  have y0 : 0≤y := le_trans bl0' B.y0
  have c0 : (0:ℚ)≤c := by
    have : (0:ℝ)≤c := le_trans B.x0.le B.x1
    exact_mod_cast this
  have bh0 : (0:ℚ)≤bh := by
    have : (0:ℝ)≤bh := le_trans y0 B.y1
    exact_mod_cast this
  have cd : (0:ℝ)<c.den := by exact_mod_cast c.den_pos
  have ld : (0:ℝ)<bl.den := by exact_mod_cast bl.den_pos
  have hd : (0:ℝ)<bh.den := by exact_mod_cast bh.den_pos
  obtain ⟨a,ha⟩ : ∃ a, fi t=m+a := ⟨fi t-m,by omega⟩
  have am : fi t-m=a := by omega
  have aI : a≤I := by omega
  have sc : ((if neg then -1 else 1:ℝ))*(fc t:ℝ)=(sco neg t:ℝ) := by
    unfold sco sneg fc
    by_cases hb : (t>>>24)%2=1
    · simp only [hb,↓reduceIte]; cases neg <;> simp
    · simp only [hb,↓reduceIte]; cases neg <;> simp
  have e : (if neg then -1 else 1:ℝ)*ev3 x y z (term J K t)=
      ((sco neg t:ℝ)*z^fk K t*y^fj J t*x^a)*x^m := by
    rw [ev_term,ha,pow_add,← sc]; ring
  rw [e,← mul_assoc]
  have xm : 0<x^m := pow_pos B.x0 m
  apply mul_le_mul_of_nonneg_right _ xm.le
  unfold lbP lbN
  rw [am]
  have mag0 : (0:ℝ)≤((t>>>25:Nat):ℝ) := Nat.cast_nonneg _
  cases hs : sneg neg t
  · -- a nonnegative coefficient
    have S : (sco neg t:ℝ)=((t>>>25:Nat):ℝ) := by
      simp only [sco,hs,Bool.false_eq_true,ite_false,Int.cast_natCast]
    rw [S]
    by_cases h : fi t=m ∧ fk K t=0
    · simp only [show (fi t=m ∧ fk K t=0 ∧ sneg neg t=false) from ⟨h.1,h.2,hs⟩,Bool.false_eq_true,and_self,↓reduceIte]
      have a0 : a=0 := by omega
      have key := pos_case mag0 ld (Nat.cast_nonneg (bl.num.toNat)) ((qcast bl0).symm.le.trans B.y0) hJ
        (show (0:ℝ)≤(c.den:ℝ)^I by positivity) (show (0:ℝ)≤(bh.den:ℝ)^J by positivity)
      rw [a0]
      convert key using 1 <;> (try simp only [Nat.cast_mul,Nat.cast_pow,Int.cast_mul,Int.cast_natCast,Nat.cast_zero,sub_zero,Int.cast_pow]); ring
    · simp only [and_true,h,↓reduceIte,Bool.false_eq_true,Nat.cast_zero,sub_zero,Int.cast_zero]
      have := pow_nonneg y0 (fj J t); have := pow_nonneg B.x0.le a; have := pow_nonneg B.z0 (fk K t)
      positivity
  · -- a negative coefficient
    have S : (sco neg t:ℝ)=-((t>>>25:Nat):ℝ) := by
      simp only [sco,hs,ite_true,Int.cast_neg,Int.cast_natCast]
    simp only [Bool.true_eq_false,and_false,↓reduceIte]
    have hS : (sco neg t:ℝ)≤0 := by rw [S]; linarith
    have key := neg_case hS cd hd ld.le B.x0.le (B.x1.trans (qcast c0).le) y0
      (B.y1.trans (qcast bh0).le) B.z0 B.z1 (k:=fk K t) aI hJ
    rw [S] at key; rw [S]
    convert key using 1; simp only [Nat.cast_mul,Nat.cast_pow,Int.cast_mul,Int.cast_natCast,Int.cast_neg,Nat.cast_zero,zero_sub,Int.cast_pow]; ring

theorem fj_le (J t : Nat) : fj J t≤J := Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))

theorem lbGo_le (B : Box c bl bh x y z) {w J K : Nat} {neg : Bool} {m I : Nat} : ∀ n d,
    degGo w m I n d=true →
    (((nsumGo (w+25) (lbP neg m I J K bl.num.toNat bl.den c.den bh.den) n d:Int)-
        (nsumGo (w+25) (lbN neg m I J c.num.toNat c.den bh.num.toNat bh.den bl.den) n d:Int):Int):ℝ)*x^m≤
      ((c.den:ℝ)^I*(bl.den:ℝ)^J*(bh.den:ℝ)^J)*((if neg then -1 else 1)*ev3 x y z (polyGo w J K n d))
  | 0,d,_ => by simp [nsumGo,polyGo,ev3]
  | n+1,d,h => by
    simp only [degGo,Bool.and_eq_true,decide_eq_true_eq] at h
    have h1 := lbt_le (neg:=neg) (K:=K) B h.1.1 h.1.2 (fj_le J _)
    have h2 := lbGo_le (J:=J) (K:=K) (neg:=neg) B n _ h.2
    rw [nsumGo,nsumGo,polyGo,ev3_add]; push_cast at h1 h2 ⊢
    linarith

theorem lbB_le (B : Box c bl bh x y z) {J K : Nat} {neg : Bool} {m I : Nat} : ∀ bs,
    degB m I bs=true →
    (((lbPB neg m I J K bl.num.toNat bl.den c.den bh.den bs:Int)-
        (lbNB neg m I J c.num.toNat c.den bh.num.toNat bh.den bl.den bs:Int):Int):ℝ)*x^m≤
      ((c.den:ℝ)^I*(bl.den:ℝ)^J*(bh.den:ℝ)^J)*((if neg then -1 else 1)*ev3 x y z (polyB J K bs))
  | [],_ => by simp [lbPB,lbNB,polyB,ev3]
  | b::bs,h => by
    simp only [degB,Bool.and_eq_true] at h
    have h1 := lbGo_le (J:=J) (K:=K) (neg:=neg) B _ _ h.1
    have h2 := lbB_le (J:=J) (K:=K) (neg:=neg) B bs h.2
    simp only [lbPB,lbNB,nsumF_eq,lbPF_eq,lbNF_eq,nsumDC_eq,polyB,ev3_add]
    push_cast at h1 h2 ⊢
    linarith

theorem spPos_sound {s : SP} {neg : Bool} (h : spPos c bl bh neg s=true) (B : Box c bl bh x y z) :
    0<(if neg then -1 else 1)*ev3 x y z s.poly := by
  unfold spPos spPosAt at h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hd,-⟩,hl⟩ := h
  have le := lbB_le (J:=s.J) (K:=s.K) (neg:=neg) B _ hd
  have D0 : (0:ℝ)<(c.den:ℝ)^(maxB s.bs-minB s.bs)*(bl.den:ℝ)^s.J*(bh.den:ℝ)^s.J := by
    have := c.den_pos; have := bl.den_pos; have := bh.den_pos; positivity
  have l0 := mul_pos (show (0:ℝ)<(((lbPB neg (minB s.bs) (maxB s.bs-minB s.bs) s.J s.K bl.num.toNat bl.den
      c.den bh.den s.bs:Int)-(lbNB neg (minB s.bs) (maxB s.bs-minB s.bs) s.J c.num.toNat c.den bh.num.toNat
      bh.den bl.den s.bs:Int):Int):ℝ) by
        have := Int.sub_pos.mpr (Int.ofNat_lt.mpr hl)
        exact_mod_cast this) (pow_pos B.x0 (minB s.bs))
  exact pos_of_mul_pos_right (lt_of_lt_of_le l0 le) D0.le

end PosSound


end Sparse

/-- The sign certificate `σ*e>0` on the box: a dense literal by interval Horner bounds, a packed
literal by sparse dominance. -/
def signPos (c bl bh : ℚ) (σ : Int) : Ex → Bool
  | .lit p => decide (σ=1 ∨ σ=-1) && pos3 c bl bh (sc3 σ p)
  | .sp s => (decide (σ=1) && spPos c bl bh false s) || (decide (σ=-1) && spPos c bl bh true s)
  | _ => false

theorem signPos_sound {c bl bh : ℚ} {x y z : ℝ} (B : Box c bl bh x y z) {σ : Int} {e : Ex}
    (h : signPos c bl bh σ e=true) : 0<σ*e.ev x y z := by
  cases e with
  | lit p =>
    simp only [signPos,Bool.and_eq_true,decide_eq_true_eq] at h
    have := B.pos h.2; rwa [ev3_sc3] at this
  | sp s =>
    simp only [signPos,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨rfl,h⟩|⟨rfl,h⟩
    · have := spPos_sound h B; simpa [Ex.ev] using this
    · have := spPos_sound h B; simpa [Ex.ev] using this
  | add a b => simp [signPos] at h
  | sub a b => simp [signPos] at h
  | mul a b => simp [signPos] at h

theorem signPos_sign {c bl bh : ℚ} {σ : Int} {e : Ex} (h : signPos c bl bh σ e=true) : σ=1 ∨ σ=-1 := by
  cases e with
  | lit p => simp only [signPos,Bool.and_eq_true,decide_eq_true_eq] at h; exact h.1
  | sp s =>
    simp only [signPos,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨rfl,-⟩|⟨rfl,-⟩ <;> simp
  | add a b => simp [signPos] at h
  | sub a b => simp [signPos] at h
  | mul a b => simp [signPos] at h

end ArtGallery.Orthogonal.BoundaryPoint.PolyBox
end
