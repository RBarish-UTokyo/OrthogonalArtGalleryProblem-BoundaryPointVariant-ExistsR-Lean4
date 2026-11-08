module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterProduct

/-! # Integer determinant signs on a register chart

The coordinate forms of a chart have rational coefficients. For the kernel, rational arithmetic is
an order of magnitude slower than integer arithmetic, so the sign checks of chart determinants are
also offered on an integer copy of the chart: every `x`-form is multiplied by the least common
multiple `dx` of its coefficient denominators (likewise `dy`), and every atom box by the least
common multiple `db` of the box denominators. A term is stored with the packed key
`power * KEY + atom`. The integer copy is computed from the rational chart (`ZData.ofChart`), so its
correctness is a lemma, and certificates are checked against a literal copy equal to it.

The checks are exact rescalings of `RegisterProduct.check` and `RegisterForm.positive`, with two
additions: a product check may use any of the three points of the determinant as its base, and the
expanded determinant is formed over packed pairs of atoms. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ZSign
open RegisterForm MarginCert

/-! ## Balanced index trees -/

/-- A list stored for logarithmic lookup: index `0` at the root, odd indices on the left, even
positive indices on the right. -/
inductive ITree (α : Type) where
  | nil
  | node (v : α) (l r : ITree α)
deriving DecidableEq

mutual
def evens {α : Type} : List α → List α
  | [] => []
  | x::xs => x::odds xs
def odds {α : Type} : List α → List α
  | [] => []
  | _::xs => evens xs
end

def ITree.ofListF {α : Type} : Nat → List α → ITree α
  | 0,_ => .nil
  | _,[] => .nil
  | f+1,x::xs => .node x (ITree.ofListF f (evens xs)) (ITree.ofListF f (odds xs))

def ITree.ofList {α : Type} (l : List α) : ITree α := ITree.ofListF l.length l

def ITree.get {α : Type} (d : α) : ITree α → Nat → α
  | .nil,_ => d
  | .node v _ _,0 => v
  | .node _ l r,i+1 => if i%2=0 then l.get d (i/2) else r.get d (i/2)

theorem split_get {α : Type} : ∀ l : List α, (∀ k, (evens l)[k]?=l[2*k]?) ∧ (∀ k, (odds l)[k]?=l[2*k+1]?) ∧
    (evens l).length≤l.length ∧ (odds l).length≤l.length
  | [] => by simp [evens,odds]
  | x::xs => by
    obtain ⟨e,o,le,lo⟩ := split_get xs
    refine ⟨?_,?_,?_,?_⟩
    · intro k
      cases k with
      | zero => simp [evens]
      | succ k => rw [evens,List.getElem?_cons_succ,o k,show 2*(k+1)=(2*k+1)+1 by omega,List.getElem?_cons_succ]
    · intro k
      rw [odds,e k,show 2*k+1=(2*k)+1 by omega,List.getElem?_cons_succ]
    · simp only [evens,List.length_cons]; omega
    · simp only [odds,List.length_cons]; omega

theorem get_ofListF {α : Type} (d : α) : ∀ f (l : List α), l.length≤f → ∀ i, (ITree.ofListF f l).get d i=l.getD i d
  | 0,l,h,i => by
    have : l=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ITree.ofListF,ITree.get]
  | f+1,[],_,i => by simp [ITree.ofListF,ITree.get]
  | f+1,x::xs,h,i => by
    obtain ⟨e,o,le,lo⟩ := split_get xs
    simp only [List.length_cons] at h
    cases i with
    | zero => simp [ITree.ofListF,ITree.get]
    | succ i =>
      simp only [ITree.ofListF,ITree.get]
      split
      · next he =>
        rw [get_ofListF d f _ (by omega),List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,e,
          List.getElem?_cons_succ,show 2*(i/2)=i by omega]
      · next ho =>
        rw [get_ofListF d f _ (by omega),List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,o,
          List.getElem?_cons_succ,show 2*(i/2)+1=i by omega]

theorem get_ofList {α : Type} (d : α) (l : List α) (i : Nat) : (ITree.ofList l).get d i=l.getD i d :=
  get_ofListF d _ l le_rfl i

/-! ## Integer forms -/

def KEY : Nat := 1048576
/-- The largest power of the size parameter allowed in a bounded term. -/
def M : Nat := 8

abbrev ZForm := List (Nat × Int)

/-- The value of a packed term: coefficient, power `key / KEY` of `s`, atom `key % KEY`. -/
def valueZ (s : ℚ) (A : Nat → ℚ) : ZForm → ℚ
  | [] => 0
  | t::f => (t.2:ℚ)*s^(t.1/KEY)*A (t.1%KEY)+valueZ s A f

/-- Adds `c` to the term with key `k`, cancelling it when it vanishes (any order of keys). -/
def insL (k : Nat) (c : Int) : ZForm → ZForm
  | [] => if c=0 then [] else [(k,c)]
  | (k',c')::r => if k.beq k' then (if c+c'=0 then r else (k,c+c')::r) else (k',c')::insL k c r

/-- Merge difference of two forms sorted by key (fuelled by the total length); exact cancellation
of equal keys when both are sorted, and the right value in any case. -/
def subF : Nat → ZForm → ZForm → ZForm
  | 0,_,_ => []
  | _+1,[],b => b.map (fun t => (t.1,-t.2))
  | _+1,a,[] => a
  | n+1,(k,c)::a,(k',c')::b =>
    if k.blt k' then (k,c)::subF n a ((k',c')::b)
    else if k'.blt k then (k',-c')::subF n ((k,c)::a) b
    else if c-c'=0 then subF n a b else (k,c-c')::subF n a b

def subZ (a b : ZForm) : ZForm := subF (a.length+b.length) a b

/-- Insertion by key. -/
def insS (t : Nat × Int) : ZForm → ZForm
  | [] => [t]
  | u::r => if t.1.ble u.1 then t::u::r else u::insS t r

def sortZ (f : ZForm) : ZForm := f.foldr insS []

def divZ (k : Nat) (f : ZForm) : Bool := f.all (fun t => (k*KEY).ble t.1)
def dropZ (k : Nat) (f : ZForm) : ZForm := f.map (fun t => (t.1-k*KEY,t.2))
/-- Every term has power at most `M`. -/
def degZ (f : ZForm) : Bool := f.all (fun t => t.1.blt ((M+1)*KEY))

def p65 (n : Nat) : Int := ((65^n : Nat) : Int)

/-- Interval product, as `RegisterProduct.productBox`. -/
def mulI (a b : Int × Int) : Int × Int :=
  (min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2)),
   max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2)))

/-! ## The integer copy of a chart -/

structure ZData where
  fx : ITree ZForm
  fy : ITree ZForm
  bz : ITree (Int × Int)
  dx : Nat
  dy : Nat
  db : Nat
  /-- Number of atoms with a box; atoms beyond have the zero box. -/
  n : Nat
  /-- Every atom of the forms is below `KEY`. -/
  ok : Bool
deriving DecidableEq

def ZData.X (z : ZData) (i : Nat) : ZForm := z.fx.get [] i
def ZData.Y (z : ZData) (i : Nat) : ZForm := z.fy.get [] i
/-- The integer box of an atom, scaled by `db`. -/
def ZData.box (z : ZData) (a : Nat) : Int × Int := if a.blt z.n then z.bz.get (0,0) a else (0,0)

/-- Box of `s^p * x` scaled by `65^M`, for `x` in `[l,h]`, `0 < s ≤ 1/65` and `p ≤ M`. -/
def winT (l h : Int) (p : Nat) : Int × Int :=
  if p=0 then (l*p65 M,h*p65 M) else (min 0 l*p65 (M-p),max 0 h*p65 (M-p))

/-- The box of a term scaled by `db * 65^M` (the term must have power at most `M`). -/
def boxT (z : ZData) (t : Nat × Int) : Int × Int :=
  winT (min (t.2*(z.box (t.1%KEY)).1) (t.2*(z.box (t.1%KEY)).2))
    (max (t.2*(z.box (t.1%KEY)).1) (t.2*(z.box (t.1%KEY)).2)) (t.1/KEY)

def boxZ (z : ZData) (f : ZForm) : Int × Int :=
  f.foldr (fun t acc => ((boxT z t).1+acc.1,(boxT z t).2+acc.2)) (0,0)

/-- Lower bound of `s^e * x` scaled by `65^E`, for `x ≥ lo`, `0 < s ≤ 1/65`, `e ≤ E`. -/
def lowT (lo : Int) (e E : Nat) : Int := if e=0 then lo*p65 E else min 0 lo*p65 (E-e)

/-- Certifies `c*d < a*b` for the values of the four forms, after removing the powers `h` of `s`. -/
def chk (z : ZData) (a b c d : ZForm) (h : Nat × Nat × Nat × Nat) : Bool :=
  divZ h.1 a && divZ h.2.1 b && divZ h.2.2.1 c && divZ h.2.2.2 d &&
  degZ (dropZ h.1 a) && degZ (dropZ h.2.1 b) && degZ (dropZ h.2.2.1 c) && degZ (dropZ h.2.2.2 d) &&
  (let U := mulI (boxZ z (dropZ h.1 a)) (boxZ z (dropZ h.2.1 b))
   let V := mulI (boxZ z (dropZ h.2.2.1 c)) (boxZ z (dropZ h.2.2.2 d))
   let e1 := h.1+h.2.1-min (h.1+h.2.1) (h.2.2.1+h.2.2.2)
   let e2 := h.2.2.1+h.2.2.2-min (h.1+h.2.1) (h.2.2.1+h.2.2.2)
   decide (0<lowT U.1 e1 (max e1 e2)+lowT (-V.2) e2 (max e1 e2)))

/-- The determinant points from base `0`, `1` or `2`: `det(w,g,c)=det(g,c,w)=det(c,w,g)`. -/
def rot (w g c : Nat × Nat) : Nat → (Nat × Nat) × (Nat × Nat) × (Nat × Nat)
  | 0 => (w,g,c)
  | 1 => (g,c,w)
  | _ => (c,w,g)

/-- Certifies `det(w,g,c) > 0` by a product comparison from the chosen base. -/
def prodOK (z : ZData) (w g c : Nat × Nat) (base : Nat) (h : Nat × Nat × Nat × Nat) : Bool :=
  chk z (subZ (z.X (rot w g c base).2.1.1) (z.X (rot w g c base).1.1))
    (subZ (z.Y (rot w g c base).2.2.2) (z.Y (rot w g c base).1.2))
    (subZ (z.Y (rot w g c base).2.1.2) (z.Y (rot w g c base).1.2))
    (subZ (z.X (rot w g c base).2.2.1) (z.X (rot w g c base).1.1)) h

/-- `prodOK` from base `0` with the points given by literal line indices, so that the kernel
shares the differences of the same lines across the checks of one declaration. -/
def prodL (z : ZData) (i0 j0 i1 j1 i2 j2 : Nat) (h : Nat × Nat × Nat × Nat) : Bool :=
  chk z (subZ (z.X i1) (z.X i0)) (subZ (z.Y j2) (z.Y j0)) (subZ (z.Y j1) (z.Y j0)) (subZ (z.X i2) (z.X i0)) h

/-! ## Expanded determinants over pairs of atoms -/

/-- Packed pair key: power, then the two atoms in increasing order. -/
def pkey (k₁ k₂ : Nat) : Nat :=
  (k₁/KEY+k₂/KEY)*(KEY*KEY)+(if (k₁%KEY).blt (k₂%KEY) then (k₁%KEY)*KEY+k₂%KEY else (k₂%KEY)*KEY+k₁%KEY)

def valueP (s : ℚ) (A : Nat → ℚ) : ZForm → ℚ
  | [] => 0
  | t::f => (t.2:ℚ)*s^(t.1/(KEY*KEY))*(A (t.1%(KEY*KEY)/KEY)*A (t.1%KEY))+valueP s A f

def insP (k : Nat) (c : Int) : ZForm → ZForm
  | [] => if c=0 then [] else [(k,c)]
  | (k',c')::r =>
    if k.blt k' then (if c=0 then (k',c')::r else (k,c)::(k',c')::r)
    else if k.beq k' then (if c+c'=0 then r else (k,c+c')::r) else (k',c')::insP k c r

/-- Adds `sgn * a * b` to `acc`, expanded over pairs of atoms. -/
def mulP (a b : ZForm) (sgn : Int) (acc : ZForm) : ZForm :=
  a.foldr (fun t acc => b.foldr (fun u acc => insP (pkey t.1 u.1) (sgn*t.2*u.2) acc) acc) acc

def detP (z : ZData) (w g c : Nat × Nat) : ZForm :=
  mulP (subZ (z.X g.1) (z.X w.1)) (subZ (z.Y c.2) (z.Y w.2)) 1
    (mulP (subZ (z.Y g.2) (z.Y w.2)) (subZ (z.X c.1) (z.X w.1)) (-1) [])

/-- Interval square, as `RegisterPoly.sqBox`. -/
def sqI (b : Int × Int) : Int × Int :=
  (if b.1≤0 ∧ 0≤b.2 then 0 else min (b.1*b.1) (b.2*b.2),max (b.1*b.1) (b.2*b.2))

/-- Box of a product of two atoms, as `RegisterPoly.B2`. -/
def pairI (z : ZData) (k : Nat) : Int × Int :=
  if (k%(KEY*KEY)/KEY).beq (k%KEY) then sqI (z.box (k%KEY)) else mulI (z.box (k%(KEY*KEY)/KEY)) (z.box (k%KEY))

def boxPT (z : ZData) (t : Nat × Int) : Int × Int :=
  winT (min (t.2*(pairI z t.1).1) (t.2*(pairI z t.1).2)) (max (t.2*(pairI z t.1).1) (t.2*(pairI z t.1).2))
    (t.1/(KEY*KEY))

def boxPZ (z : ZData) (f : ZForm) : Int × Int :=
  f.foldr (fun t acc => ((boxPT z t).1+acc.1,(boxPT z t).2+acc.2)) (0,0)

/-- Certifies `det(w,g,c) > 0` from the expanded determinant after removing `s^k`. -/
def polyOK (z : ZData) (w g c : Nat × Nat) (k : Nat) : Bool :=
  let f := detP z w g c
  f.all (fun t => (k*(KEY*KEY)).ble t.1 && t.1.blt ((k+M+1)*(KEY*KEY))) &&
  decide (0<(boxPZ z (f.map (fun t => (t.1-k*(KEY*KEY),t.2)))).1)

/-- Structurally vanishing determinant: two equal points, or three points on one grid line. -/
def lineZ (w g c : Nat × Nat) : Bool :=
  (g.1==c.1 && g.2==c.2) || (g.1==w.1 && g.2==w.2) || (c.1==w.1 && c.2==w.2) ||
    (w.1==g.1 && g.1==c.1) || (w.2==g.2 && g.2==c.2)

/-- Certifies `det(w,g,c) = 0` identically. -/
def zeroOK (z : ZData) (w g c : Nat × Nat) : Bool := lineZ w g c || (detP z w g c).isEmpty

/-- The least power of `s` in a form (linear keys `q`, pair keys `q*q`). -/
def minPow (q : Nat) : ZForm → Nat
  | [] => 0
  | t::f => f.foldr (fun u m => min (u.1/q) m) (t.1/q)

/-- Product check from a base, removing the least power of `s` from each factor. -/
def prodAuto (z : ZData) (w g c : Nat × Nat) (base : Nat) : Bool :=
  let p := rot w g c base
  let a := subZ (z.X p.2.1.1) (z.X p.1.1)
  let b := subZ (z.Y p.2.2.2) (z.Y p.1.2)
  let c' := subZ (z.Y p.2.1.2) (z.Y p.1.2)
  let d := subZ (z.X p.2.2.1) (z.X p.1.1)
  chk z a b c' d (minPow KEY a,minPow KEY b,minPow KEY c',minPow KEY d)

/-- Certifies `det(w,g,c) > 0` without a hint: product checks from the three bases, then the
expanded determinant after removing its least power of `s`. -/
def autoOK (z : ZData) (w g c : Nat × Nat) : Bool :=
  prodAuto z w g c 1 || prodAuto z w g c 2 || prodAuto z w g c 0 ||
    polyOK z w g c (minPow (KEY*KEY) (detP z w g c))

/-! ## The integer copy computed from a rational chart -/

def lcmL (l : List Nat) : Nat := l.foldr Nat.lcm 1

/-- Integer coefficient of a rational one at scale `d` (exact when the denominator divides `d`). -/
def scaleQ (d : Nat) (c : ℚ) : Int := c.num*((d/c.den : Nat) : Int)

def toZ0 (d : Nat) (f : Form) : ZForm := f.map (fun t => (t.1.1*KEY+t.1.2,scaleQ d t.2))

/-- The integer form, sorted by key. -/
def toZ (d : Nat) (f : Form) : ZForm := sortZ (toZ0 d f)

def formsDen (fs : List Form) : Nat := lcmL (fs.flatMap (fun f => f.map (fun t => t.2.den)))
def boxesDen (bs : List Box) : Nat := lcmL (bs.flatMap (fun b => [b.lo.den,b.hi.den]))

/-- Atom boxes of `RegisterTable.atomBox bs`: atom `0` is the constant one, atom `i+1` is `bs[i]`. -/
def ZData.ofChart (fx fy : List Form) (bs : List Box) : ZData where
  fx := ITree.ofList (fx.map (toZ (formsDen fx)))
  fy := ITree.ofList (fy.map (toZ (formsDen fy)))
  bz := ITree.ofList (((1:Int)*((boxesDen bs : Nat) : Int),(1:Int)*((boxesDen bs : Nat) : Int))::
    bs.map (fun b => (scaleQ (boxesDen bs) b.lo,scaleQ (boxesDen bs) b.hi)))
  dx := formsDen fx
  dy := formsDen fy
  db := boxesDen bs
  n := bs.length+1
  ok := (fx++fy).all (fun f => f.all (fun t => t.1.2.blt KEY))

/-! ## Soundness: linear forms -/

theorem valueZ_cons (s : ℚ) (A : Nat → ℚ) (t : Nat × Int) (f : ZForm) :
    valueZ s A (t::f)=(t.2:ℚ)*s^(t.1/KEY)*A (t.1%KEY)+valueZ s A f := rfl

theorem valueZ_neg (s : ℚ) (A : Nat → ℚ) (b : ZForm) :
    valueZ s A (b.map (fun t => (t.1,-t.2)))=-valueZ s A b := by
  induction b with
  | nil => simp [valueZ]
  | cons t b ih => simp only [List.map_cons,valueZ_cons,ih]; push_cast; ring

theorem insL_value (s : ℚ) (A : Nat → ℚ) (k : Nat) (c : Int) (f : ZForm) :
    valueZ s A (insL k c f)=(c:ℚ)*s^(k/KEY)*A (k%KEY)+valueZ s A f := by
  induction f with
  | nil => unfold insL; split <;> simp_all [valueZ]
  | cons t f ih =>
    obtain ⟨k',c'⟩ := t
    unfold insL
    split
    · next hk =>
      have e : k=k' := by simpa using hk
      subst e
      split
      · next hz =>
        have : (c:ℚ)=-c' := by exact_mod_cast (eq_neg_of_add_eq_zero_left hz)
        rw [valueZ_cons,this]; ring
      · rw [valueZ_cons,valueZ_cons]; push_cast; ring
    · rw [valueZ_cons,valueZ_cons,ih]; ring

theorem subF_value (s : ℚ) (A : Nat → ℚ) :
    ∀ n (a b : ZForm), a.length+b.length≤n → valueZ s A (subF n a b)=valueZ s A a-valueZ s A b
  | 0,a,b,h => by
    have ha : a=[] := List.eq_nil_of_length_eq_zero (by omega)
    have hb : b=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha hb; simp [subF,valueZ]
  | n+1,[],b,_ => by simp [subF,valueZ_neg,valueZ]
  | n+1,t::a,[],_ => by simp [subF,valueZ]
  | n+1,(k,c)::a,(k',c')::b,h => by
    simp only [List.length_cons] at h
    simp only [subF]
    by_cases h1 : k.blt k'=true
    · simp only [h1,ite_true,valueZ_cons]
      rw [subF_value s A n a _ (by simp only [List.length_cons]; omega),valueZ_cons]; ring
    · simp only [h1,ite_false,Bool.false_eq_true]
      by_cases h2 : k'.blt k=true
      · simp only [h2,ite_true,valueZ_cons]
        rw [subF_value s A n _ b (by simp only [List.length_cons]; omega),valueZ_cons]; push_cast; ring
      · simp only [h2,ite_false,Bool.false_eq_true]
        have e : k=k' := by
          simp only [Nat.blt_eq,not_lt] at h1 h2; omega
        subst e
        split
        · next hz =>
          rw [subF_value s A n a b (by omega),valueZ_cons,valueZ_cons]
          have : (c:ℚ)=c' := by exact_mod_cast (sub_eq_zero.mp hz)
          rw [this]; ring
        · rw [valueZ_cons,subF_value s A n a b (by omega),valueZ_cons,valueZ_cons]; push_cast; ring

theorem subZ_value (s : ℚ) (A : Nat → ℚ) (a b : ZForm) :
    valueZ s A (subZ a b)=valueZ s A a-valueZ s A b := subF_value s A _ a b le_rfl

theorem insS_value (s : ℚ) (A : Nat → ℚ) (t : Nat × Int) (f : ZForm) :
    valueZ s A (insS t f)=valueZ s A (t::f) := by
  induction f with
  | nil => rfl
  | cons u r ih =>
    unfold insS
    split
    · rfl
    · rw [valueZ_cons,ih,valueZ_cons,valueZ_cons,valueZ_cons]; ring

theorem sortZ_value (s : ℚ) (A : Nat → ℚ) (f : ZForm) : valueZ s A (sortZ f)=valueZ s A f := by
  unfold sortZ
  induction f with
  | nil => rfl
  | cons t f ih => rw [List.foldr_cons,insS_value,valueZ_cons,ih,valueZ_cons]

private theorem key_drop {k key : Nat} (h : k*KEY≤key) :
    (key-k*KEY)/KEY=key/KEY-k ∧ (key-k*KEY)%KEY=key%KEY := by
  unfold KEY at *; omega

theorem dropZ_value {k : Nat} {f : ZForm} (h : divZ k f=true) (s : ℚ) (A : Nat → ℚ) :
    valueZ s A f=s^k*valueZ s A (dropZ k f) := by
  induction f with
  | nil => simp [dropZ,valueZ]
  | cons t f ih =>
    simp only [divZ,List.all_cons,Bool.and_eq_true,Nat.ble_eq] at h
    obtain ⟨ht,hf⟩ := h
    obtain ⟨e1,e2⟩ := key_drop ht
    have hk : k≤t.1/KEY := by unfold KEY at *; omega
    simp only [dropZ,List.map_cons,valueZ_cons] at ih ⊢
    rw [ih hf,e1,e2]
    have : s^(t.1/KEY)=s^k*s^(t.1/KEY-k) := by rw [←pow_add]; congr 1; omega
    rw [this]; ring

/-- The atom boxes of the integer copy enclose the scaled atom values. -/
def ZBounds (z : ZData) (A : Nat → ℚ) : Prop :=
  ∀ a, ((z.box a).1:ℚ)≤A a*z.db ∧ A a*z.db≤((z.box a).2:ℚ)

private theorem p65_cast (n : Nat) : ((p65 n : Int) : ℚ)=65^n := by simp [p65]

private theorem int_mul_bound {c l h : Int} {x : ℚ} (hl : (l:ℚ)≤x) (hh : x≤(h:ℚ)) :
    ((min (c*l) (c*h) : Int) : ℚ)≤c*x ∧ c*x≤((max (c*l) (c*h) : Int) : ℚ) := by
  push_cast
  rcases le_total 0 (c:ℚ) with hp|hn
  · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_left hl hp),(mul_le_mul_of_nonneg_left hh hp).trans (le_max_right ..)⟩
  · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hh hn),(mul_le_mul_of_nonpos_left hl hn).trans (le_max_left ..)⟩

private theorem pow_window {s : ℚ} (hs : 0<s) (hu : s≤1/65) {p : Nat} (hp : p≤M) :
    0≤s^p*65^M ∧ s^p*65^M≤65^(M-p) := by
  refine ⟨by positivity,?_⟩
  have h1 : s^p≤(1/65)^p := pow_le_pow_left₀ hs.le hu p
  have h2 : (65:ℚ)^M=65^p*65^(M-p) := by rw [←pow_add]; congr 1; omega
  calc s^p*65^M≤(1/65)^p*65^M := mul_le_mul_of_nonneg_right h1 (by positivity)
    _=65^(M-p) := by rw [h2,one_div_pow,←mul_assoc,one_div,inv_mul_cancel₀ (by positivity),one_mul]

private theorem scaled_window {l h x y Y : ℚ} (hl : l≤x) (hh : x≤h) (y0 : 0≤y) (yY : y≤Y) :
    min 0 l*Y≤x*y ∧ x*y≤max 0 h*Y := by
  have Y0 : 0≤Y := y0.trans yY
  constructor
  · rcases le_total 0 x with px|nx
    · exact (mul_nonpos_of_nonpos_of_nonneg (min_le_left ..) Y0).trans (mul_nonneg px y0)
    · calc min 0 l*Y≤l*Y := mul_le_mul_of_nonneg_right (min_le_right ..) Y0
        _≤x*Y := mul_le_mul_of_nonneg_right hl Y0
        _≤x*y := mul_le_mul_of_nonpos_left yY nx
  · rcases le_total 0 x with px|nx
    · calc x*y≤x*Y := mul_le_mul_of_nonneg_left yY px
        _≤h*Y := mul_le_mul_of_nonneg_right hh Y0
        _≤max 0 h*Y := mul_le_mul_of_nonneg_right (le_max_right ..) Y0
    · exact (mul_nonpos_of_nonpos_of_nonneg nx y0).trans (mul_nonneg (le_max_left ..) Y0)

/-- Bound of one scaled term from a box of `x`, where the term is `s^p * x`. -/
theorem winT_bound {s : ℚ} (hs : 0<s) (hu : s≤1/65) {p : Nat} (hp : p≤M) {l h : Int} {x : ℚ}
    (hl : (l:ℚ)≤x) (hh : x≤(h:ℚ)) :
    ((winT l h p).1:ℚ)≤x*(s^p*65^M) ∧ x*(s^p*65^M)≤((winT l h p).2:ℚ) := by
  unfold winT
  by_cases p0 : p=0
  · subst p0
    simp only [ite_true,pow_zero,one_mul]; push_cast [p65_cast]
    exact ⟨mul_le_mul_of_nonneg_right hl (by positivity),mul_le_mul_of_nonneg_right hh (by positivity)⟩
  · simp only [p0,ite_false]; push_cast [p65_cast]
    obtain ⟨y0,yY⟩ := pow_window hs hu hp
    exact scaled_window hl hh y0 yY

theorem boxT_bound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) {s : ℚ} (hs : 0<s) (hu : s≤1/65)
    (t : Nat × Int) (hp : t.1/KEY≤M) :
    ((boxT z t).1:ℚ)≤(t.2:ℚ)*s^(t.1/KEY)*A (t.1%KEY)*(z.db*65^M) ∧
      (t.2:ℚ)*s^(t.1/KEY)*A (t.1%KEY)*(z.db*65^M)≤((boxT z t).2:ℚ) := by
  have c := int_mul_bound (c:=t.2) (hb (t.1%KEY)).1 (hb (t.1%KEY)).2
  have e : (t.2:ℚ)*s^(t.1/KEY)*A (t.1%KEY)*(z.db*65^M)=(t.2*(A (t.1%KEY)*z.db))*(s^(t.1/KEY)*65^M) := by ring
  rw [e]
  exact winT_bound hs hu hp c.1 c.2

theorem boxZ_bound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) {s : ℚ} (hs : 0<s) (hu : s≤1/65)
    (f : ZForm) (hd : degZ f=true) :
    ((boxZ z f).1:ℚ)≤valueZ s A f*(z.db*65^M) ∧ valueZ s A f*(z.db*65^M)≤((boxZ z f).2:ℚ) := by
  induction f with
  | nil => simp [boxZ,valueZ]
  | cons t f ih =>
    simp only [degZ,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hd
    have hp : t.1/KEY≤M := by unfold KEY M at *; omega
    have bt := boxT_bound hb hs hu t hp
    have bf := ih (by simpa [degZ] using hd.2)
    simp only [boxZ,List.foldr_cons] at bf ⊢
    rw [valueZ_cons]; push_cast
    constructor <;> nlinarith [bt.1,bt.2,bf.1,bf.2]

theorem mulI_bound {a b : Int × Int} {u v : ℚ} (A : (a.1:ℚ)≤u ∧ u≤a.2) (B : (b.1:ℚ)≤v ∧ v≤b.2) :
    ((mulI a b).1:ℚ)≤u*v ∧ u*v≤((mulI a b).2:ℚ) := by
  have := RegisterProduct.product_bound (a:=⟨a.1,a.2⟩) (b:=⟨b.1,b.2⟩) A B
  simp only [RegisterProduct.productBox] at this
  simp only [mulI]; push_cast
  exact this

private theorem lowT_le {lo : Int} {x s : ℚ} (hs : 0<s) (hu : s≤1/65) {e E : Nat} (he : e≤E)
    (hx : (lo:ℚ)≤x) : ((lowT lo e E : Int) : ℚ)≤65^E*(s^e*x) := by
  unfold lowT
  by_cases e0 : e=0
  · subst e0; simp only [ite_true,pow_zero,one_mul]; push_cast [p65_cast]; nlinarith [pow_pos (show (0:ℚ)<65 by norm_num) E]
  · simp only [e0,ite_false]; push_cast [p65_cast]
    have hE : (65:ℚ)^E=65^e*65^(E-e) := by rw [←pow_add]; congr 1; omega
    have se : s^e≤(1/65)^e := pow_le_pow_left₀ hs.le hu e
    have sp : 0<s^e := pow_pos hs e
    rcases le_total 0 x with px|nx
    · have : min 0 (lo:ℚ)*65^(E-e)≤0 := mul_nonpos_of_nonpos_of_nonneg (min_le_left ..) (by positivity)
      exact this.trans (by positivity)
    · have lneg : (lo:ℚ)≤0 := hx.trans nx
      rw [min_eq_right lneg]
      have k : 65^E*(s^e*x)≥65^E*((1/65)^e*x) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonpos_right se nx
      have k2 : (65:ℚ)^E*((1/65)^e*x)=65^(E-e)*x := by
        rw [hE,one_div_pow]; field_simp
      rw [k2] at k
      nlinarith [pow_pos (show (0:ℚ)<65 by norm_num) (E-e)]

theorem chk_sound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) (hdb : 0<z.db) {s : ℚ} (hs : 0<s)
    (hu : s≤1/65) {a b c d : ZForm} {h : Nat × Nat × Nat × Nat} (pass : chk z a b c d h=true) :
    valueZ s A c*valueZ s A d<valueZ s A a*valueZ s A b := by
  obtain ⟨i,j,k,l⟩ := h
  simp only [chk,Bool.and_eq_true,decide_eq_true_eq] at pass
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨da,db_⟩,dc⟩,dd⟩,ga⟩,gb⟩,gc⟩,gd⟩,good⟩ := pass
  have dbq : (0:ℚ)<z.db := by exact_mod_cast hdb
  have Spos : (0:ℚ)<z.db*65^M := by positivity
  have Ba := boxZ_bound hb hs hu _ ga
  have Bb := boxZ_bound hb hs hu _ gb
  have Bc := boxZ_bound hb hs hu _ gc
  have Bd := boxZ_bound hb hs hu _ gd
  have U := mulI_bound Ba Bb
  have V := mulI_bound Bc Bd
  rw [dropZ_value da s A,dropZ_value db_ s A,dropZ_value dc s A,dropZ_value dd s A]
  generalize (z.db:ℚ)*65^M=S at Spos Ba Bb Bc Bd U V
  generalize valueZ s A (dropZ i a)=a' at Ba U ⊢
  generalize valueZ s A (dropZ j b)=b' at Bb U ⊢
  generalize valueZ s A (dropZ k c)=c' at Bc V ⊢
  generalize valueZ s A (dropZ l d)=d' at Bd V ⊢
  generalize mulI (boxZ z (dropZ i a)) (boxZ z (dropZ j b))=U' at U good
  generalize mulI (boxZ z (dropZ k c)) (boxZ z (dropZ l d))=V' at V good
  generalize hm : min (i+j) (k+l)=m at good
  have L1 := lowT_le (e:=i+j-m) (E:=max (i+j-m) (k+l-m)) hs hu (le_max_left _ _) U.1
  have L2 := lowT_le (e:=k+l-m) (E:=max (i+j-m) (k+l-m)) (x:=-(c'*S*(d'*S))) (lo:=-V'.2) hs hu
    (le_max_right _ _) (by push_cast; linarith [V.2])
  have g' : (0:ℚ)<(lowT U'.1 (i+j-m) (max (i+j-m) (k+l-m)) : ℚ)+(lowT (-V'.2) (k+l-m) (max (i+j-m) (k+l-m)) : ℚ) := by
    exact_mod_cast good
  have h65 : (0:ℚ)<65^(max (i+j-m) (k+l-m)) := by positivity
  have key : 0<s^(i+j-m)*(a'*S*(b'*S))-s^(k+l-m)*(c'*S*(d'*S)) := by
    by_contra hneg
    push Not at hneg
    have := mul_le_mul_of_nonneg_left hneg h65.le
    nlinarith
  have hij : s^(i+j)=s^m*s^(i+j-m) := by rw [←pow_add]; congr 1; omega
  have hkl : s^(k+l)=s^m*s^(k+l-m) := by rw [←pow_add]; congr 1; omega
  have sm : 0<s^m := pow_pos hs m
  have e : (s^i*a'*(s^j*b')-s^k*c'*(s^l*d'))*(S*S)=s^m*(s^(i+j-m)*(a'*S*(b'*S))-s^(k+l-m)*(c'*S*(d'*S))) := by
    rw [show s^i*a'*(s^j*b')=s^(i+j)*(a'*b') by rw [pow_add]; ring,
      show s^k*c'*(s^l*d')=s^(k+l)*(c'*d') by rw [pow_add]; ring,hij,hkl]; ring
  have pos : 0<(s^i*a'*(s^j*b')-s^k*c'*(s^l*d'))*(S*S) := by rw [e]; exact mul_pos sm key
  have := (mul_pos_iff_of_pos_right (by positivity : (0:ℚ)<S*S)).mp pos
  linarith

/-! ## Soundness: determinants -/

/-- The integer determinant `det(w,g,c)` of the copy. -/
def DZ (z : ZData) (s : ℚ) (A : Nat → ℚ) (w g c : Nat × Nat) : ℚ :=
  (valueZ s A (z.X g.1)-valueZ s A (z.X w.1))*(valueZ s A (z.Y c.2)-valueZ s A (z.Y w.2))-
    (valueZ s A (z.Y g.2)-valueZ s A (z.Y w.2))*(valueZ s A (z.X c.1)-valueZ s A (z.X w.1))

theorem DZ_rot (z : ZData) (s : ℚ) (A : Nat → ℚ) (w g c : Nat × Nat) (base : Nat) :
    DZ z s A (rot w g c base).1 (rot w g c base).2.1 (rot w g c base).2.2=DZ z s A w g c := by
  rcases base with _|_|_ <;> simp only [rot,DZ] <;> ring

theorem prodOK_sound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) (hdb : 0<z.db) {s : ℚ} (hs : 0<s)
    (hu : s≤1/65) {w g c : Nat × Nat} {base : Nat} {h : Nat × Nat × Nat × Nat}
    (pass : prodOK z w g c base h=true) : 0<DZ z s A w g c := by
  have := chk_sound hb hdb hs hu pass
  simp only [subZ_value] at this
  rw [←DZ_rot z s A w g c base]
  simp only [DZ]
  linarith

theorem prodL_sound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) (hdb : 0<z.db) {s : ℚ} (hs : 0<s)
    (hu : s≤1/65) {i0 j0 i1 j1 i2 j2 : Nat} {h : Nat × Nat × Nat × Nat}
    (pass : prodL z i0 j0 i1 j1 i2 j2 h=true) : 0<DZ z s A (i0,j0) (i1,j1) (i2,j2) :=
  prodOK_sound hb hdb hs hu (base:=0) (h:=h) pass

private theorem pkey_decode (k₁ k₂ : Nat) :
    pkey k₁ k₂/(KEY*KEY)=k₁/KEY+k₂/KEY ∧
      ((pkey k₁ k₂%(KEY*KEY)/KEY=k₁%KEY ∧ pkey k₁ k₂%KEY=k₂%KEY) ∨
       (pkey k₁ k₂%(KEY*KEY)/KEY=k₂%KEY ∧ pkey k₁ k₂%KEY=k₁%KEY)) := by
  unfold pkey
  split
  · next h => simp only [Nat.blt_eq] at h; unfold KEY at *; omega
  · next h => simp only [Nat.blt_eq] at h; unfold KEY at *; omega

private theorem pkey_mono (s : ℚ) (A : Nat → ℚ) (k₁ k₂ : Nat) :
    s^(pkey k₁ k₂/(KEY*KEY))*(A (pkey k₁ k₂%(KEY*KEY)/KEY)*A (pkey k₁ k₂%KEY))=
      s^(k₁/KEY)*A (k₁%KEY)*(s^(k₂/KEY)*A (k₂%KEY)) := by
  obtain ⟨e,h|h⟩ := pkey_decode k₁ k₂
  · rw [e,h.1,h.2,pow_add]; ring
  · rw [e,h.1,h.2,pow_add]; ring

theorem valueP_cons (s : ℚ) (A : Nat → ℚ) (t : Nat × Int) (f : ZForm) :
    valueP s A (t::f)=(t.2:ℚ)*s^(t.1/(KEY*KEY))*(A (t.1%(KEY*KEY)/KEY)*A (t.1%KEY))+valueP s A f := rfl

theorem insP_value (s : ℚ) (A : Nat → ℚ) (k : Nat) (c : Int) (f : ZForm) :
    valueP s A (insP k c f)=(c:ℚ)*s^(k/(KEY*KEY))*(A (k%(KEY*KEY)/KEY)*A (k%KEY))+valueP s A f := by
  induction f with
  | nil => unfold insP; split <;> simp_all [valueP]
  | cons t f ih =>
    obtain ⟨k',c'⟩ := t
    unfold insP
    split
    · split
      · next hc => simp [hc,valueP_cons]
      · simp only [valueP_cons]
    · split
      · next hk =>
        have e : k=k' := by simpa using hk
        subst e
        split
        · next hz =>
          have : (c:ℚ)=-c' := by exact_mod_cast (eq_neg_of_add_eq_zero_left hz)
          rw [valueP_cons,this]; ring
        · rw [valueP_cons,valueP_cons]; push_cast; ring
      · rw [valueP_cons,valueP_cons,ih]; ring

theorem mulT_value (s : ℚ) (A : Nat → ℚ) (t : Nat × Int) (sgn : Int) (b acc : ZForm) :
    valueP s A (b.foldr (fun u acc => insP (pkey t.1 u.1) (sgn*t.2*u.2) acc) acc)=
      sgn*((t.2:ℚ)*s^(t.1/KEY)*A (t.1%KEY))*valueZ s A b+valueP s A acc := by
  induction b with
  | nil => simp [valueZ]
  | cons u b ih =>
    rw [List.foldr_cons,insP_value,ih,valueZ_cons]
    have := pkey_mono s A t.1 u.1
    push_cast
    linear_combination ((sgn:ℚ)*t.2*u.2)*this

theorem mulP_value (s : ℚ) (A : Nat → ℚ) (a b : ZForm) (sgn : Int) (acc : ZForm) :
    valueP s A (mulP a b sgn acc)=sgn*valueZ s A a*valueZ s A b+valueP s A acc := by
  unfold mulP
  induction a generalizing acc with
  | nil => simp [valueZ]
  | cons t a ih =>
    rw [List.foldr_cons,mulT_value,ih,valueZ_cons]; ring

theorem detP_value (z : ZData) (s : ℚ) (A : Nat → ℚ) (w g c : Nat × Nat) :
    valueP s A (detP z w g c)=DZ z s A w g c := by
  simp only [detP,mulP_value,subZ_value,DZ,valueP]; push_cast; ring

theorem zeroOK_sound {z : ZData} {s : ℚ} {A : Nat → ℚ} {w g c : Nat × Nat} (pass : zeroOK z w g c=true) :
    DZ z s A w g c=0 := by
  obtain ⟨w1,w2⟩ := w; obtain ⟨g1,g2⟩ := g; obtain ⟨c1,c2⟩ := c
  simp only [zeroOK,lineZ,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at pass
  rcases pass with ((((⟨rfl,rfl⟩|⟨rfl,rfl⟩)|⟨rfl,rfl⟩)|⟨rfl,rfl⟩)|⟨rfl,rfl⟩)|pass
  all_goals try (simp only [DZ]; ring1)
  have e : detP z (w1,w2) (g1,g2) (c1,c2)=[] := List.isEmpty_iff.mp pass
  rw [←detP_value,e]; rfl

private theorem sqI_bound {b : Int × Int} {x : ℚ} (hl : (b.1:ℚ)≤x) (hh : x≤(b.2:ℚ)) :
    ((sqI b).1:ℚ)≤x*x ∧ x*x≤((sqI b).2:ℚ) := by
  obtain ⟨l,h⟩ := b
  simp only [sqI] at hl hh ⊢
  constructor
  · split
    · push_cast; exact mul_self_nonneg x
    · next hz =>
      push_cast
      rcases le_or_gt 0 l with pl|nl
      · have plq : (0:ℚ)≤l := by exact_mod_cast pl
        exact (min_le_left ..).trans (mul_le_mul hl hl plq (plq.trans hl))
      · have nh : h<0 := by
          by_contra c; exact hz ⟨nl.le,le_of_not_gt c⟩
        have nhq : (h:ℚ)<0 := by exact_mod_cast nh
        have ha : x≤0 := hh.trans nhq.le
        exact (min_le_right ..).trans (by nlinarith)
  · push_cast
    rcases le_total 0 x with pa|na
    · exact (mul_le_mul hh hh pa (pa.trans hh)).trans (le_max_right ..)
    · exact (by nlinarith : x*x≤l*l).trans (le_max_left ..)

private theorem pairI_bound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) (k : Nat) :
    ((pairI z k).1:ℚ)≤A (k%(KEY*KEY)/KEY)*z.db*(A (k%KEY)*z.db) ∧
      A (k%(KEY*KEY)/KEY)*z.db*(A (k%KEY)*z.db)≤((pairI z k).2:ℚ) := by
  unfold pairI
  split
  · next he =>
    have e : k%(KEY*KEY)/KEY=k%KEY := by simpa using he
    rw [e]
    exact sqI_bound (hb _).1 (hb _).2
  · exact mulI_bound (hb _) (hb _)

theorem boxPT_bound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) {s : ℚ} (hs : 0<s) (hu : s≤1/65)
    (t : Nat × Int) (hp : t.1/(KEY*KEY)≤M) :
    ((boxPT z t).1:ℚ)≤(t.2:ℚ)*s^(t.1/(KEY*KEY))*(A (t.1%(KEY*KEY)/KEY)*A (t.1%KEY))*(z.db*z.db*65^M) ∧
      (t.2:ℚ)*s^(t.1/(KEY*KEY))*(A (t.1%(KEY*KEY)/KEY)*A (t.1%KEY))*(z.db*z.db*65^M)≤((boxPT z t).2:ℚ) := by
  have m := pairI_bound hb t.1
  have c := int_mul_bound (c:=t.2) m.1 m.2
  have e : (t.2:ℚ)*s^(t.1/(KEY*KEY))*(A (t.1%(KEY*KEY)/KEY)*A (t.1%KEY))*(z.db*z.db*65^M)=
      (t.2*(A (t.1%(KEY*KEY)/KEY)*z.db*(A (t.1%KEY)*z.db)))*(s^(t.1/(KEY*KEY))*65^M) := by ring
  rw [e]
  exact winT_bound hs hu hp c.1 c.2

theorem boxPZ_bound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) {s : ℚ} (hs : 0<s) (hu : s≤1/65)
    (f : ZForm) (hd : ∀ t∈f, t.1/(KEY*KEY)≤M) :
    ((boxPZ z f).1:ℚ)≤valueP s A f*(z.db*z.db*65^M) := by
  induction f with
  | nil => simp [boxPZ,valueP]
  | cons t f ih =>
    have bt := boxPT_bound hb hs hu t (hd t (by simp))
    have bf := ih (fun u hu => hd u (by simp [hu]))
    simp only [boxPZ,List.foldr_cons] at bf ⊢
    rw [valueP_cons]; push_cast
    nlinarith [bt.1,bf]

private theorem pair_drop {k key : Nat} (h : k*(KEY*KEY)≤key) :
    (key-k*(KEY*KEY))/(KEY*KEY)=key/(KEY*KEY)-k ∧ (key-k*(KEY*KEY))%(KEY*KEY)/KEY=key%(KEY*KEY)/KEY ∧
      (key-k*(KEY*KEY))%KEY=key%KEY := by
  unfold KEY at *; omega

theorem polyOK_sound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) (hdb : 0<z.db) {s : ℚ} (hs : 0<s)
    (hu : s≤1/65) {w g c : Nat × Nat} {k : Nat} (pass : polyOK z w g c k=true) : 0<DZ z s A w g c := by
  rw [←detP_value]
  simp only [polyOK,Bool.and_eq_true,List.all_eq_true,Nat.ble_eq,Nat.blt_eq,decide_eq_true_eq] at pass
  obtain ⟨keys,good⟩ := pass
  generalize detP z w g c=f at keys good ⊢
  have drop : valueP s A f=s^k*valueP s A (f.map (fun t => (t.1-k*(KEY*KEY),t.2))) := by
    clear good
    induction f with
    | nil => simp [valueP]
    | cons t f ih =>
      have ht := keys t (by simp)
      obtain ⟨e1,e2,e3⟩ := pair_drop ht.1
      have hk : k≤t.1/(KEY*KEY) := by unfold KEY at *; omega
      simp only [List.map_cons,valueP_cons]
      rw [ih (fun u hu => keys u (by simp [hu])),e1,e2,e3]
      have : s^(t.1/(KEY*KEY))=s^k*s^(t.1/(KEY*KEY)-k) := by rw [←pow_add]; congr 1; omega
      rw [this]; ring
  have deg : ∀ t∈f.map (fun t => (t.1-k*(KEY*KEY),t.2)), t.1/(KEY*KEY)≤M := by
    intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨u,hu,rfl⟩ := ht
    have := keys u hu
    unfold KEY M at *; omega
  have B := boxPZ_bound hb hs hu _ deg
  have dbq : (0:ℚ)<z.db := by exact_mod_cast hdb
  have pos : (0:ℚ)<valueP s A (f.map (fun t => (t.1-k*(KEY*KEY),t.2)))*(z.db*z.db*65^M) :=
    lt_of_lt_of_le (by exact_mod_cast good) B
  have := (mul_pos_iff_of_pos_right (by positivity : (0:ℚ)<z.db*z.db*65^M)).mp pos
  rw [drop]; exact mul_pos (pow_pos hs k) this

theorem prodAuto_sound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) (hdb : 0<z.db) {s : ℚ} (hs : 0<s)
    (hu : s≤1/65) {w g c : Nat × Nat} {base : Nat} (pass : prodAuto z w g c base=true) :
    0<DZ z s A w g c := prodOK_sound hb hdb hs hu (base:=base) (h:=_) pass

theorem autoOK_sound {z : ZData} {A : Nat → ℚ} (hb : ZBounds z A) (hdb : 0<z.db) {s : ℚ} (hs : 0<s)
    (hu : s≤1/65) {w g c : Nat × Nat} (pass : autoOK z w g c=true) : 0<DZ z s A w g c := by
  simp only [autoOK,Bool.or_eq_true] at pass
  rcases pass with ((h|h)|h)|h
  · exact prodAuto_sound hb hdb hs hu h
  · exact prodAuto_sound hb hdb hs hu h
  · exact prodAuto_sound hb hdb hs hu h
  · exact polyOK_sound hb hdb hs hu h

/-! ## The integer copy of a rational chart -/

theorem dvd_lcmL {x : Nat} : ∀ {l : List Nat}, x∈l → x∣lcmL l
  | [],h => by simp at h
  | y::l,h => by
    simp only [List.mem_cons] at h
    rcases h with rfl|h
    · exact Nat.dvd_lcm_left _ _
    · exact (dvd_lcmL h).trans (Nat.dvd_lcm_right _ _)

theorem lcmL_pos : ∀ {l : List Nat}, (∀ x∈l, 0<x) → 0<lcmL l
  | [],_ => by simp [lcmL]
  | y::l,h => Nat.lcm_pos (h y (by simp)) (lcmL_pos (fun x hx => h x (by simp [hx])))

theorem scaleQ_cast {d : Nat} {c : ℚ} (h : c.den∣d) : ((scaleQ d c : Int) : ℚ)=c*d := by
  obtain ⟨k,rfl⟩ := h
  have hd : (c.den:ℚ)≠0 := by exact_mod_cast c.den_ne_zero
  have : c.den*k/c.den=k := Nat.mul_div_cancel_left k c.den_pos
  simp only [scaleQ,this]
  push_cast
  rw [←mul_assoc,Rat.mul_den_eq_num]

theorem toZ0_value (s : ℚ) (A : Nat → ℚ) {d : Nat} (f : Form) (hd : ∀ t∈f, t.2.den∣d)
    (ha : ∀ t∈f, t.1.2<KEY) : valueZ s A (toZ0 d f)=d*value s A f := by
  induction f with
  | nil => simp [toZ0,valueZ,value]
  | cons t f ih =>
    have k1 : (t.1.1*KEY+t.1.2)/KEY=t.1.1 := by have := ha t (by simp); unfold KEY at *; omega
    have k2 : (t.1.1*KEY+t.1.2)%KEY=t.1.2 := by have := ha t (by simp); unfold KEY at *; omega
    have ih' := ih (fun u hu => hd u (by simp [hu])) (fun u hu => ha u (by simp [hu]))
    simp only [toZ0,List.map_cons] at ih' ⊢
    rw [valueZ_cons,ih',k1,k2,scaleQ_cast (hd t (by simp)),value,valTerm]; ring

theorem toZ_value (s : ℚ) (A : Nat → ℚ) {d : Nat} (f : Form) (hd : ∀ t∈f, t.2.den∣d)
    (ha : ∀ t∈f, t.1.2<KEY) : valueZ s A (toZ d f)=d*value s A f := by
  rw [toZ,sortZ_value,toZ0_value s A f hd ha]

theorem ofChart_X (fx fy : List Form) (bs : List Box) (i : Nat) :
    (ZData.ofChart fx fy bs).X i=toZ (formsDen fx) (fx.getD i []) := by
  simp only [ZData.X,ZData.ofChart,get_ofList]
  rw [show ([]:ZForm)=toZ (formsDen fx) [] from rfl,List.getD_map]

theorem ofChart_Y (fx fy : List Form) (bs : List Box) (i : Nat) :
    (ZData.ofChart fx fy bs).Y i=toZ (formsDen fy) (fy.getD i []) := by
  simp only [ZData.Y,ZData.ofChart,get_ofList]
  rw [show ([]:ZForm)=toZ (formsDen fy) [] from rfl,List.getD_map]

private theorem den_mem {fs : List Form} {f : Form} (hf : f∈fs) {t : RegisterForm.Term} (ht : t∈f) :
    t.2.den∣formsDen fs := by
  apply dvd_lcmL
  simp only [List.mem_flatMap,List.mem_map]
  exact ⟨f,hf,t,ht,rfl⟩

private theorem getD_mem {f : Form} {fs : List Form} {i : Nat} (ht : f=fs.getD i []) :
    f=[] ∨ f∈fs := by
  rw [ht,List.getD_eq_getElem?_getD]
  cases h : fs[i]? with
  | none => left; rfl
  | some v => right; exact List.mem_of_getElem? h

theorem ofChart_xvalue (fx fy : List Form) (bs : List Box) (hok : (ZData.ofChart fx fy bs).ok=true)
    (s : ℚ) (A : Nat → ℚ) (i : Nat) :
    valueZ s A ((ZData.ofChart fx fy bs).X i)=(ZData.ofChart fx fy bs).dx*value s A (fx.getD i []) := by
  rw [ofChart_X]
  simp only [ZData.ofChart,List.all_append,Bool.and_eq_true,List.all_eq_true,Nat.blt_eq] at hok
  rcases getD_mem (fs:=fx) (i:=i) rfl with h|h
  · rw [h]; simp [toZ,toZ0,sortZ,valueZ,value]
  · exact toZ_value s A _ (fun t ht => den_mem h ht) (fun t ht => hok.1 _ h t ht)

theorem ofChart_yvalue (fx fy : List Form) (bs : List Box) (hok : (ZData.ofChart fx fy bs).ok=true)
    (s : ℚ) (A : Nat → ℚ) (i : Nat) :
    valueZ s A ((ZData.ofChart fx fy bs).Y i)=(ZData.ofChart fx fy bs).dy*value s A (fy.getD i []) := by
  rw [ofChart_Y]
  simp only [ZData.ofChart,List.all_append,Bool.and_eq_true,List.all_eq_true,Nat.blt_eq] at hok
  rcases getD_mem (fs:=fy) (i:=i) rfl with h|h
  · rw [h]; simp [toZ,toZ0,sortZ,valueZ,value]
  · exact toZ_value s A _ (fun t ht => den_mem h ht) (fun t ht => hok.2 _ h t ht)

theorem ofChart_pos (fx fy : List Form) (bs : List Box) :
    0<(ZData.ofChart fx fy bs).dx ∧ 0<(ZData.ofChart fx fy bs).dy ∧ 0<(ZData.ofChart fx fy bs).db := by
  simp only [ZData.ofChart,formsDen,boxesDen]
  refine ⟨lcmL_pos ?_,lcmL_pos ?_,lcmL_pos ?_⟩
  · intro x hx
    simp only [List.mem_flatMap,List.mem_map] at hx
    obtain ⟨_,_,t,_,rfl⟩ := hx
    exact t.2.den_pos
  · intro x hx
    simp only [List.mem_flatMap,List.mem_map] at hx
    obtain ⟨_,_,t,_,rfl⟩ := hx
    exact t.2.den_pos
  · intro x hx
    simp only [List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hx
    obtain ⟨b,_,h⟩ := hx
    rcases h with rfl|rfl
    · exact b.lo.den_pos
    · exact b.hi.den_pos

theorem ofChart_bounds (fx fy : List Form) (bs : List Box) {A : Nat → ℚ}
    (h : Bounds (RegisterTable.atomBox bs) A) : ZBounds (ZData.ofChart fx fy bs) A := by
  intro a
  have dbq : (0:ℚ)≤boxesDen bs := by positivity
  simp only [ZData.box,ZData.ofChart]
  by_cases ha : a.blt (bs.length+1)=true
  · simp only [ha,↓reduceIte,get_ofList]
    simp only [Nat.blt_eq] at ha
    cases a with
    | zero =>
      have := h 0
      simp only [RegisterTable.atomBox] at this
      have e : A 0=1 := le_antisymm this.2 this.1
      simp [e]
    | succ i =>
      have hi : i<bs.length := by omega
      have b := h (i+1)
      simp only [RegisterTable.atomBox,getBox,List.getElem?_eq_getElem hi,Option.getD_some] at b
      simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi]
      simp only [Option.map_some,Option.getD_some]
      have dlo : bs[i].lo.den∣boxesDen bs := by
        apply dvd_lcmL; simp only [List.mem_flatMap]; exact ⟨bs[i],List.getElem_mem hi,by simp⟩
      have dhi : bs[i].hi.den∣boxesDen bs := by
        apply dvd_lcmL; simp only [List.mem_flatMap]; exact ⟨bs[i],List.getElem_mem hi,by simp⟩
      rw [scaleQ_cast dlo,scaleQ_cast dhi]
      exact ⟨mul_le_mul_of_nonneg_right b.1 dbq,mul_le_mul_of_nonneg_right b.2 dbq⟩
  · have ha' : a.blt (bs.length+1)=false := Bool.eq_false_iff.mpr ha
    simp only [ha',Bool.false_eq_true,↓reduceIte]
    simp only [Nat.blt_eq,not_lt] at ha
    cases a with
    | zero => omega
    | succ i =>
      have hi : i ≥ bs.length := by omega
      have b := h (i+1)
      simp only [RegisterTable.atomBox,getBox,List.getElem?_eq_none hi,Option.getD_none,zeroBox] at b
      have e : A (i+1)=0 := le_antisymm b.2 b.1
      simp [e]

end ArtGallery.Orthogonal.BoundaryPoint.ZSign
end
