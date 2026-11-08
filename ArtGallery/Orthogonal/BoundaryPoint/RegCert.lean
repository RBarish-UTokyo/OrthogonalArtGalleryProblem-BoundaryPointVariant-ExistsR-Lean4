module

public import ArtGallery.Orthogonal.BoundaryPoint.KronCert
public import ArtGallery.Orthogonal.BoundaryPoint.RegisterOrder

/-! # Closed forms of executed registers

A certificate lists registers of a program together with polynomial closed
forms `N/D` in three real variables. Each entry is checked against the program
row of its register and the closed forms of the row's arguments by exact
polynomial identities, verified at a Kronecker point. Denominators stay nonzero
through explicit cofactors: a new denominator times its cofactor is a product of
earlier nonzero denominators or numerators of nonzero registers. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegCert
open MarginCert LinearRegister RegisterTable RegisterOrder KronCert

/-- A closed form `N/D` with the cofactor `g` of its denominator. -/
structure Entry where
  reg : Nat
  N : Ex
  D : Ex
  g : Ex

/-- Closed forms of program inputs: input `k` equals `N/D`, with `D` a nonzero constant. -/
abbrev Inputs := List (Nat × Ex × Int)

def c3 (c : Int) : P3 := [[[c]]]

def auto (e : Ex) : Bool := e.auto

theorem auto_sound {e : Ex} (h : auto e=true) (x y z : ℝ) : e.ev x y z=0 := Ex.sound h x y z

/-- Check one entry with program row `o`, given the closed forms of earlier registers. -/
def okOp (bs : List Box) (ins : Inputs) (known : List (Nat × Ex × Ex)) (e : Entry) : Op → Bool
  | .plus a b =>
    match (known.find? (·.1=e.reg+1+a)).map (·.2),(known.find? (·.1=e.reg+1+b)).map (·.2) with
    | some (Na,Da),some (Nb,Db) =>
      Ex.auto2 (.sub (.mul (.mul e.N Da) Db) (.mul (.add (.mul Na Db) (.mul Nb Da)) e.D))
      (.sub (.mul e.D e.g) (.mul Da Db))
    | _,_ => false
  | .times a b =>
    match (known.find? (·.1=e.reg+1+a)).map (·.2),(known.find? (·.1=e.reg+1+b)).map (·.2) with
    | some (Na,Da),some (Nb,Db) =>
      Ex.auto2 (.sub (.mul (.mul e.N Da) Db) (.mul (.mul Na Nb) e.D))
      (.sub (.mul e.D e.g) (.mul Da Db))
    | _,_ => false
  | .neg a =>
    match (known.find? (·.1=e.reg+1+a)).map (·.2) with
    | some (Na,Da) => Ex.auto2 (.add (.mul e.N Da) (.mul Na e.D))
        (.sub (.mul e.D e.g) Da)
    | _ => false
  | .recip a =>
    match (known.find? (·.1=e.reg+1+a)).map (·.2) with
    | some (Na,Da) =>
      (decide (0<(getBox bs (e.reg+1+a)).lo) || decide ((getBox bs (e.reg+1+a)).hi<0)) &&
      Ex.auto2 (.sub (.mul e.N Na) (.mul Da e.D)) (.sub (.mul e.D e.g) Na)
    | _ => false
  | .lit q =>
    Ex.auto2 (.sub (.mul e.N (.lit (c3 q.den))) (.mul (.lit (c3 q.num)) e.D))
      (.sub (.mul e.D e.g) (.lit (c3 q.den)))
  | .input k =>
    match ins.find? (·.1=k) with
    | some (_,Q,d) => decide (d≠0) && Ex.auto2 (.sub (.mul e.N (.lit (c3 d))) (.mul Q e.D))
        (.sub (.mul e.D e.g) (.lit (c3 d)))
    | none => false
  | _ => false

def Entry.ok (rows : List Row) (bs : List Box) (ins : Inputs) (known : List (Nat × Ex × Ex)) (e : Entry) : Bool :=
  match rows[e.reg]? with
  | some r => okOp bs ins known e r.op
  | none => false

def check (rows : List Row) (bs : List Box) (ins : Inputs) : List (Nat × Ex × Ex) → List Entry → Bool
  | _,[] => true
  | known,e::es => e.ok rows bs ins known && check rows bs ins ((e.reg,e.N,e.D)::known) es

/-- The real value of register `j` matches the closed form at the point `(x,y,z)`. -/
def Holds (xs : List ℚ) (x y z : ℝ) (j : Nat) (N D : Ex) : Prop :=
  ((getRat xs j : ℚ) : ℝ)*D.ev x y z=N.ev x y z ∧ D.ev x y z≠0

section Steps
variable {x xa xb N D g Na Da Nb Db : ℝ}

private theorem cof_ne (h : D*g-Da*Db=0) (na : Da≠0) (nb : Db≠0) : D≠0 := by
  intro z; rw [z] at h; exact mul_ne_zero na nb (by linarith)

theorem step_plus (ha : xa*Da=Na) (hb : xb*Db=Nb) (na : Da≠0) (nb : Db≠0) (hx : x=xa+xb)
    (id : N*Da*Db-(Na*Db+Nb*Da)*D=0) (cof : D*g-Da*Db=0) : x*D=N ∧ D≠0 := by
  refine ⟨?_,cof_ne cof na nb⟩
  have : Da*Db*(N-x*D)=0 := by linear_combination id - D*Db*ha - D*Da*hb - D*Da*Db*hx
  rcases mul_eq_zero.mp this with h|h
  · exact absurd h (mul_ne_zero na nb)
  · linarith

theorem step_times (ha : xa*Da=Na) (hb : xb*Db=Nb) (na : Da≠0) (nb : Db≠0) (hx : x=xa*xb)
    (id : N*Da*Db-Na*Nb*D=0) (cof : D*g-Da*Db=0) : x*D=N ∧ D≠0 := by
  refine ⟨?_,cof_ne cof na nb⟩
  have : Da*Db*(N-x*D)=0 := by linear_combination id - D*xb*Db*ha - D*Na*hb - D*Da*Db*hx
  rcases mul_eq_zero.mp this with h|h
  · exact absurd h (mul_ne_zero na nb)
  · linarith

theorem step_neg (ha : xa*Da=Na) (na : Da≠0) (hx : x=-xa) (id : N*Da+Na*D=0) (cof : D*g-Da=0) :
    x*D=N ∧ D≠0 := by
  refine ⟨?_,fun z => by rw [z] at cof; exact na (by linarith)⟩
  have : Da*(N-x*D)=0 := by linear_combination id + D*ha - D*Da*hx
  rcases mul_eq_zero.mp this with h|h
  · exact absurd h na
  · linarith

theorem step_recip (ha : xa*Da=Na) (na : Da≠0) (nz : xa≠0) (hx : x=xa⁻¹) (id : N*Na-Da*D=0)
    (cof : D*g-Na=0) : x*D=N ∧ D≠0 := by
  have nN : Na≠0 := by rw [←ha]; exact mul_ne_zero nz na
  refine ⟨?_,fun z => by rw [z] at cof; exact nN (by linarith)⟩
  have : Da*(N*xa-D)=0 := by linear_combination id + N*ha
  rcases mul_eq_zero.mp this with h|h
  · exact absurd h na
  · rw [hx]; field_simp; linarith

theorem step_const {q : ℚ} (hx : x=q) (id : N*q.den-q.num*D=0) (cof : D*g-q.den=0) : x*D=N ∧ D≠0 := by
  have hd : (q.den:ℝ)≠0 := by exact_mod_cast q.den_nz
  refine ⟨?_,fun z => by rw [z] at cof; exact hd (by linarith)⟩
  have hq : (q:ℝ)=q.num/q.den := by exact_mod_cast (Rat.num_div_den q).symm
  rw [hx,hq]; field_simp; linarith

theorem step_input {d : ℝ} (hd : d≠0) {Q : ℝ} (hin : x*d=Q) (id : N*d-Q*D=0) (cof : D*g-d=0) :
    x*D=N ∧ D≠0 := by
  refine ⟨?_,fun z => by rw [z] at cof; exact hd (by linarith)⟩
  have : d*(N-x*D)=0 := by linear_combination id - D*hin
  rcases mul_eq_zero.mp this with h|h
  · exact absurd h hd
  · linarith

end Steps

private theorem find_holds {xs : List ℚ} {x y z : ℝ} {known : List (Nat × Ex × Ex)}
    (hk : ∀ t∈known, Holds xs x y z t.1 t.2.1 t.2.2) {j : Nat} {N D : Ex}
    (h : (known.find? (·.1=j)).map (·.2)=some (N,D)) : Holds xs x y z j N D := by
  obtain ⟨t,ht,e⟩ := Option.map_eq_some_iff.mp h
  have mem := List.mem_of_find?_eq_some ht
  have tj : t.1=j := by simpa using List.find?_some ht
  obtain ⟨t1,t2,t3⟩ := t
  simp only at tj e
  subst tj; cases e
  exact hk _ mem

private theorem drop_get (xs : List ℚ) (i a : Nat) : getRat (xs.drop (i+1)) a=getRat xs (i+1+a) := by
  simp [getRat,List.getElem?_drop]

private theorem ev0 {e : Ex} (h : auto e=true) (x y z : ℝ) : e.ev x y z=0 := Ex.sound h x y z

theorem entry_sound {args xs : List ℚ} {rows : List Row} (run : Ledger args rows xs) {bs : List Box}
    (bounds : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    {ins : Inputs} {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    {known : List (Nat × Ex × Ex)} (hk : ∀ t∈known, Holds xs x y z t.1 t.2.1 t.2.2)
    {e : Entry} (h : e.ok rows bs ins known=true) : Holds xs x y z e.reg e.N e.D := by
  unfold Entry.ok at h
  cases hrow : rows[e.reg]? with
  | none => simp [hrow] at h
  | some r =>
    have val := original run hrow
    simp only [hrow] at h
    unfold Holds
    cases hop : r.op with
    | plus a b =>
      rw [hop] at h val; simp only [okOp] at h; simp only [Op.rat,drop_get] at val
      split at h
      · next Na Da Nb Db ha hb =>
        have e1 := (Ex.auto2_sound h).1 x y z; have e2 := (Ex.auto2_sound h).2 x y z
        simp only [Ex.ev] at e1 e2
        obtain ⟨la,na⟩ := find_holds hk ha
        obtain ⟨lb,nb⟩ := find_holds hk hb
        exact step_plus la lb na nb (by rw [val]; push_cast; ring) e1 e2
      · simp at h
    | times a b =>
      rw [hop] at h val; simp only [okOp] at h; simp only [Op.rat,drop_get] at val
      split at h
      · next Na Da Nb Db ha hb =>
        have e1 := (Ex.auto2_sound h).1 x y z; have e2 := (Ex.auto2_sound h).2 x y z
        simp only [Ex.ev] at e1 e2
        obtain ⟨la,na⟩ := find_holds hk ha
        obtain ⟨lb,nb⟩ := find_holds hk hb
        exact step_times la lb na nb (by rw [val]; push_cast; ring) e1 e2
      · simp at h
    | neg a =>
      rw [hop] at h val; simp only [okOp] at h; simp only [Op.rat,drop_get] at val
      split at h
      · next Na Da ha =>
        have e1 := (Ex.auto2_sound h).1 x y z; have e2 := (Ex.auto2_sound h).2 x y z
        simp only [Ex.ev] at e1 e2
        obtain ⟨la,na⟩ := find_holds hk ha
        exact step_neg la na (by rw [val]; push_cast; ring) e1 e2
      · simp at h
    | recip a =>
      rw [hop] at h val; simp only [okOp] at h; simp only [Op.rat,drop_get] at val
      split at h
      · next Na Da ha =>
        simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
        obtain ⟨away,h12⟩ := h
        have e1 := (Ex.auto2_sound h12).1 x y z; have e2 := (Ex.auto2_sound h12).2 x y z
        simp only [Ex.ev] at e1 e2
        obtain ⟨la,na⟩ := find_holds hk ha
        have nz : getRat xs (e.reg+1+a)≠0 := by
          have b := bounds (e.reg+1+a)
          rcases away with l|u
          · exact ne_of_gt (lt_of_lt_of_le l b.1)
          · exact ne_of_lt (lt_of_le_of_lt b.2 u)
        exact step_recip la na (by exact_mod_cast nz) (by rw [val]; push_cast; ring) e1 e2
      · simp at h
    | lit q =>
      rw [hop] at h val; simp only [okOp] at h; simp only [Op.rat] at val
      have e1 := (Ex.auto2_sound h).1 x y z; have e2 := (Ex.auto2_sound h).2 x y z
      simp only [Ex.ev,ev3,ev2,ev1,c3] at e1 e2
      push_cast at e1 e2
      exact step_const (q:=q) (by rw [val]) (by linarith) (by linarith)
    | input k =>
      rw [hop] at h val; simp only [okOp] at h; simp only [Op.rat] at val
      split at h
      · next t Q d hf =>
        simp only [Bool.and_eq_true,decide_eq_true_eq] at h
        obtain ⟨dn,h12⟩ := h
        have e1 := (Ex.auto2_sound h12).1 x y z; have e2 := (Ex.auto2_sound h12).2 x y z
        simp only [Ex.ev,ev3,ev2,ev1,c3] at e1 e2
        push_cast at e1 e2
        have mem := List.mem_of_find?_eq_some hf
        have tk : t=k := by simpa using List.find?_some hf
        subst tk
        have hi := hin _ _ _ mem
        rw [←val] at hi
        exact step_input (g:=e.g.ev x y z) (d:=(d:ℝ)) (by exact_mod_cast dn) hi (by linarith) (by linarith)
      · simp at h
    | absVal a => rw [hop] at h; simp [okOp] at h
    | larger a b => rw [hop] at h; simp [okOp] at h

theorem check_sound {args xs : List ℚ} {rows : List Row} (run : Ledger args rows xs) {bs : List Box}
    (bounds : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    {ins : Inputs} {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q) :
    ∀ (es : List Entry) (known : List (Nat × Ex × Ex)), (∀ t∈known, Holds xs x y z t.1 t.2.1 t.2.2) →
      check rows bs ins known es=true → ∀ e∈es, Holds xs x y z e.reg e.N e.D
  | [],_,_,_ => by simp
  | e::es,known,hk,h => by
    simp only [check,Bool.and_eq_true] at h
    have he := entry_sound run bounds hin hk h.1
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · apply check_sound run bounds hin es _ _ h.2 f hf
      intro t ht
      rcases List.mem_cons.mp ht with rfl|ht
      · exact he
      · exact hk t ht

end ArtGallery.Orthogonal.BoundaryPoint.RegCert
end
