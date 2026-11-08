module

public import ArtGallery.Orthogonal.BoundaryPoint.RegBranch

/-! # Register certificates through branch rows

A chain of steps: ordinary `RegCert` entries, and branch steps for `larger` and
`absVal` rows whose branch is fixed on the parameter box by certified signs. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegChain
open MarginCert LinearRegister RegisterTable KronCert PolyBox RegCert RegBranch

inductive Step
  | plain (e : RegCert.Entry)
  | larger (reg a b : Nat) (first : Bool) (σa σb : Int) (M : Ex)
  | abs (reg a : Nat) (σ : Int) (M : Ex)

def look (known : List (Nat × Ex × Ex)) (j : Nat) : Option (Ex × Ex) := (known.find? (·.1=j)).map (·.2)

/-- The closed form produced by a step, if it checks. -/
def Step.out (c bl bh : ℚ) (rows : List Row) (bs : List Box) (ins : Inputs) (known : List (Nat × Ex × Ex)) :
    Step → Option (Nat × Ex × Ex)
  | .plain e => if e.ok rows bs ins known then some (e.reg,e.N,e.D) else none
  | .larger reg a b first σa σb M =>
    match (rows[reg]?).map Row.op,look known (reg+1+a),look known (reg+1+b) with
    | some (.larger a' b'),some (Na,Da),some (Nb,Db) =>
      if a'=a ∧ b'=b then
        if first then (if RegBranch.larger c bl bh Na Da Nb Db M σa σb then some (reg,Na,Da) else none)
        else (if RegBranch.larger c bl bh Nb Db Na Da M σb σa then some (reg,Nb,Db) else none)
      else none
    | _,_,_ => none
  | .abs reg a σ M =>
    match (rows[reg]?).map Row.op,look known (reg+1+a) with
    | some (.absVal a'),some (N,D) =>
      if a'=a ∧ absSign c bl bh N D M σ then some (reg,esc σ N,D) else none
    | _,_ => none

def run (c bl bh : ℚ) (rows : List Row) (bs : List Box) (ins : Inputs) :
    List (Nat × Ex × Ex) → List Step → Option (List (Nat × Ex × Ex))
  | known,[] => some known
  | known,st::sts => match st.out c bl bh rows bs ins known with
    | some t => run c bl bh rows bs ins (t::known) sts
    | none => none

theorem look_holds {xs : List ℚ} {x y z : ℝ} {known : List (Nat × Ex × Ex)}
    (hk : ∀ t∈known, Holds xs x y z t.1 t.2.1 t.2.2) {j : Nat} {N D : Ex}
    (h : look known j=some (N,D)) : Holds xs x y z j N D := by
  unfold look at h
  obtain ⟨t,ht,e⟩ := Option.map_eq_some_iff.mp h
  have mem := List.mem_of_find?_eq_some ht
  have tj : t.1=j := by simpa using List.find?_some ht
  obtain ⟨t1,t2,t3⟩ := t
  simp only at tj e
  subst tj; cases e
  exact hk _ mem

theorem out_sound {args xs : List ℚ} {rows : List Row} (run' : Ledger args rows xs) {bs : List Box}
    (bounds : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    {ins : Inputs} {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    {c bl bh : ℚ} (B : Box c bl bh x y z)
    {known : List (Nat × Ex × Ex)} (hk : ∀ t∈known, Holds xs x y z t.1 t.2.1 t.2.2)
    {st : Step} {t : Nat × Ex × Ex} (h : st.out c bl bh rows bs ins known=some t) :
    Holds xs x y z t.1 t.2.1 t.2.2 := by
  cases st with
  | plain e =>
    simp only [Step.out] at h
    split at h
    · next ok => cases h; exact entry_sound run' bounds hin hk ok
    · cases h
  | larger reg a b first σa σb M =>
    simp only [Step.out] at h
    split at h
    · next a' b' Na Da Nb Db hop ha hb =>
      split at h
      · next hab =>
        obtain ⟨rfl,rfl⟩ := hab
        have Ha := look_holds hk ha
        have Hb := look_holds hk hb
        cases first
        · simp only [Bool.false_eq_true,ite_false] at h
          split at h
          · next cert => cases h; exact holds_larger' run' hop Ha Hb B cert
          · cases h
        · simp only [ite_true] at h
          split at h
          · next cert => cases h; exact holds_larger run' hop Ha Hb B cert
          · cases h
      · cases h
    · cases h
  | abs reg a σ M =>
    simp only [Step.out] at h
    split at h
    · next a' N D hop ha =>
      split at h
      · next cond =>
        obtain ⟨rfl,cert⟩ := cond
        cases h
        exact holds_abs run' hop (look_holds hk ha) B cert
      · cases h
    · cases h

theorem run_sound {args xs : List ℚ} {rows : List Row} (run' : Ledger args rows xs) {bs : List Box}
    (bounds : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    {ins : Inputs} {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    {c bl bh : ℚ} (B : Box c bl bh x y z) :
    ∀ (sts : List Step) (known out : List (Nat × Ex × Ex)), (∀ t∈known, Holds xs x y z t.1 t.2.1 t.2.2) →
      run c bl bh rows bs ins known sts=some out → ∀ t∈out, Holds xs x y z t.1 t.2.1 t.2.2
  | [],known,out,hk,h => by simp only [run,Option.some.injEq] at h; subst h; exact hk
  | st::sts,known,out,hk,h => by
    simp only [run] at h
    split at h
    · next t ht =>
      apply run_sound run' bounds hin B sts (t::known) out _ h
      intro u hu
      rcases List.mem_cons.mp hu with rfl|hu
      · exact out_sound run' bounds hin B hk ht
      · exact hk u hu
    · cases h

/-- The chain runs and its output contains every listed closed form. -/
def runTops (c bl bh : ℚ) (rows : List Row) (bs : List Box) (ins : Inputs) (steps : List Step)
    (tops : List (Nat × Ex × Ex)) : Bool :=
  match run c bl bh rows bs ins [] steps with
  | some out => tops.all (fun t => out.contains t)
  | none => false

theorem runTops_sound {args xs : List ℚ} {rows : List Row} (run' : Ledger args rows xs) {bs : List Box}
    (bounds : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    {ins : Inputs} {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    {c bl bh : ℚ} (B : Box c bl bh x y z) {steps : List Step} {tops : List (Nat × Ex × Ex)}
    (h : runTops c bl bh rows bs ins steps tops=true) : ∀ t∈tops, Holds xs x y z t.1 t.2.1 t.2.2 := by
  unfold runTops at h
  split at h
  · next out hout =>
    intro t ht
    have := List.all_eq_true.mp h t ht
    exact run_sound run' bounds hin B steps [] out (by simp) hout t (List.contains_iff_mem.mp this)
  · cases h

end ArtGallery.Orthogonal.BoundaryPoint.RegChain
end
