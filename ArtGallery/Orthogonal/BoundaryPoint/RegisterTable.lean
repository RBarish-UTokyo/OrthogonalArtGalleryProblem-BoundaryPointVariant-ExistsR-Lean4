module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterOp

/-! # Local row checks and soundness for the whole physical register stack
Register numbers run backwards from the last executed row. Opaque rows denote
the original computed number exactly. A claimed form is checked against the
original instruction and the already executed rows that it reads. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterTable
open MarginCert LinearRegister RegisterForm RegisterOp

inductive Entry where
  | raw
  | claim (form : Form) (rule : Rule)

def form (entries : List Entry) (i : Nat) : Form := match entries[i]? with
  | none => []
  | some .raw => atom (i+1)
  | some (.claim f _) => f

def atomBox (bs : List Box) : Nat → Box
  | 0 => ⟨1,1⟩
  | i+1 => getBox bs i

def atomVal (xs : List ℚ) : Nat → ℚ
  | 0 => 1
  | i+1 => getRat xs i

def rowOK (rs : List Row) (bs : List Box) (cache : List Entry) (i : Nat) : Bool :=
  match cache[i]? with
  | some .raw => true
  | some (.claim f how) =>
    (rs[i]?.bind (fun r => applyRule (atomBox bs) (fun j => form cache (i+1+j)) (getBox bs i) r.op how)).any (same f)
  | none => false

def block (rs : List Row) (bs : List Box) (cache : List Entry) (offset count : Nat) :=
  (List.range' offset count).all (rowOK rs bs cache)

def Verified (rs : List Row) (bs : List Box) (cache : List Entry) (lo hi : Nat) :=
  ∀ i : Nat, lo ≤ i → i < hi → rowOK rs bs cache i = true

theorem block_ok {rs bs cache a c} (h : block rs bs cache a c=true) : Verified rs bs cache a (a+c) := by
  intro i lo hi
  exact List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨lo,hi⟩)

theorem join {rs bs cache a b c} (l : Verified rs bs cache a b) (r : Verified rs bs cache b c) :
    Verified rs bs cache a c := by
  intro i lo hi
  rcases lt_or_ge i b with h|h
  · exact l i lo h
  · exact r i h hi

theorem lengths {args rows xs} (h : Ledger args rows xs) : rows.length=xs.length := by
  induction h <;> simp_all

theorem original {args rows xs} (data : Ledger args rows xs) {i : Nat} {r : Row} (h : rows[i]?=some r) :
    getRat xs i=r.op.rat args (xs.drop (i+1)) := by
  induction data generalizing i with
  | nil => simp at h
  | cons a _ ih =>
    cases i with
    | zero => have eq : a=r := by simpa using h
              subst r; simp [getRat]
    | succ j => simpa only [getRat,List.getElem?_cons_succ,List.drop_succ_cons] using ih (by simpa only [List.getElem?_cons_succ] using h)

theorem drop_lookup (xs : List ℚ) (i j : Nat) : getRat (xs.drop (i+1)) j=getRat xs (i+1+j) := by
  simp [getRat,List.getElem?_drop]

private theorem any_iff {α : Type} {o : Option α} {p : α → Bool} (h : o.any p=true) :
    ∃ a,o=some a ∧ p a=true := by cases o <;> simp_all

theorem atom_bound {bs xs} (h : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi) :
    Bounds (atomBox bs) (atomVal xs) := by
  intro i; cases i with
  | zero => exact ⟨le_refl _,le_refl _⟩
  | succ i => exact h i

theorem model {args rs xs} (data : Ledger args rs xs) {bs : List Box}
    (bounds : ∀ i,(getBox bs i).lo≤getRat xs i ∧ getRat xs i≤(getBox bs i).hi)
    (hs : 0<getRat args 0) (hu : getRat args 0≤cap) {cache : List Entry} (size : cache.length=rs.length)
    (all : Verified rs bs cache 0 rs.length) (i : Nat) :
    value (getRat args 0) (atomVal xs) (form cache i)=getRat xs i := by
  have rawLen := lengths data
  suffices H : ∀ k j,rs.length≤j+k → value (getRat args 0) (atomVal xs) (form cache j)=getRat xs j from H _ i (Nat.le_add_left ..)
  intro k
  induction k with
  | zero =>
    intro j hj
    have endC : cache.length≤j := by omega
    have endX : xs.length≤j := by omega
    simp [form,getRat,List.getElem?_eq_none endC,List.getElem?_eq_none endX,value]
  | succ k ih =>
    intro j hj
    by_cases inRange : j<rs.length
    · have ok := all j (Nat.zero_le _) inRange
      have inside : j < cache.length := by omega
      obtain ⟨e,he⟩ : ∃ e, cache[j]? = some e := ⟨cache[j],List.getElem?_eq_getElem inside⟩
      cases e with
      | raw =>
        simp only [form,he,atom,value,valTerm,atomVal,pow_zero,one_mul,add_zero]
      | claim claimed how =>
        have hCert : (rs[j]?.bind (fun r => applyRule (atomBox bs) (fun u => form cache (j+1+u))
          (getBox bs j) r.op how)).any (same claimed)=true := by simpa only [rowOK,he] using ok
        obtain ⟨f,found,eq⟩ := any_iff hCert
        obtain ⟨r,op,checked⟩ := Option.bind_eq_some_iff.mp found
        have instruction := original data op
        have identity (t : Nat) : value (getRat args 0) (atomVal xs) (form cache (j+1+t))=getRat (xs.drop (j+1)) t := by
          rw [drop_lookup]; exact ih _ (by omega)
        have h := RegisterOp.sound (atom_bound bounds) rfl hs hu _ identity (getBox bs j) r.op
          (instruction ▸ bounds j) how checked
        rw [form,he,same_value eq, h,←instruction]
    · have endC : cache.length≤j := by omega
      have endX : xs.length≤j := by omega
      simp [form,getRat,List.getElem?_eq_none endC,List.getElem?_eq_none endX,value]

def affineNegative (rows : List Row) (bs : List Box) (i : Nat) : Bool :=
  decide ((getBox bs i).hi<0) || (read 8 rows i).any (fun f => decide (f.1≤0 ∧ f.2<0))

def negative (rows : List Row) (bs : List Box) (i : Nat) := match rows[i]? with
  | some ⟨.larger a b,_,_⟩ => affineNegative rows bs (i+1+a) && affineNegative rows bs (i+1+b)
  | _ => affineNegative rows bs i

private theorem affine_neg {args rows xs} (run : Ledger args rows xs) (hs : 0<getRat args 0) {bs : List Box}
    (bound : ∀ i,getRat xs i≤(getBox bs i).hi) {i : Nat} (h : affineNegative rows bs i=true) : getRat xs i<0 := by
  rcases (show (getBox bs i).hi<0 ∨ _ from (by simpa only [affineNegative,Bool.or_eq_true,decide_eq_true_eq] using h)) with a|b
  · exact (bound i).trans_lt a
  · obtain ⟨f,hf,test⟩ := any_iff b
    obtain ⟨lo,strict⟩ := of_decide_eq_true test
    rw [read_value run 8 i hf,val]
    linarith [mul_neg_of_neg_of_pos strict hs]

theorem negative_sound {args rows xs} (run : Ledger args rows xs) (hs : 0<getRat args 0) {bs : List Box}
    (bound : ∀ i,getRat xs i≤(getBox bs i).hi) {i : Nat} (h : negative rows bs i=true) : getRat xs i<0 := by
  unfold negative at h
  split at h
  next a b r flag row =>
    rw [original run row,Op.rat,drop_lookup,drop_lookup]
    have pair : affineNegative rows bs (i+1+a)=true ∧ affineNegative rows bs (i+1+b)=true := by simpa only [Bool.and_eq_true] using h
    exact max_lt (affine_neg run hs bound pair.1) (affine_neg run hs bound pair.2)
  next => exact affine_neg run hs bound h

end ArtGallery.Orthogonal.BoundaryPoint.RegisterTable
end
