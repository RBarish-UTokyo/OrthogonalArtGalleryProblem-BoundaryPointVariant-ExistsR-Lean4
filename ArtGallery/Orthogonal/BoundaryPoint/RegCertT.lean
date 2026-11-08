module

public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.ZSign

/-! # Register certificates with fast lookups

`RegCert.check` and `RegChain.Step.out` read the program rows and register boxes from lists, which
the kernel walks one cell at a time; a step of a long program spends most of its check walking to
its register. The same checks with the rows and boxes given as lookup functions agree with the
list-based ones (`checkT_eq`, `outT_eq`), so a certificate may be decided with the rows and boxes
read from balanced trees. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegCertT
open MarginCert LinearRegister RegisterTable KronCert PolyBox RegCert RegBranch RegChain

/-- `RegCert.okOp` with the register boxes given by `B`. -/
def okOpT (B : Nat → Box) (ins : Inputs) (known : List (Nat × Ex × Ex)) (e : RegCert.Entry) : Op → Bool
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
      (decide (0<(B (e.reg+1+a)).lo) || decide ((B (e.reg+1+a)).hi<0)) &&
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

theorem okOpT_eq (bs : List Box) (ins : Inputs) (known : List (Nat × Ex × Ex)) (e : RegCert.Entry) (o : Op) :
    okOpT (getBox bs) ins known e o=okOp bs ins known e o := by
  cases o <;> rfl

def okT (R : Nat → Option Row) (B : Nat → Box) (ins : Inputs) (known : List (Nat × Ex × Ex))
    (e : RegCert.Entry) : Bool :=
  match R e.reg with
  | some r => okOpT B ins known e r.op
  | none => false

theorem okT_eq (rows : List Row) (bs : List Box) (ins : Inputs) (known : List (Nat × Ex × Ex)) (e : RegCert.Entry) :
    okT (fun i => rows[i]?) (getBox bs) ins known e=e.ok rows bs ins known := by
  unfold okT Entry.ok
  show (match rows[e.reg]? with | some r => okOpT (getBox bs) ins known e r.op | none => false)=_
  cases rows[e.reg]? with
  | none => rfl
  | some r => exact okOpT_eq bs ins known e r.op

def checkT (R : Nat → Option Row) (B : Nat → Box) (ins : Inputs) : List (Nat × Ex × Ex) → List RegCert.Entry → Bool
  | _,[] => true
  | known,e::es => okT R B ins known e && checkT R B ins ((e.reg,e.N,e.D)::known) es

theorem checkT_eq (rows : List Row) (bs : List Box) (ins : Inputs) :
    ∀ (known : List (Nat × Ex × Ex)) (es : List RegCert.Entry),
      checkT (fun i => rows[i]?) (getBox bs) ins known es=check rows bs ins known es
  | _,[] => rfl
  | known,e::es => by
    simp only [checkT,check,okT_eq,checkT_eq rows bs ins _ es]

/-- `RegChain.Step.out` with the rows given by `R` and the boxes by `B`. -/
def outT (c bl bh : ℚ) (R : Nat → Option Row) (B : Nat → Box) (ins : Inputs) (known : List (Nat × Ex × Ex)) :
    Step → Option (Nat × Ex × Ex)
  | .plain e => if okT R B ins known e then some (e.reg,e.N,e.D) else none
  | .larger reg a b first σa σb M =>
    match (R reg).map Row.op,look known (reg+1+a),look known (reg+1+b) with
    | some (.larger a' b'),some (Na,Da),some (Nb,Db) =>
      if a'=a ∧ b'=b then
        if first then (if RegBranch.larger c bl bh Na Da Nb Db M σa σb then some (reg,Na,Da) else none)
        else (if RegBranch.larger c bl bh Nb Db Na Da M σb σa then some (reg,Nb,Db) else none)
      else none
    | _,_,_ => none
  | .abs reg a σ M =>
    match (R reg).map Row.op,look known (reg+1+a) with
    | some (.absVal a'),some (N,D) =>
      if a'=a ∧ absSign c bl bh N D M σ then some (reg,esc σ N,D) else none
    | _,_ => none

theorem outT_eq (c bl bh : ℚ) (rows : List Row) (bs : List Box) (ins : Inputs) (known : List (Nat × Ex × Ex))
    (st : Step) : outT c bl bh (fun i => rows[i]?) (getBox bs) ins known st=st.out c bl bh rows bs ins known := by
  cases st with
  | plain e => simp only [outT,Step.out,okT_eq]
  | larger reg a b first σa σb M => rfl
  | abs reg a σ M => rfl

/-- Lookups in an index tree built from a list agree with the list's. -/
theorem tree_rows (rows : List Row) (t : ZSign.ITree (Option Row)) (h : t=ZSign.ITree.ofList (rows.map some)) :
    (fun i => rows[i]?)=(fun i => t.get none i) := by
  funext i
  rw [h,ZSign.get_ofList,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases rows[i]? <;> rfl

theorem tree_boxes (bs : List Box) (t : ZSign.ITree Box) (h : t=ZSign.ITree.ofList bs) :
    getBox bs=(fun i => t.get zeroBox i) := by
  funext i
  rw [h,ZSign.get_ofList,List.getD_eq_getElem?_getD]
  rfl

end ArtGallery.Orthogonal.BoundaryPoint.RegCertT
end
