module

public import ArtGallery.Orthogonal.BoundaryPoint.RegisterOrder
public import ArtGallery.Orthogonal.BoundaryPoint.ZSign

/-! # Register tables with fast lookups

`RegisterTable.block` and `RegisterOrder.check` read the rows, boxes and cache entries from lists,
which the kernel walks one cell at a time (about a thousand cells deep for a long program). The
same checks with the three tables given as lookup functions agree with the list-based ones, so a
table may be decided with its rows, boxes and entries read from balanced index trees
(`block_of_tree`, `check_of_tree`). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RegisterTableT
open MarginCert LinearRegister RegisterForm RegisterOp RegisterTable RegisterOrder ShapeRefs ChartDrawing
open BoundaryChart RoomCoordinates RoomPolynomials

deriving instance DecidableEq for Rule
deriving instance DecidableEq for Entry

def formF (C : Nat → Option Entry) (i : Nat) : Form := match C i with
  | none => []
  | some .raw => atom (i+1)
  | some (.claim f _) => f

def atomBoxF (B : Nat → Box) : Nat → Box
  | 0 => ⟨1,1⟩
  | i+1 => B i

def rowOKF (R : Nat → Option Row) (B : Nat → Box) (C : Nat → Option Entry) (i : Nat) : Bool :=
  match C i with
  | some .raw => true
  | some (.claim f how) =>
    ((R i).bind (fun r => applyRule (atomBoxF B) (fun j => formF C (i+1+j)) (B i) r.op how)).any (same f)
  | none => false

def blockF (R : Nat → Option Row) (B : Nat → Box) (C : Nat → Option Entry) (offset count : Nat) : Bool :=
  (List.range' offset count).all (rowOKF R B C)

theorem formF_eq (cache : List Entry) : formF (fun i => cache[i]?)=form cache := by
  funext i; unfold formF form; rfl

theorem atomBoxF_eq (bs : List Box) : atomBoxF (getBox bs)=atomBox bs := by
  funext i; cases i <;> rfl

theorem rowOKF_eq (rs : List Row) (bs : List Box) (cache : List Entry) (i : Nat) :
    rowOKF (fun i => rs[i]?) (getBox bs) (fun i => cache[i]?) i=rowOK rs bs cache i := by
  unfold rowOKF rowOK; rw [atomBoxF_eq,formF_eq]; rfl

theorem blockF_eq (rs : List Row) (bs : List Box) (cache : List Entry) (o c : Nat) :
    blockF (fun i => rs[i]?) (getBox bs) (fun i => cache[i]?) o c=block rs bs cache o c := by
  unfold blockF block; congr 1

def expressionF (C : Nat → Option Entry) (a : Axis) : Ref → Form
  | .origin => []
  | .register i => formF C i
  | .level i => polynomial ((axisPolys a).getD i [])

def extentF (B : Nat → Box) (C : Nat → Option Entry) (a : Axis) : Ref → Box
  | .register i => B i
  | r => boxForm (atomBoxF B) (expressionF C a r)

def orderedF (rs : List Row) (bs : List Box) (B : Nat → Box) (C : Nat → Option Entry) (a : Axis) (l r : Ref) :
    SignHint → Bool
  | .boxes => decide ((extentF B C a l).hi < (extentF B C a r).lo)
  | .power k => positive (atomBoxF B) (diff (expressionF C a r) (expressionF C a l)) k
  | .negativeAtom => negToken rs bs (diff (expressionF C a r) (expressionF C a l))

def checkF (t : Template) (rs : List Row) (bs : List Box) (B : Nat → Box) (C : Nat → Option Entry) (y : Bool)
    (hints : List SignHint) : Bool :=
  let v := selected (pool y (refs t)) (idsOf t y)
  (List.range (v.length-1)).all fun i => orderedF rs bs B C (axisOf t y) (v.getD i 0) (v.getD (i+1) 0) (hints.getD i .boxes)

theorem expressionF_eq (cache : List Entry) (a : Axis) :
    expressionF (fun i => cache[i]?) a=expression cache a := by
  funext r; cases r <;> simp only [expressionF,expression,formF_eq]

theorem extentF_eq (bs : List Box) (cache : List Entry) (a : Axis) :
    extentF (getBox bs) (fun i => cache[i]?) a=extent bs cache a := by
  funext r; cases r <;> simp only [extentF,extent,expressionF_eq,atomBoxF_eq]

theorem checkF_eq (t : Template) (rs : List Row) (bs : List Box) (cache : List Entry) (y : Bool)
    (hints : List SignHint) : checkF t rs bs (getBox bs) (fun i => cache[i]?) y hints=check t rs bs cache y hints := by
  unfold checkF check
  congr 1

/-- Lookups in an index tree built from a list agree with the list's. -/
theorem tree_opt {α : Type} (l : List α) (t : ZSign.ITree (Option α)) (h : t=ZSign.ITree.ofList (l.map some)) :
    (fun i => l[i]?)=(fun i => t.get none i) := by
  funext i
  rw [h,ZSign.get_ofList,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases l[i]? <;> rfl

theorem tree_box (bs : List Box) (t : ZSign.ITree Box) (h : t=ZSign.ITree.ofList bs) :
    getBox bs=(fun i => t.get zeroBox i) := by
  funext i
  rw [h,ZSign.get_ofList,List.getD_eq_getElem?_getD]
  rfl

theorem block_of_tree {rs : List Row} {bs : List Box} {cache : List Entry} {rT : ZSign.ITree (Option Row)}
    {bT : ZSign.ITree Box} {cT : ZSign.ITree (Option Entry)} (hr : rT=ZSign.ITree.ofList (rs.map some))
    (hb : bT=ZSign.ITree.ofList bs) (hc : cT=ZSign.ITree.ofList (cache.map some)) {o c : Nat}
    (h : blockF (fun i => rT.get none i) (fun i => bT.get zeroBox i) (fun i => cT.get none i) o c=true) :
    block rs bs cache o c=true := by
  rw [←blockF_eq,tree_opt rs rT hr,tree_box bs bT hb,tree_opt cache cT hc]; exact h

theorem check_of_tree {t : Template} {rs : List Row} {bs : List Box} {cache : List Entry}
    {bT : ZSign.ITree Box} {cT : ZSign.ITree (Option Entry)}
    (hb : bT=ZSign.ITree.ofList bs) (hc : cT=ZSign.ITree.ofList (cache.map some)) {y : Bool} {hints : List SignHint}
    (h : checkF t rs bs (fun i => bT.get zeroBox i) (fun i => cT.get none i) y hints=true) :
    check t rs bs cache y hints=true := by
  rw [←checkF_eq,tree_box bs bT hb,tree_opt cache cT hc]; exact h

end ArtGallery.Orthogonal.BoundaryPoint.RegisterTableT
end
