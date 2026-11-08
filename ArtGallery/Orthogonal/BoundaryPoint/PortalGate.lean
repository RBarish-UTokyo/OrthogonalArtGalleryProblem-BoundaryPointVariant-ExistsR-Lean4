module

public import ArtGallery.Orthogonal.BoundaryPoint.PortalWindow
public import ArtGallery.Orthogonal.BoundaryPoint.RegisterProduct
public import ArtGallery.Orthogonal.BoundaryPoint.IndexedWing

/-! # Verifying a pocket's angular exclusion on the entire closed door -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.PortalGate
open GridPins GridParity PortalWindow PinGridData RegisterForm RegisterTable RegisterOrder
open IndexedWing ChartDrawing LinearRegister MarginCert PerpendicularPin ArtGallery.Orthogonal.Hard

inductive Node
  | level (y : Bool) (i : Nat)
  | low (y : Bool)
  | high (y : Bool)

def Node.form (t : Template) (cache : List Entry) : Node → Form
  | .level y i => expression cache (axisOf t y) ((refsFor t y).getD i 0)
  | .low y => if y then const 1 else []
  | .high y => if y then const 1 else [((1,0),1/320)]

noncomputable def Node.real (X Y : List ℝ) (s : ℝ) : Node → ℝ
  | .level y i => PortalWindow.level X Y y i
  | .low y => if y then 1 else 0
  | .high y => if y then 1 else s/320

abbrev Delta := Node × Node
def Delta.form (t : Template) (c : List Entry) (a : Delta) := diff (a.1.form t c) (a.2.form t c)
noncomputable def Delta.real (X Y : List ℝ) (s : ℝ) (a : Delta) := a.1.real X Y s - a.2.real X Y s

def forward (p : Portal) : Delta :=
  let n := !p.swap
  if p.flip then (.level n (component n p.tip),.low n) else (.high n,.level n (component n p.tip))
def depth (p : Portal) : Delta :=
  let n := !p.swap
  (.level n (upper n p.pocket),.level n (lower n p.pocket))
def width (p : Portal) : Delta :=
  (.level p.swap (upper p.swap p.pocket),.level p.swap (lower p.swap p.pocket))
def transverse (p : Portal) (right : Bool) : Delta :=
  let t := p.swap
  if right then (.low t,.level t (component t p.tip)) else (.level t (component t p.tip),.high t)

inductive Hint
  | back (k : Nat)
  | side (right : Bool) (k : Nat) (h : RegisterProduct.Hint)

def check (t : Template) (bs : List Box) (c : List Entry) (p : Portal) : Hint → Bool
  | .back k => positive (atomBox bs) (diff [] ((forward p).form t c)) k
  | .side right k hint =>
    let gap := (transverse p right).form t c
    let B := (width p).form t c
    positive (atomBox bs) (diff gap B) k &&
      RegisterProduct.check (atomBox bs) gap ((depth p).form t c) B ((forward p).form t c) hint

private theorem node_value {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (a : Node) :
    let X := (grid t args false).map ((↑) : ℚ → ℝ)
    let Y := (grid t args true).map ((↑) : ℚ → ℝ)
    ((value (getRat args 0) (atomVal xs) (a.form t cache):ℚ):ℝ)=a.real X Y (getRat args 0) := by
  cases a with
  | level ax i =>
    rw [Node.form,formula m,←grid_value m run ax i]
    dsimp only
    have h := (List.getD_map (l:=grid t args ax) (d:=0) (n:=i) (fun a : ℚ => (a:ℝ))).symm
    cases ax <;> simpa [Node.real,PortalWindow.level] using h
  | low ax => cases ax <;> simp [Node.form,Node.real,const_value _ _ _ (show atomVal xs 0=1 from rfl),value]
  | high ax =>
    cases ax <;> simp [Node.form,Node.real,const_value _ _ _ (show atomVal xs 0=1 from rfl),value,valTerm,atomVal] <;> ring

theorem delta_value {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (a : Delta) :
    let X := (grid t args false).map ((↑) : ℚ → ℝ)
    let Y := (grid t args true).map ((↑) : ℚ → ℝ)
    ((value (getRat args 0) (atomVal xs) (a.form t cache):ℚ):ℝ)=a.real X Y (getRat args 0) := by
  simp only [Delta.form,Delta.real,diff_value,Rat.cast_sub,node_value m run]

def PlaneTest (X Y : List ℝ) (s : ℝ) (p : Portal) : Hint → Prop
  | .back _ => (forward p).real X Y s < 0
  | .side right _ _ =>
    (width p).real X Y s < (transverse p right).real X Y s ∧
    (width p).real X Y s * (forward p).real X Y s < (transverse p right).real X Y s * (depth p).real X Y s

theorem arithmetic {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (p : Portal) (hint : Hint)
    (ok : check t bs cache p hint=true) :
    PlaneTest ((grid t args false).map ((↑) : ℚ → ℝ)) ((grid t args true).map ((↑) : ℚ → ℝ))
      (getRat args 0) p hint := by
  cases hint with
  | back k =>
    have pos := positive_value (atom_bound m.bounds) m.pos m.upper ok
    rw [diff_value,value,zero_sub,neg_pos] at pos
    simpa only [PlaneTest,delta_value m run,Rat.cast_zero] using (Rat.cast_lt (K:=ℝ)).mpr pos
  | side right k h =>
    have ⟨gap,prod⟩ := Bool.and_eq_true_iff.mp ok
    have pos := positive_value (atom_bound m.bounds) m.pos m.upper gap
    rw [diff_value,sub_pos] at pos
    have compared := RegisterProduct.compare (atom_bound m.bounds) m.pos m.upper h prod
    exact ⟨by simpa only [delta_value m run] using (Rat.cast_lt (K:=ℝ)).mpr pos,
      by simpa only [Rat.cast_mul,delta_value m run] using (Rat.cast_lt (K:=ℝ)).mpr compared⟩

def Door (s : ℝ) (g : Point) := 0≤g.1 ∧ g.1≤s/320 ∧ g.2=1

private theorem endpoints {s : ℝ} {g : Point} (door : Door s g) (ax : Bool) (X Y : List ℝ) :
    (Node.low ax).real X Y s ≤ component ax g ∧ component ax g ≤ (Node.high ax).real X Y s := by
  cases ax with
  | false => exact ⟨door.1,door.2.1⟩
  | true => exact ⟨door.2.2.ge,door.2.2.le⟩

private theorem grid_component (X Y : List ℝ) (ax : Bool) (idx : Nat × Nat) :
    component ax (gridPt X Y idx)=level X Y ax (component ax idx) := by cases ax <;> rfl

theorem misses {P : Polygon} {X Y : List ℝ} {rs : List (CorridorProgram.Rect Nat)}
    (hx : X.IsChain (·<·)) (hy : Y.IsChain (·<·)) (fill : P.filled=cellsR X Y rs)
    (boxes : ∀ r∈rs,ValidBox X.length Y.length r) (p : Portal) (valid : p.Valid X.length Y.length rs)
    {s : ℝ} (h : Hint) (test : PlaneTest X Y s p h) {g : Point} (door : Door s g) :
    ¬P.Sees (gridPt X Y p.tip) g := by
  apply PortalWindow.blocked hx hy fill boxes p valid
  let t := p.swap
  let n := !p.swap
  let w := gridPt X Y p.tip
  have fw : p.frame.pt w=(component t w,signR p.flip (component n w)) := by rw [chart_components]; rfl
  have fg : p.frame.pt g=(component t g,signR p.flip (component n g)) := by rw [chart_components]; rfl
  have norm : (p.frame.pt g).2-(p.frame.pt w).2≤(forward p).real X Y s := by
    rw [fg,fw]; dsimp only; rw [show component n w=level X Y n (component n p.tip) from grid_component ..]
    have b := endpoints door n X Y
    cases e : p.flip <;> simp only [forward,Delta.real,e,signR,ite_true,Bool.false_eq_true,ite_false,Node.real] at * <;> linarith
  have sameW : p.T X Y (upper t p.pocket)-p.T X Y (lower t p.pocket)=(width p).real X Y s := rfl
  have sameD : p.N X Y p.near-p.N X Y p.far=(depth p).real X Y s := by
    cases e : p.flip <;> simp [Portal.N,Portal.near,Portal.far,depth,Delta.real,Node.real,signR,e] <;> ring
  have nonneg (ax : Bool) (lo hi : Nat) (hlo : lo<(if ax then Y else X).length)
      (hhi : hi<(if ax then Y else X).length) (order : lo≤hi) :
      level X Y ax lo≤level X Y ax hi := by
    cases ax <;> first | exact (strictMonoOn_getD hx).monotoneOn hlo hhi order | exact (strictMonoOn_getD hy).monotoneOn hlo hhi order
  have box := boxes _ valid.1
  have dims (ax : Bool) : lower ax p.pocket<(if ax then Y else X).length ∧ upper ax p.pocket<(if ax then Y else X).length := by
    cases ax with | false => exact ⟨box.1,box.2.1⟩ | true => exact box.2.2
  have apos : 0≤(depth p).real X Y s := sub_nonneg.mpr (nonneg n _ _ (dims n).1 (dims n).2 valid.2.2.2.1.le)
  have bpos : 0≤(width p).real X Y s := sub_nonneg.mpr (nonneg t _ _ (dims t).1 (dims t).2 (valid.2.2.2.2.1.trans valid.2.2.2.2.2.1))
  cases h with
  | back k => exact Or.inl (sub_neg.mp (norm.trans_lt test))
  | side right k h =>
    have transverse_bound : (transverse p right).real X Y s ≤ |(p.frame.pt g).1-(p.frame.pt w).1| := by
      rw [fg,fw]; dsimp only
      rw [show component t w=level X Y t (component t p.tip) from grid_component ..]
      have b := endpoints door t X Y
      cases right with
      | false =>
        apply le_trans _ (neg_le_abs _)
        change level X Y t (component t p.tip)-(Node.high t).real X Y s ≤ _
        linarith [b.2]
      | true => exact (sub_le_sub_right b.1 _).trans (le_abs_self _)
    rw [sameW,sameD]
    exact Or.inr ⟨test.1.trans_le transverse_bound,((mul_le_mul_of_nonneg_left norm bpos).trans_lt test.2).trans_le
      (mul_le_mul_of_nonneg_right transverse_bound apos)⟩

end ArtGallery.Orthogonal.BoundaryPoint.PortalGate
end
