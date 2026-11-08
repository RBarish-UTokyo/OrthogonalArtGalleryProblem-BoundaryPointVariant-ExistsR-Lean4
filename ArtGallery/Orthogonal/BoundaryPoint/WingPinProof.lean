module

public import ArtGallery.Orthogonal.BoundaryPoint.PinContact
public import ArtGallery.Orthogonal.BoundaryPoint.RegisterProduct
public import ArtGallery.Orthogonal.BoundaryPoint.WingTiles

/-! # Physical localization of a boundary viewer of a wing's three pin witnesses -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingPinProof
open Set CorridorProgram GridParity GridPins PinGridData RoomGrid IndexedWing RegisterForm RegisterTable RegisterOrder
open MarginCert LinearRegister ChartDrawing ShapeRefs BoundaryChart WingEnvelope ArtGallery.Orthogonal.Hard

def distance (t : Template) (cache : List Entry) (axis neg : Bool) (i j : Nat) : Form :=
  let F := fun k => expression cache (axisOf t axis) ((refsFor t axis).getD k 0)
  if neg then diff (F j) (F i) else diff (F i) (F j)

def gap (t : Template) (bs : List Box) (cache : List Entry) (p : Pin) (h : RegisterProduct.Hint) :=
  let x := distance t cache p.frame.swap p.frame.negT
  let y := distance t cache (!p.frame.swap) p.frame.negN
  RegisterProduct.check (atomBox bs) (y p.clear p.floor) (x p.nearC p.farC) (x p.high p.farC) (y p.top p.floor) h

private theorem cast_at (l : List ℚ) (i : Nat) :
    (((l.getD i 0):ℚ):ℝ)=(l.map ((↑) : ℚ → ℝ)).getD i 0 := by
  simpa only [Rat.cast_zero] using (List.getD_map (l:=l) (d:=0) (n:=i) (fun a : ℚ => (a:ℝ))).symm

private theorem distance_value {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (a neg : Bool) (i j : Nat) :
    let X := (grid t args false).map ((↑) : ℚ → ℝ)
    let Y := (grid t args true).map ((↑) : ℚ → ℝ)
    ((value (getRat args 0) (atomVal xs) (distance t cache a neg i j):ℚ):ℝ)=
      coord a neg X Y i-coord a neg X Y j := by
  have q (k : Nat) : value (getRat args 0) (atomVal xs)
      (expression cache (axisOf t a) ((refsFor t a).getD k 0))=(grid t args a).getD k 0 :=
    (formula m ..).trans (grid_value m run a k).symm
  dsimp only
  cases neg
  · simp only [distance,Bool.false_eq_true,ite_false,diff_value,q,Rat.cast_sub,cast_at,coord,signR]
    cases a <;> rfl
  · simp only [distance,ite_true,diff_value,q,Rat.cast_sub,cast_at,coord,signR]
    cases a <;> simp only [ite_true,Bool.false_eq_true,ite_false]; all_goals ring

theorem aperture {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) (p : Pin) (h : RegisterProduct.Hint)
    (checked : gap t bs cache p h=true) :
    let X := (grid t args false).map ((↑) : ℚ → ℝ)
    let Y := (grid t args true).map ((↑) : ℚ → ℝ)
    let T := p.tval X Y
    let N := p.nval X Y
    (T p.high-T p.farC)*(N p.top-N p.floor)<(N p.clear-N p.floor)*(T p.nearC-T p.farC) := by
  have prod := RegisterProduct.compare (atom_bound m.bounds) m.pos m.upper h checked
  have H := (Rat.cast_lt (K:=ℝ)).mpr prod
  simpa only [Rat.cast_mul,distance_value m run,Pin.tval,Pin.nval] using H

def roleOK (p : Pin) : List Index → Bool
  | [_,a,b,x,y,z] => decide (p.spot=(a,b) ∨ p.spot=(b,a)) && p.witnesses.all fun q => decide (q∈[x,y,z])
  | _ => false

def Forces (t : Template) (args : List ℚ) :=
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  let P := actual t.chart data
  ∀ c a b u v w, [c,a,b,u,v,w]∈data.2 → ∀ z∈P.boundary,
    P.Sees z (ratPoint u) → P.Sees z (ratPoint v) → P.Sees z (ratPoint w) →
    z∈ArtGallery.segment (ratPoint a) (ratPoint b)

structure Cert (t : Template) (cache : List Entry) (bs : List Box) (data : Data Nat) (pins : List (Pin × RegisterProduct.Hint)) : Prop where
  valid : ∀ z∈pins,z.1.Valid t.chart.x.length t.chart.y.length data.1
  nodes : ∀ z∈pins, ∀ v∈z.1.witnesses,small t.chart.x.length t.chart.y.length v
  contacts : pins.all (fun z => PinContact.check z.1 data.1 t.chart.cycle.points)=true
  gaps : pins.all (fun z => gap t bs cache z.1 z.2)=true
  assignments : ∀ r∈data.2,∃ z∈pins,roleOK z.1 r=true

set_option maxHeartbeats 1500000 in
theorem from_model {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) {xh yh : List SignHint}
    (xc : RegisterOrder.check t rows bs cache false xh=true) (yc : RegisterOrder.check t rows bs cache true yh=true)
    {index : Data Nat} (rec : IndexedWing.check t rows cache index=true) (filled : WingTiles.Filled t args)
    (axisEdges : cyclicAxis t.chart.cycle.points)
    (vertices : ∀ p∈t.chart.cycle.points,p.1<t.chart.x.length ∧ p.2<t.chart.y.length)
    (cellIndices : ∀ r∈index.1, ValidBox t.chart.x.length t.chart.y.length r)
    {pins : List (Pin × RegisterProduct.Hint)} (cert : Cert t cache bs index pins) : Forces t args := by
  let x := grid t args false
  let y := grid t args true
  let X := x.map ((↑) : ℚ → ℝ)
  let Y := y.map ((↑) : ℚ → ℝ)
  let fn (i : Index) := (x.getD i.1 0,y.getD i.2 0)
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  let P := actual t.chart data
  have xlen : X.length=t.chart.x.length := by simp [X,x,grid,selected,idsOf]
  have ylen : Y.length=t.chart.y.length := by simp [Y,y,grid,selected,idsOf]
  have xord : X.IsChain (·<·) := RegisterOrder.axis m run false xh xc
  have yord : Y.IsChain (·<·) := RegisterOrder.axis m run true yh yc
  have data_eq := IndexedWing.realized m run index rec
  have roles : data.2=index.2.map (List.map fn) := congrArg Prod.snd data_eq
  have cellEq : P.filled=cellsR X Y index.1 := by
    change P.filled=WingTiles.cells data.1 at filled
    rw [filled]
    change WingTiles.cells (ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))).1=_
    rw [data_eq]; exact WingTiles.grid_cells _ _ _
  have P_eq : P=⟨t.chart.cycle.points.map (gridPt X Y)⟩ := actual_grid _ _
  have bd (z) (hz : z∈P.boundary) : boundaryB t.chart.cycle.points (GridAtom.atom z.1 X) (GridAtom.atom z.2 Y)=true := by
    rw [P_eq] at hz; exact (boundary_iff xord yord (by simpa only [xlen,ylen] using vertices) axisEdges z).mp hz
  have point (i : Index) : ratPoint (fn i)=gridPt X Y i := Prod.ext (cast_at x i.1) (cast_at y i.2)
  intro c a b u v w member z boundary su sv sw
  change [c,a,b,u,v,w]∈data.2 at member
  rw [roles] at member
  obtain ⟨role,registered,eq⟩ := List.mem_map.mp member
  obtain ⟨⟨pin,hint⟩,owned,hit⟩ := cert.assignments role registered
  unfold roleOK at hit
  split at hit
  next c' a' b' u' v' w' =>
    have place : (pin.spot=(a',b') ∨ pin.spot=(b',a')) ∧
        pin.witnesses.all (fun q => decide (q∈[u',v',w']))=true := by simpa only [Bool.and_eq_true,decide_eq_true_eq] using hit
    have lookup := List.all_eq_true.mp place.2
    simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at eq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := eq
    rw [point] at su sv sw
    have sees (q) (hq : q∈pin.witnesses) : P.Sees z (gridPt X Y q) := by
      have loc := of_decide_eq_true (lookup q hq)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at loc
      rcases loc with rfl|rfl|rfl <;> assumption
    have checked : gap t bs cache pin hint=true := List.all_eq_true.mp cert.gaps (pin,hint) owned
    have margin := aperture (t:=t) m run pin hint checked
    have loc := PinGridData.localizes (P:=P) (xs:=X) (ys:=Y) (rs:=index.1) (l:=t.chart.cycle.points) xord yord cellEq bd
      (by simpa only [xlen,ylen] using cellIndices) pin
      (by simpa only [xlen,ylen] using cert.valid _ owned)
      (by simpa only [xlen,ylen] using cert.nodes _ owned)
      (fun A _ B _ => PinContact.sound (List.all_eq_true.mp cert.contacts (pin,hint) owned) A B)
      margin boundary sees
    rw [point,point]
    rcases place.1 with direct|rev
    · simpa only [direct] using loc
    · simpa only [rev,Geometry.segment_comm (gridPt X Y b') (gridPt X Y a')] using loc
  · contradiction

theorem at_size {t : Template} {rs : List Nat} (basic : WingEnvelopeCert.Cert t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {cache : List Entry} {xh yh : List SignHint} {index : Data Nat}
    {pins : List (Pin × RegisterProduct.Hint)}
    (data : let p := t.corridor.baseRows++t.corridor.rest
      let rows := p.reverse
      let bs := stack [] p
      cache.length=rows.length ∧ Verified rows bs cache 0 rows.length ∧
      RegisterOrder.check t rows bs cache false xh=true ∧ RegisterOrder.check t rows bs cache true yh=true ∧
      IndexedWing.check t rows cache index=true ∧ Cert t cache bs index pins)
    (axisEdges : cyclicAxis t.chart.cycle.points)
    (vertices : ∀ p∈t.chart.cycle.points,p.1<t.chart.x.length ∧ p.2<t.chart.y.length)
    (cellIndices : ∀ r∈index.1, ValidBox t.chart.x.length t.chart.y.length r) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    WingTiles.Filled t args → Forces t args := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤RegisterForm.cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have bounds := lookup_bound (xs:=[]) (WingEnvelopeCert.parameters n j rs hn hj hr) (by exact empty_encloses) basic.arithmetic
  obtain ⟨size,valid,xc,yc,rec,cert⟩ := data
  have m : Model args xs p.reverse (stack [] p) cache := ⟨run,bounds,pos,small,RegisterTable.model run bounds pos small size valid⟩
  dsimp only; intro filled
  exact from_model m rfl xc yc rec filled axisEdges vertices cellIndices cert

end ArtGallery.Orthogonal.BoundaryPoint.WingPinProof
end
