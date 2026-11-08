module

public import ArtGallery.Orthogonal.BoundaryPoint.PortalSlice
public import ArtGallery.Orthogonal.BoundaryPoint.WingTiles

/-! # Whole-door exclusion for every individual full-wing pin witness -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingPrivacy
open PortalGate PortalWindow GridParity GridPins RoomGrid IndexedWing RegisterOrder RegisterForm RegisterTable
open MarginCert LinearRegister ChartDrawing ShapeRefs BoundaryChart WingEnvelope PinGridData
open CorridorProgram ArtGallery.Orthogonal.Hard

inductive Route
  | pocket (p : Portal) (h : Hint)
  | slice (c : PortalSlice.Cut)

def Route.tip : Route → Index
  | .pocket p _ => p.tip
  | .slice c => c.tip

def Route.valid (nx ny : Nat) (rs : List (Rect Nat)) : Route → Bool
  | .pocket p _ => decide (p.Valid nx ny rs)
  | .slice c => decide (c.valid nx ny rs)

def Route.numeric (t : Template) (bs : List Box) (cache : List Entry) : Route → Bool
  | .pocket p h => PortalGate.check t bs cache p h
  | .slice c => c.check t bs cache

def AllHidden (t : Template) (args : List ℚ) : Prop :=
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  let P := actual t.chart data
  ∀ r∈data.2, ∀ w∈r.drop 3, ∀ g,Door (getRat args 0) g → ¬P.Sees (ratPoint w) g

structure Cert (t : Template) (bs : List Box) (cache : List Entry) (idx : Data Nat) (routes : List Route) : Prop where
  geometry : routes.all (Route.valid t.chart.x.length t.chart.y.length idx.1)=true
  numeric : routes.all (Route.numeric t bs cache)=true
  registered : ∀ r∈idx.2, ∀ w∈r.drop 3, ∃ route∈routes,route.tip=w

theorem from_model {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) {xh yh : List SignHint}
    (xc : RegisterOrder.check t rows bs cache false xh=true) (yc : RegisterOrder.check t rows bs cache true yh=true)
    {idx : Data Nat} (rec : IndexedWing.check t rows cache idx=true) (filled : WingTiles.Filled t args)
    (boxes : ∀ b∈idx.1,ValidBox t.chart.x.length t.chart.y.length b)
    {routes : List Route} (cert : Cert t bs cache idx routes) : AllHidden t args := by
  let x := grid t args false
  let y := grid t args true
  let X := x.map ((↑) : ℚ → ℝ)
  let Y := y.map ((↑) : ℚ → ℝ)
  let fn (i : Index) := (x.getD i.1 0,y.getD i.2 0)
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  let P := actual t.chart data
  have xl : X.length=t.chart.x.length := by simp [X,x,grid,selected,idsOf]
  have yl : Y.length=t.chart.y.length := by simp [Y,y,grid,selected,idsOf]
  have hx : X.IsChain (·<·) := RegisterOrder.axis m run false xh xc
  have hy : Y.IsChain (·<·) := RegisterOrder.axis m run true yh yc
  have reindex := IndexedWing.realized m run idx rec
  have marks : data.2=idx.2.map (List.map fn) := congrArg Prod.snd reindex
  have region : P.filled=cellsR X Y idx.1 := by
    change P.filled=WingTiles.cells data.1 at filled
    rw [filled]
    change WingTiles.cells (ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))).1=_
    rw [reindex]; exact WingTiles.grid_cells _ _ _
  have pt (i : Index) : ratPoint (fn i)=gridPt X Y i := by
    have lookup (l : List ℚ) (j : Nat) : ((l.getD j 0:ℚ):ℝ)=(l.map ((↑) : ℚ → ℝ)).getD j 0 := by
      simpa only [Rat.cast_zero] using (List.getD_map (l:=l) (d:=0) (n:=j) (fun a : ℚ => (a:ℝ))).symm
    exact Prod.ext (lookup x i.1) (lookup y i.2)
  intro r hr w hw g door
  change r∈data.2 at hr
  rw [marks] at hr
  obtain ⟨role,mem,rfl⟩ := List.mem_map.mp hr
  rw [←List.map_drop] at hw
  obtain ⟨tip,belongs,rfl⟩ := List.mem_map.mp hw
  obtain ⟨route,listed,rfl⟩ := cert.registered role mem tip belongs
  have valid := List.all_eq_true.mp cert.geometry route listed
  have numeric := List.all_eq_true.mp cert.numeric route listed
  rw [pt]
  cases route with
  | pocket p h =>
    apply PortalGate.misses hx hy region (by simpa only [xl,yl] using boxes) p _ h (PortalGate.arithmetic m run p h numeric) door
    simpa only [xl,yl] using (of_decide_eq_true valid)
  | slice c => exact PortalSlice.misses m run c (of_decide_eq_true valid) boxes numeric hx hy region g door

theorem at_size {t : Template} {rs : List Nat} (basic : WingEnvelopeCert.Cert t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {cache : List Entry} {xh yh : List SignHint} {idx : Data Nat}
    {ps : List Route}
    (data : let p := t.corridor.baseRows++t.corridor.rest
      let rows := p.reverse
      let bs := stack [] p
      cache.length=rows.length ∧ Verified rows bs cache 0 rows.length ∧
      RegisterOrder.check t rows bs cache false xh=true ∧ RegisterOrder.check t rows bs cache true yh=true ∧
      IndexedWing.check t rows cache idx=true ∧ Cert t bs cache idx ps)
    (boxes : ∀ b∈idx.1,ValidBox t.chart.x.length t.chart.y.length b) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    WingTiles.Filled t args → AllHidden t args := by
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
  exact from_model m rfl xc yc rec filled boxes cert

end ArtGallery.Orthogonal.BoundaryPoint.WingPrivacy
end
