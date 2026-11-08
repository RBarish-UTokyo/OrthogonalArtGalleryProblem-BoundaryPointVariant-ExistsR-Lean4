module

public import ArtGallery.Orthogonal.BoundaryPoint.SepWing

/-! # The certified chart model of an executed wing

The strictly increasing register grids of a wing, its chart polygon and its
rectangle and role data, packaged as a `SepCert.Good` model at every admissible
parameter. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingModel
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert RegisterForm RegisterTable RegisterOrder
open MarginCert LinearRegister ChartDrawing ShapeRefs BoundaryChart IndexedWing PinGridData CorridorProgram SepWing
open ArtGallery.Orthogonal.Hard

private theorem cast_at (l : List ℚ) (i : Nat) :
    (((l.getD i 0):ℚ):ℝ)=(l.map ((↑) : ℚ → ℝ)).getD i 0 := by
  simpa only [Rat.cast_zero] using (List.getD_map (l:=l) (d:=0) (n:=i) (fun a : ℚ => (a:ℝ))).symm

theorem good_of_model {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) {xh yh : List SignHint}
    (xc : RegisterOrder.check t rows bs cache false xh=true) (yc : RegisterOrder.check t rows bs cache true yh=true)
    {idx : Data Nat} (rec : IndexedWing.check t rows cache idx=true) (filled : WingTiles.Filled t args)
    (simple : ∀ g : Data ℚ, ((selected (pool false g) t.chart.x).map ((↑) : ℚ → ℝ)).IsChain (·<·) →
      ((selected (pool true g) t.chart.y).map ((↑) : ℚ → ℝ)).IsChain (·<·) → (actual t.chart g).Simple)
    {anc : List Nat} {certs : List (List SepCert.Entry)} (cert : SepWing.Cert t cache bs idx anc certs) :
    let X := (grid t args false).map ((↑) : ℚ → ℝ)
    let Y := (grid t args true).map ((↑) : ℚ → ℝ)
    Good (chartOf t cache bs idx) X Y (getRat args 0) (atomVal xs) ∧
      actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0)))=
        (chartOf t cache bs idx).poly X Y ∧
      ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))=
        WingEnvelope.mapData (fun i => (grid t args false).getD i 0) (fun i => (grid t args true).getD i 0) idx := by
  let x := grid t args false
  let y := grid t args true
  let X := x.map ((↑) : ℚ → ℝ)
  let Y := y.map ((↑) : ℚ → ℝ)
  let fn (i : Index) := (x.getD i.1 0,y.getD i.2 0)
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  let L := actual t.chart data
  let C := chartOf t cache bs idx
  have hx : X.IsChain (·<·) := RegisterOrder.axis m run false xh xc
  have hy : Y.IsChain (·<·) := RegisterOrder.axis m run true yh yc
  have xlen : X.length=t.chart.x.length := by simp [X,x,grid,selected,idsOf]
  have ylen : Y.length=t.chart.y.length := by simp [Y,y,grid,selected,idsOf]
  have data_eq := IndexedWing.realized m run idx rec
  have roles_eq : data.2=idx.2.map (List.map fn) := congrArg Prod.snd data_eq
  have L_eq : L=C.poly X Y := actual_grid _ _
  have region : L.filled=cellsR X Y idx.1 := by
    change L.filled=WingTiles.cells data.1 at filled
    rw [filled]
    change WingTiles.cells (ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))).1=_
    rw [data_eq]; exact WingTiles.grid_cells _ _ _
  have point (i : Index) : ratPoint (fn i)=gridPt X Y i := Prod.ext (cast_at x i.1) (cast_at y i.2)
  have value_q (ax : Bool) (i : Nat) :
      value (getRat args 0) (atomVal xs) (PortalGate.Node.form t cache (.level ax i))=(grid t args ax).getD i 0 := by
    rw [PortalGate.Node.form,formula m,←grid_value m run ax i]
  have simpleL : L.Simple := simple data hx hy
  obtain ⟨b,hb,b1,b2,b3⟩ := cert.bottom
  have hbn : b<(C.poly X Y).n := by simpa [poly_n,Chart.n,C,chartOf] using hb
  have left : (C.poly X Y).InteriorLeft := by
    have vb (k : Nat) (hk : k<C.n) := vtx_eq C X Y hk
    have nC : C.n=t.chart.cycle.points.length := rfl
    refine Polygon.interiorLeft_of_bottom_edge (L_eq ▸ simpleL) hbn (y₀:=Y.getD 0 0) ?_ ?_ ?_ ?_
    · intro j hj
      rw [poly_n] at hj
      rw [vb j hj]
      have mem := node_mem C hj
      have r := cert.verts _ mem
      exact mono_le' hy (by rw [ylen]; exact r.2) (Nat.zero_le _)
    · rw [vb b (by rw [nC]; exact hb)]
      simp only [gridPt]; exact congrArg (fun k => Y.getD k 0) b1
    · rw [poly_n,vtx_eq C X Y (Nat.mod_lt _ (by rw [nC]; omega))]
      simp only [gridPt]; exact congrArg (fun k => Y.getD k 0) b2
    · rw [vb b (by rw [nC]; exact hb),poly_n,vtx_eq C X Y (Nat.mod_lt _ (by rw [nC]; omega))]
      have r := cert.verts _ (node_mem C (i:=(b+1)%C.n) (Nat.mod_lt _ (by rw [nC]; omega)))
      exact level_lt hx (by rw [xlen]; exact r.1) b3
  have G : Good C X Y (getRat args 0) (atomVal xs) := {
    hx := hx, hy := hy, lx := xlen, ly := ylen
    vx := by
      intro i hi
      have hi' : i<t.chart.x.length := hi
      have e : C.fx.getD i []=PortalGate.Node.form t cache (.level false i) := by
        simp only [C,chartOf,fxOf,fyOf]; rw [List.getD_eq_getElem _ _ (by simpa using hi')]; simp
      rw [e,value_q false i]; exact (cast_at x i).symm
    vy := by
      intro i hi
      have hi' : i<t.chart.y.length := hi
      have e : C.fy.getD i []=PortalGate.Node.form t cache (.level true i) := by
        simp only [C,chartOf,fxOf,fyOf]; rw [List.getD_eq_getElem _ _ (by simpa using hi')]; simp
      rw [e,value_q true i]; exact (cast_at y i).symm
    bounds := by
      show Bounds (BoxTree.fastBox _) _
      rw [BoxTree.fastBox_eq]; exact atom_bound m.bounds
    pos := m.pos
    small := m.upper
    verts := cert.verts
    axis := cert.axis
    simple := L_eq ▸ simpleL
    left := left
    fill := L_eq ▸ region
    tileIdx := cert.tiles
    cells := cert.cells
    zval := fun hok => ⟨ZSign.ofChart_xvalue _ _ _ hok _ _,ZSign.ofChart_yvalue _ _ _ hok _ _⟩
    zb := ZSign.ofChart_bounds _ _ _ (atom_bound m.bounds)
    zpos := ZSign.ofChart_pos _ _ _ }
  exact ⟨G,L_eq,data_eq⟩

theorem good_at_size {t : Template} {rs : List Nat} (basic : WingEnvelopeCert.Cert t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {cache : List RegisterTable.Entry} {xh yh : List SignHint}
    {idx : Data Nat}
    (data : let p := t.corridor.baseRows++t.corridor.rest
      let rows := p.reverse
      let bs := stack [] p
      cache.length=rows.length ∧ Verified rows bs cache 0 rows.length ∧
      RegisterOrder.check t rows bs cache false xh=true ∧ RegisterOrder.check t rows bs cache true yh=true ∧
      IndexedWing.check t rows cache idx=true)
    (simple : ∀ g : Data ℚ, ((selected (pool false g) t.chart.x).map ((↑) : ℚ → ℝ)).IsChain (·<·) →
      ((selected (pool true g) t.chart.y).map ((↑) : ℚ → ℝ)).IsChain (·<·) → (actual t.chart g).Simple)
    {anc : List Nat} {certs : List (List SepCert.Entry)}
    (cert : SepWing.Cert t cache (stack [] (t.corridor.baseRows++t.corridor.rest)) idx anc certs) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    let xs := execRat args [] (t.corridor.baseRows++t.corridor.rest)
    let X := (grid t args false).map ((↑) : ℚ → ℝ)
    let Y := (grid t args true).map ((↑) : ℚ → ℝ)
    WingTiles.Filled t args →
    Good (chartOf t cache (stack [] (t.corridor.baseRows++t.corridor.rest)) idx) X Y s (atomVal xs) ∧
      actual t.chart (ShapeRefs.join (t.corridor.coords args) (t.room.coords s))=
        (chartOf t cache (stack [] (t.corridor.baseRows++t.corridor.rest)) idx).poly X Y ∧
      ShapeRefs.join (t.corridor.coords args) (t.room.coords s)=
        WingEnvelope.mapData (fun i => (grid t args false).getD i 0) (fun i => (grid t args true).getD i 0) idx := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤RegisterForm.cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have bounds := lookup_bound (xs:=[]) (WingEnvelopeCert.parameters n j rs hn hj hr) (by exact MarginCert.empty_encloses) basic.arithmetic
  obtain ⟨size,valid,xc,yc,rec⟩ := data
  have m : Model args xs p.reverse (stack [] p) cache := ⟨run,bounds,pos,small,RegisterTable.model run bounds pos small size valid⟩
  dsimp only; intro filled
  exact good_of_model m rfl xc yc rec filled simple cert

/-- The register model of an executed wing program at every admissible size. -/
theorem model_at_size {t : Template} {rs : List Nat} (basic : WingEnvelopeCert.Cert t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {cache : List RegisterTable.Entry}
    (size : cache.length=(t.corridor.baseRows++t.corridor.rest).reverse.length)
    (valid : Verified (t.corridor.baseRows++t.corridor.rest).reverse (stack [] (t.corridor.baseRows++t.corridor.rest))
      cache 0 (t.corridor.baseRows++t.corridor.rest).reverse.length) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    Model args (execRat args [] (t.corridor.baseRows++t.corridor.rest)) (t.corridor.baseRows++t.corridor.rest).reverse
      (stack [] (t.corridor.baseRows++t.corridor.rest)) cache := by
  intro s args
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤RegisterForm.cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have bounds := lookup_bound (xs:=[]) (WingEnvelopeCert.parameters n j rs hn hj hr) (by exact MarginCert.empty_encloses) basic.arithmetic
  exact ⟨run,bounds,pos,small,RegisterTable.model run bounds pos small size valid⟩

theorem grid_length (t : Template) (args : List ℚ) (y : Bool) :
    ((IndexedWing.grid t args y).map (fun q : ℚ => (q:ℝ))).length=(if y then t.chart.y else t.chart.x).length := by
  simp [IndexedWing.grid,selected,RegisterOrder.idsOf]

/-- Every argument after the scale is a multiple of the scale by at most `n`. -/
theorem args_unit {rs : List Nat} {n j : Nat} (hn : 0<n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) (k : Nat) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    0≤getRat args (k+1) ∧ getRat args (k+1)≤1 := by
  intro s args
  have hn' : (0:ℚ)<n := by exact_mod_cast hn
  have unit (i : Nat) (hi : i≤n) : 0≤(i:ℚ)*s ∧ (i:ℚ)*s≤1 := by
    simp only [s]; constructor
    · positivity
    · rw [mul_one_div,div_le_one hn']; exact_mod_cast hi
  cases k with
  | zero => exact unit j hj
  | succ k =>
    simp only [args,getRat,List.getElem?_cons_succ,List.getElem?_map]
    cases h : rs[k]? with
    | none => simp
    | some i => simpa using unit i (hr i (List.mem_of_getElem? h))

end ArtGallery.Orthogonal.BoundaryPoint.WingModel
end
