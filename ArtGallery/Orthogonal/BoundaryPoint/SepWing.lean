module

public import ArtGallery.Orthogonal.BoundaryPoint.SepCert
public import ArtGallery.Orthogonal.BoundaryPoint.BoxTree
public import ArtGallery.Orthogonal.BoundaryPoint.RoleSeparation
public import ArtGallery.Orthogonal.BoundaryPoint.WingPrivacy

/-! # Same-wing role separation of a wing chart from a span certificate

`SepWing.from_model` turns a checked `SepCert` role certificate for every role
of a wing template into `RoleSeparation.Separated` at an admissible parameter.
The chart grid, its tiles and its role records are those of the existing wing
model; the grid levels are the register forms used by the door certificates. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.SepWing
open Set GridAtom GridParity RoomGrid SpanCells SepGeom SepCert RegisterForm RegisterTable RegisterOrder
open MarginCert LinearRegister ChartDrawing ShapeRefs BoundaryChart IndexedWing PinGridData CorridorProgram
open ArtGallery.Orthogonal.Hard

theorem mono_le' {xs : List ℝ} (hx : xs.IsChain (·<·)) {i j : Nat} (hj : j<xs.length) (h : i≤j) :
    xs.getD i 0≤xs.getD j 0 := by
  rcases Nat.lt_or_ge i j with lt|ge
  · exact (level_lt hx hj lt).le
  · rw [show i=j by omega]

/-- The coordinate forms of the vertical chart lines. -/
def fxOf (t : Template) (cache : List RegisterTable.Entry) : List Form :=
  (List.range t.chart.x.length).map fun i => PortalGate.Node.form t cache (.level false i)

/-- The coordinate forms of the horizontal chart lines. -/
def fyOf (t : Template) (cache : List RegisterTable.Entry) : List Form :=
  (List.range t.chart.y.length).map fun i => PortalGate.Node.form t cache (.level true i)

/-- The boolean chart of a wing template. -/
def chartOf (t : Template) (cache : List RegisterTable.Entry) (bs : List Box) (idx : Data Nat) : SepCert.Chart where
  nx := t.chart.x.length
  ny := t.chart.y.length
  cyc := t.chart.cycle.points
  tiles := idx.1
  fx := fxOf t cache
  fy := fyOf t cache
  B := BoxTree.fastBox bs
  z := ZSign.ZData.ofChart (fxOf t cache) (fyOf t cache) bs

/-- The decidable part of a separation certificate for one wing template. -/
structure Cert (t : Template) (cache : List RegisterTable.Entry) (bs : List Box) (idx : Data Nat) (anc : List Nat)
    (certs : List (List SepCert.Entry)) : Prop where
  axis : cyclicAxis t.chart.cycle.points
  verts : ∀ v∈t.chart.cycle.points, v.1<t.chart.x.length ∧ v.2<t.chart.y.length
  tiles : ∀ r∈idx.1, r.1<t.chart.x.length ∧ r.2.1<t.chart.x.length ∧ r.2.2.1<t.chart.y.length ∧ r.2.2.2<t.chart.y.length
  cells : ∀ e∈cellsOf t.chart.cycle.points, Inner t.chart.x.length e.1 ∧ Inner t.chart.y.length e.2 ∧ (e.1%2=1 ∨ e.2%2=1)
  bottom : ∃ i, i < t.chart.cycle.points.length ∧
    (t.chart.cycle.points.getD i (0,0)).2=0 ∧
    (t.chart.cycle.points.getD ((i+1)%t.chart.cycle.points.length) (0,0)).2=0 ∧
    (t.chart.cycle.points.getD i (0,0)).1<(t.chart.cycle.points.getD ((i+1)%t.chart.cycle.points.length) (0,0)).1
  six : ∀ r∈idx.2, r.length=6
  inRange : (chartOf t cache bs idx).rolesIn idx.2=true
  roles : ∀ i, i < idx.2.length → (chartOf t cache bs idx).roleOK idx.2 i (anc.getD i 0%3) (certs.getD i [])=true

private theorem cast_at (l : List ℚ) (i : Nat) :
    (((l.getD i 0):ℚ):ℝ)=(l.map ((↑) : ℚ → ℝ)).getD i 0 := by
  simpa only [Rat.cast_zero] using (List.getD_map (l:=l) (d:=0) (n:=i) (fun a : ℚ => (a:ℝ))).symm

private theorem witness_map {α β : Type} (f : α → β) (l : List α) (dα : α) (dβ : β) {a : Nat}
    (ha : a<(l.drop 3).length) : ((l.map f).drop 3).getD a dβ=f ((l.drop 3).getD a dα) := by
  rw [←List.map_drop,List.getD_eq_getElem _ _ (by simpa using ha),List.getD_eq_getElem _ _ ha,List.getElem_map]

private theorem drop_index {α : Type} {l : List α} {q : α} (h : q∈l.drop 3) (len : l.length=6) (d : α) :
    ∃ t, t<3 ∧ t<(l.drop 3).length ∧ (l.drop 3).getD t d=q := by
  obtain ⟨t,ht,e⟩ := List.getElem_of_mem h
  have l3 : (l.drop 3).length=3 := by simp [len]
  exact ⟨t,by omega,ht,by rw [List.getD_eq_getElem _ _ ht,e]⟩

theorem from_model {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) {xh yh : List SignHint}
    (xc : RegisterOrder.check t rows bs cache false xh=true) (yc : RegisterOrder.check t rows bs cache true yh=true)
    {idx : Data Nat} (rec : IndexedWing.check t rows cache idx=true) (filled : WingTiles.Filled t args)
    (simple : ∀ g : Data ℚ, ((selected (pool false g) t.chart.x).map ((↑) : ℚ → ℝ)).IsChain (·<·) →
      ((selected (pool true g) t.chart.y).map ((↑) : ℚ → ℝ)).IsChain (·<·) → (actual t.chart g).Simple)
    {anc : List Nat} {certs : List (List SepCert.Entry)} (cert : Cert t cache bs idx anc certs) :
    RoleSeparation.Separated t args anc := by
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
  constructor
  · intro i r hr
    change data.2[i]?=some r at hr
    rw [roles_eq,List.getElem?_map] at hr
    obtain ⟨q,hq,rfl⟩ := Option.map_eq_some_iff.mp hr
    rw [List.length_map]; exact cert.six q (List.mem_of_getElem? hq)
  · intro i k ne ri rk hi hk z hz sa h hh
    change z∈L.boundary at hz
    change L.Sees z _ at sa
    change ¬L.Sees z _
    change data.2[i]?=some ri at hi
    change data.2[k]?=some rk at hk
    rw [roles_eq,List.getElem?_map] at hi hk
    obtain ⟨qi,hqi,rfl⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨qk,hqk,rfl⟩ := Option.map_eq_some_iff.mp hk
    have ii : i < idx.2.length := (List.getElem?_eq_some_iff.mp hqi).1
    have kk : k < idx.2.length := (List.getElem?_eq_some_iff.mp hqk).1
    have qi_eq : idx.2.getD i []=qi := by rw [List.getD_eq_getElem?_getD,hqi]; rfl
    have qk_eq : idx.2.getD k []=qk := by rw [List.getD_eq_getElem?_getD,hqk]; rfl
    have si := cert.six qi (List.mem_of_getElem? hqi)
    have sk := cert.six qk (List.mem_of_getElem? hqk)
    have ai : anc.getD i 0%3<(qi.drop 3).length := by simp [si]; omega
    -- the anchor as a grid node
    have wa : RoleSeparation.witness (qi.map fn) (anc.getD i 0%3)=fn (wit idx.2 i (anc.getD i 0%3)) := by
      unfold RoleSeparation.witness wit; rw [qi_eq]; exact witness_map fn qi (0,0) (0,0) ai
    rw [wa,point] at sa
    rw [←List.map_drop] at hh
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hh
    obtain ⟨tt,t3,tl,tq⟩ := drop_index hq sk (0,0)
    rw [point]
    have wq : wit idx.2 k tt=q := by unfold wit; rw [qk_eq]; exact tq
    rw [←wq]
    rw [L_eq] at hz sa ⊢
    exact role_sound G cert.inRange ii (by rw [qi_eq]; exact ai) (cert.roles i ii) hz sa kk (Ne.symm ne) t3
      (by rw [qk_eq]; exact tl)

theorem at_size {t : Template} {rs : List Nat} (basic : WingEnvelopeCert.Cert t rs.length) (n j : Nat)
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
    (cert : Cert t cache (stack [] (t.corridor.baseRows++t.corridor.rest)) idx anc certs) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    WingTiles.Filled t args → RoleSeparation.Separated t args anc := by
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
  exact from_model m rfl xc yc rec filled simple cert

end ArtGallery.Orthogonal.BoundaryPoint.SepWing
end
