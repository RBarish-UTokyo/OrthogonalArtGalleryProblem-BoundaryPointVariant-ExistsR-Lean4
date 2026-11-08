module

public import ArtGallery.Orthogonal.BoundaryPoint.PortalGate
public import ArtGallery.Orthogonal.BoundaryPoint.WingTiles

/-! # One private witness per full-wing role is invisible through the hub door -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingEscape
open Set ChartDrawing ShapeRefs BoundaryChart WingEnvelope RegisterOrder RegisterTable RegisterForm
open PortalGate PortalWindow GridPins PinGridData IndexedWing LinearRegister MarginCert GridParity RoomGrid
open CorridorProgram ArtGallery.Orthogonal.Hard

def Hidden (t : Template) (args : List ℚ) : Prop :=
  let data := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  let P := actual t.chart data
  ∀ role∈data.2, ∃ w∈role.drop 3, ∀ q, Door (getRat args 0) q → ¬P.Sees (ratPoint w) q

abbrev CertPoint := Portal × Hint

structure Cert (t : Template) (bs : List Box) (c : List Entry) (idx : Data Nat) (ps : List CertPoint) : Prop where
  valid : ∀ z∈ps,z.1.Valid t.chart.x.length t.chart.y.length idx.1
  aperture : ps.all (fun z => PortalGate.check t bs c z.1 z.2)=true
  assignments : ∀ r∈idx.2,∃ z∈ps,z.1.tip∈r.drop 3

theorem from_model {t : Template} {args xs rows bs cache} (m : Model args xs rows bs cache)
    (run : xs=execRat args [] (t.corridor.baseRows++t.corridor.rest)) {xh yh : List SignHint}
    (xc : RegisterOrder.check t rows bs cache false xh=true) (yc : RegisterOrder.check t rows bs cache true yh=true)
    {idx : Data Nat} (rec : IndexedWing.check t rows cache idx=true) (filled : WingTiles.Filled t args)
    (boxes : ∀ b∈idx.1,ValidBox t.chart.x.length t.chart.y.length b)
    {ps : List CertPoint} (cert : Cert t bs cache idx ps) : Hidden t args := by
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
  have data_eq := IndexedWing.realized m run idx rec
  have roles : data.2=idx.2.map (List.map fn) := congrArg Prod.snd data_eq
  have region : P.filled=cellsR X Y idx.1 := by
    change P.filled=WingTiles.cells data.1 at filled
    rw [filled]
    change WingTiles.cells (ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))).1=_
    rw [data_eq]; exact WingTiles.grid_cells _ _ _
  have pt (i : Index) : ratPoint (fn i)=gridPt X Y i := by
    have lookup (l : List ℚ) (j : Nat) : ((l.getD j 0:ℚ):ℝ)=(l.map ((↑) : ℚ → ℝ)).getD j 0 := by
      simpa only [Rat.cast_zero] using (List.getD_map (l:=l) (d:=0) (n:=j) (fun a : ℚ => (a:ℝ))).symm
    exact Prod.ext (lookup x i.1) (lookup y i.2)
  intro r hr
  change r∈data.2 at hr
  rw [roles] at hr
  obtain ⟨role,mem,rfl⟩ := List.mem_map.mp hr
  obtain ⟨⟨p,h⟩,listed,belongs⟩ := cert.assignments role mem
  refine ⟨fn p.tip,?_,?_⟩
  · rw [←List.map_drop]; exact List.mem_map_of_mem belongs
  · intro q door
    rw [pt]
    exact misses xord yord region (by simpa only [xlen,ylen] using boxes) p
      (by simpa only [xlen,ylen] using cert.valid _ listed) h
      (arithmetic m run p h (List.all_eq_true.mp cert.aperture (p,h) listed)) door

theorem at_size {t : Template} {rs : List Nat} (basic : WingEnvelopeCert.Cert t rs.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈rs,i≤n) {cache : List Entry} {xh yh : List SignHint} {idx : Data Nat}
    {ps : List CertPoint}
    (data : let p := t.corridor.baseRows++t.corridor.rest
      let rows := p.reverse
      let bs := stack [] p
      cache.length=rows.length ∧ Verified rows bs cache 0 rows.length ∧
      RegisterOrder.check t rows bs cache false xh=true ∧ RegisterOrder.check t rows bs cache true yh=true ∧
      IndexedWing.check t rows cache idx=true ∧ Cert t bs cache idx ps)
    (boxes : ∀ b∈idx.1,ValidBox t.chart.x.length t.chart.y.length b) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(rs.map fun (i:Nat) => (i:ℚ)*s)
    WingTiles.Filled t args → Hidden t args := by
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

end ArtGallery.Orthogonal.BoundaryPoint.WingEscape
end
