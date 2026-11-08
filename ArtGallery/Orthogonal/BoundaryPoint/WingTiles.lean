module

public import ArtGallery.Orthogonal.BoundaryPoint.WingMarks
public import ArtGallery.Orthogonal.BoundaryPoint.GridSweep

/-! # Jordan-filled set of the executed staircase and one-window room
The rectangle coordinates in this conclusion are read directly from the
production register and room programs. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.WingTiles
open Set CorridorProgram GridParity GridSweep ShapeRefs IndexedWing ChartDrawing BoundaryChart WingEnvelope
open RegisterTable RegisterOrder MarginCert LinearRegister WingOrderSound ArtGallery.Orthogonal.Hard

def cells (rs : List (Rect ℚ)) : Set Point :=
  {q | ∃ r∈rs,(r.1:ℝ)≤q.1 ∧ q.1≤(r.2.1:ℝ) ∧ (r.2.2.1:ℝ)≤q.2 ∧ q.2≤(r.2.2.2:ℝ)}

def Filled (t : Template) (args : List ℚ) :=
  let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))
  (actual t.chart g).filled=cells g.1

theorem grid_cells (x y : List ℚ) (d : Data Nat) :
    cells ((mapData (fun i => x.getD i 0) (fun i => y.getD i 0) d).1)=
    cellsR (x.map ((↑) : ℚ → ℝ)) (y.map ((↑) : ℚ → ℝ)) d.1 := by
  have cv (l : List ℚ) (i : Nat) : (l.map ((↑) : ℚ → ℝ)).getD i 0=(((l.getD i 0):ℚ):ℝ) := by
    simpa only [Rat.cast_zero] using List.getD_map (l:=l) (n:=i) (d:=0) (fun u : ℚ => (u:ℝ))
  ext q
  change (∃ r∈(mapData _ _ d).1,_) ↔ ∃ r∈d.1,_
  constructor
  · rintro ⟨r,hr,inside⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    refine ⟨i,hi,?_⟩
    simpa only [cv] using inside
  · rintro ⟨r,hr,inside⟩
    refine ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,?_⟩
    simpa only [cv] using inside

theorem at_size {t : Template} {ranks : List Nat} (ev : Evidence t ranks.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) {cache : List Entry} {xh yh : List SignHint} (index : Data Nat)
    (data : let p := t.corridor.baseRows++t.corridor.rest
      let rs := p.reverse
      let bs := stack [] p
      cache.length=rs.length ∧ Verified rs bs cache 0 rs.length ∧
      RegisterOrder.check t rs bs cache false xh=true ∧ RegisterOrder.check t rs bs cache true yh=true ∧
      IndexedWing.check t rs cache index=true)
    (axisEdges : RoomGrid.cyclicAxis t.chart.cycle.points)
    (bounds : ∀ r∈index.1,r.1<t.chart.x.length ∧ r.2.1<t.chart.x.length ∧ r.2.2.1<t.chart.y.length ∧ r.2.2.2<t.chart.y.length)
    (sweep : Checked t.chart.cycle.points index.1 t.chart.y.length 0 (2*t.chart.x.length+1)) :
    let s := (1:ℚ)/n
    Filled t (s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)) := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  let g := ShapeRefs.join (t.corridor.coords args) (t.room.coords s)
  let X := (grid t args false).map ((↑) : ℚ → ℝ)
  let Y := (grid t args true).map ((↑) : ℚ → ℝ)
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤RegisterForm.cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have enc := lookup_bound (xs:=[]) (WingEnvelopeCert.parameters n j ranks hn hj hr) (by exact empty_encloses) ev.intervals.arithmetic
  obtain ⟨size,valid,xc,yc,rec⟩ := data
  have m : Model args xs p.reverse (stack [] p) cache := ⟨run,enc,pos,small,RegisterTable.model run enc pos small size valid⟩
  have xlen : X.length=t.chart.x.length := by simp [X,grid,selected,idsOf]
  have ylen : Y.length=t.chart.y.length := by simp [Y,grid,selected,idsOf]
  have spec := IndexedWing.realized m rfl index rec
  have cx : cells g.1=cellsR X Y index.1 := by
    change cells (ShapeRefs.join (t.corridor.coords args) (t.room.coords (getRat args 0))).1=_
    rw [spec]; exact grid_cells _ _ _
  have pol : actual t.chart g=⟨t.chart.cycle.points.map (gridPt X Y)⟩ := actual_grid _ _
  change (actual t.chart g).filled=cells g.1
  rw [cx,pol]
  apply filled_of_rows (xs:=X) (ys:=Y) (RegisterOrder.axis m rfl false xh xc) (RegisterOrder.axis m rfl true yh yc)
    (by simpa only [xlen,ylen] using ev.indices) axisEdges (pol ▸ WingOrderSound.realized ev n j hn hj hr)
    (by simpa only [xlen,ylen] using bounds)
  intro i
  rw [ylen]; exact sweep i.val (Nat.zero_le _) (by simpa only [xlen] using i.isLt)

end ArtGallery.Orthogonal.BoundaryPoint.WingTiles
end
