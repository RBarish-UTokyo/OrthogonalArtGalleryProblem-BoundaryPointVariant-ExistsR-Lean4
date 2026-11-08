module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomContact
public import ArtGallery.Orthogonal.BoundaryPoint.WingTiles

/-! # The arithmetic room of an executed wing meets its staircase in the window

The executed rectangle list is the staircase list followed by the room list.
On the certified wing grid the two unions meet exactly in a vertical grid
segment, whose three coordinates are room levels. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomJoin
open Set CorridorProgram GridParity ShapeRefs IndexedWing ChartDrawing BoundaryChart WingEnvelope
open RegisterTable RegisterOrder MarginCert LinearRegister WingOrderSound RoomCoordinates ArtGallery.Orthogonal.Hard

theorem cells_append (a b : List (Rect ℚ)) : WingTiles.cells (a++b)=WingTiles.cells a∪WingTiles.cells b := by
  ext q; simp only [WingTiles.cells,List.mem_append,Set.mem_ofPred_eq,Set.mem_union]
  constructor
  · rintro ⟨r,(h|h),i⟩
    · exact Or.inl ⟨r,h,i⟩
    · exact Or.inr ⟨r,h,i⟩
  · rintro (⟨r,h,i⟩|⟨r,h,i⟩)
    · exact ⟨r,Or.inl h,i⟩
    · exact ⟨r,Or.inr h,i⟩

theorem cells_map (x y : List ℚ) (l : List (Rect Nat)) :
    WingTiles.cells (l.map fun r => (x.getD r.1 0,x.getD r.2.1 0,y.getD r.2.2.1 0,y.getD r.2.2.2 0))=
    cellsR (x.map ((↑) : ℚ → ℝ)) (y.map ((↑) : ℚ → ℝ)) l := by
  simpa [mapData] using WingTiles.grid_cells x y (l,[])

/-- The room rectangles of a wing, evaluated at inverse size `1/n`. -/
theorem room_cells (a : PlanGeometry.ArithmeticRoom) (n : Nat) :
    WingTiles.cells (a.coords ((1:ℚ)/n)).1=cellsR (a.x.coordsR (1/(n:ℝ))) (a.y.coordsR (1/(n:ℝ))) a.cells := by
  have hs : (((1:ℚ)/n : ℚ) : ℝ)=1/(n:ℝ) := by push_cast; ring
  rw [←hs,←cast_coords,←cast_coords]
  simpa [PlanGeometry.ArithmeticRoom.coords] using cells_map (a.x.coordsQ ((1:ℚ)/n)) (a.y.coordsQ ((1:ℚ)/n)) a.cells

/-- Local split of an executed wing into staircase cells and room cells, with
their common window. -/
theorem split {t : Template} {ranks : List Nat} (ev : Evidence t ranks.length) (n j : Nat)
    (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) {cache : List Entry} {xh yh : List SignHint} (index : Data Nat)
    (data : let p := t.corridor.baseRows++t.corridor.rest
      let rs := p.reverse
      let bs := stack [] p
      cache.length=rs.length ∧ Verified rs bs cache 0 rs.length ∧
      RegisterOrder.check t rs bs cache false xh=true ∧ RegisterOrder.check t rs bs cache true yh=true ∧
      IndexedWing.check t rs cache index=true)
    (bounds : ∀ r∈index.1,r.1<t.chart.x.length ∧ r.2.1<t.chart.x.length ∧ r.2.2.1<t.chart.y.length ∧ r.2.2.2<t.chart.y.length)
    {k : Nat} (hk : t.corridor.cells.length=k) {w : Nat × Nat × Nat}
    (ok : RoomContact.check (index.1.take k) (index.1.drop k) w=true)
    {a b₀ b₁ : Nat}
    (wa : RegisterAlias.equivalent (t.corridor.baseRows++t.corridor.rest).reverse cache t.room.x (.level a) ((refsFor t false).getD w.1 0)=true)
    (wb₀ : RegisterAlias.equivalent (t.corridor.baseRows++t.corridor.rest).reverse cache t.room.y (.level b₀) ((refsFor t true).getD w.2.1 0)=true)
    (wb₁ : RegisterAlias.equivalent (t.corridor.baseRows++t.corridor.rest).reverse cache t.room.y (.level b₁) ((refsFor t true).getD w.2.2 0)=true) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)
    let X := t.room.x.coordsR (1/(n:ℝ))
    let Y := t.room.y.coordsR (1/(n:ℝ))
    WingTiles.cells (t.corridor.coords args).1 ∩ WingTiles.cells (t.room.coords s).1 =
      ArtGallery.segment (X.getD a 0,Y.getD b₀ 0) (X.getD a 0,Y.getD b₁ 0) := by
  let s := (1:ℚ)/n
  let args := s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)
  let p := t.corridor.baseRows++t.corridor.rest
  let xs := execRat args [] p
  let XG := (grid t args false).map ((↑) : ℚ → ℝ)
  let YG := (grid t args true).map ((↑) : ℚ → ℝ)
  have pos : 0<getRat args 0 := by change 0<(1:ℚ)/n; positivity
  have small : getRat args 0≤RegisterForm.cap := by
    change (1:ℚ)/n≤1/65
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have run : Ledger args p.reverse xs := by simpa only [List.append_nil,xs] using exec_ledger (Ledger.nil (args:=args)) p
  have enc := lookup_bound (xs:=[]) (WingEnvelopeCert.parameters n j ranks hn hj hr) (by exact empty_encloses) ev.intervals.arithmetic
  obtain ⟨size,valid,xc,yc,rec⟩ := data
  have m : Model args xs p.reverse (stack [] p) cache := ⟨run,enc,pos,small,RegisterTable.model run enc pos small size valid⟩
  have spec := IndexedWing.realized m rfl index rec
  have hx : XG.IsChain (·<·) := RegisterOrder.axis m rfl false xh xc
  have hy : YG.IsChain (·<·) := RegisterOrder.axis m rfl true yh yc
  have xlen : XG.length=t.chart.x.length := by simp [XG,grid,selected,idsOf]
  have ylen : YG.length=t.chart.y.length := by simp [YG,grid,selected,idsOf]
  -- the two rectangle lists
  have corrLen : (t.corridor.coords args).1.length=k := by
    rw [←hk]; simp [Layout.coords]
  have parts := congrArg Prod.fst spec
  simp only [ShapeRefs.join,mapData] at parts
  have corrEq : (t.corridor.coords args).1=(index.1.take k).map
      (fun r => ((grid t args false).getD r.1 0,(grid t args false).getD r.2.1 0,
        (grid t args true).getD r.2.2.1 0,(grid t args true).getD r.2.2.2 0)) := by
    have h := congrArg (List.take k) parts
    rw [List.take_left' corrLen] at h
    rw [h,List.map_take]
  have roomEq : (t.room.coords (getRat args 0)).1=(index.1.drop k).map
      (fun r => ((grid t args false).getD r.1 0,(grid t args false).getD r.2.1 0,
        (grid t args true).getD r.2.2.1 0,(grid t args true).getD r.2.2.2 0)) := by
    have h := congrArg (List.drop k) parts
    rw [List.drop_left' corrLen] at h
    rw [h,List.map_drop]
  change WingTiles.cells (t.corridor.coords args).1 ∩ WingTiles.cells (t.room.coords (getRat args 0)).1=_
  rw [corrEq,roomEq,cells_map,cells_map]
  have inb (l : List (Rect Nat)) (hl : ∀ r∈l,r∈index.1) :
      ∀ r∈l,r.1<XG.length ∧ r.2.1<XG.length ∧ r.2.2.1<YG.length ∧ r.2.2.2<YG.length := by
    intro r hr'; rw [xlen,ylen]; exact bounds r (hl r hr')
  rw [RoomContact.contact (xs:=XG) (ys:=YG) hx hy (inb _ (fun r h => List.mem_of_mem_take h))
    (inb _ (fun r h => List.mem_of_mem_drop h)) ok]
  have cast (l : List ℚ) (i : Nat) : (l.map ((↑) : ℚ → ℝ)).getD i 0=((l.getD i 0 : ℚ) : ℝ) := by
    simpa only [Rat.cast_zero] using List.getD_map (l:=l) (n:=i) (d:=0) (fun u : ℚ => (u:ℝ))
  have value (y : Bool) (i c : Nat)
      (h : RegisterAlias.equivalent p.reverse cache (axisOf t y) (.level c) ((refsFor t y).getD i 0)=true) :
      ((grid t args y).map ((↑) : ℚ → ℝ)).getD i 0=((if y then t.room.y else t.room.x).coordsR (1/(n:ℝ))).getD c 0 := by
    rw [cast,grid_value m rfl,←RegisterAlias.equal m _ h]
    simp only [readRef]
    have hs : (getRat args 0 : ℝ)=1/(n:ℝ) := by change (((1:ℚ)/n : ℚ) : ℝ)=_; push_cast; ring
    rw [←hs,←cast_coords,cast]
    cases y <;> rfl
  have e1 := value false w.1 a wa
  have e2 := value true w.2.1 b₀ wb₀
  have e3 := value true w.2.2 b₁ wb₁
  simp only [Bool.false_eq_true,ite_false,ite_true] at e1 e2 e3
  change ArtGallery.segment (XG.getD w.1 0,YG.getD w.2.1 0) (XG.getD w.1 0,YG.getD w.2.2 0)=_
  rw [e1,e2,e3]

end ArtGallery.Orthogonal.BoundaryPoint.RoomJoin
end
