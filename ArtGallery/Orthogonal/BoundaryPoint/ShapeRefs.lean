module

public import ArtGallery.Orthogonal.BoundaryPoint.WingEnvelopeCert

/-! # Sources of the individual coordinates in the emitted chart
A selector reads a staircase register, a polynomial coordinate of the room,
or the actual default zero used by the drawing program. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ShapeRefs
open ChartDrawing BoundaryChart CorridorProgram MarginCert LinearRegister RoomCoordinates WingEnvelope

inductive Ref where
  | origin
  | register (i : Nat)
  | level (i : Nat)

instance : Zero Ref := ⟨.origin⟩

def join {α : Type} (a b : Data α) : Data α := (a.1++b.1,a.2++b.2)

def refs (t : Template) : Data Ref := join
  (mapData Ref.register Ref.register (t.corridor.cells,t.corridor.roles))
  (mapData Ref.level Ref.level (t.room.cells,t.room.roles))

def axes {α : Type} [Zero α] (c : Chart) (g : Data α) : List (α × α) :=
  c.cycle.points.map (chartPt (selected (pool false g) c.x) (selected (pool true g) c.y))

def readRef (xs : List ℚ) (a : Axis) (s : ℚ) : Ref → ℚ
  | .origin => 0
  | .register i => getRat xs i
  | .level i => (a.coordsQ s).getD i 0

private theorem select_map {α β : Type} [Zero α] [Zero β] (f : α → β) (zero : f 0=0)
    (l : List α) (k : Nat) : (l.map f).getD k 0=f (l.getD k 0) := by
  simpa only [zero] using List.getD_map (l:=l) (d:=0) (n:=k) f

private theorem selected_map {α β : Type} [Zero α] [Zero β] (f : α → β) (zero : f 0=0)
    (l : List α) (ids : List Nat) : selected (l.map f) ids=(selected l ids).map f := by
  simp only [selected,List.map_map,Function.comp_def,select_map f zero]

theorem axes_map {α β : Type} [Zero α] [Zero β] (c : Chart) (g : Data α)
    (x y : α → β) (zx : x 0=0) (zy : y 0=0) :
    axes c (mapData x y g)=(axes c g).map fun p => (x p.1,y p.2) := by
  simp only [axes,map_pool,Bool.false_eq_true,ite_false,ite_true,selected_map x zx,selected_map y zy,
    List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro p _
  simp only [chartPt,select_map x zx,select_map y zy]

theorem coords (t : Template) (args : List ℚ) (s : ℚ) :
    let xs := execRat args [] (t.corridor.baseRows++t.corridor.rest)
    mapData (readRef xs t.room.x s) (readRef xs t.room.y s) (refs t)=
      join (t.corridor.coords args) (t.room.coords s) := by
  simp only [mapData,refs,join,Layout.coords,PlanGeometry.ArithmeticRoom.coords,List.map_append,
    List.map_map,Function.comp_def,Prod.mk.injEq,readRef,exec_append]
  exact ⟨rfl,rfl⟩

theorem levels (t : Template) (args : List ℚ) (s : ℚ) (y : Bool) (ids : List Nat) :
    let xs := execRat args [] (t.corridor.baseRows++t.corridor.rest)
    let g := join (t.corridor.coords args) (t.room.coords s)
    selected (pool y g) ids=(selected (pool y (refs t)) ids).map
      (readRef xs (if y then t.room.y else t.room.x) s) := by
  dsimp only; rw [←coords,map_pool]
  cases y <;> apply selected_map _ rfl

theorem actual (t : Template) (args : List ℚ) (s : ℚ) :
    let xs := execRat args [] (t.corridor.baseRows++t.corridor.rest)
    let c := t.corridor.coords args
    let r := t.room.coords s
    t.chart.draw (c.1++r.1,c.2++r.2) =
      (axes t.chart (refs t)).map (fun p => (readRef xs t.room.x s p.1,readRef xs t.room.y s p.2)) := by
  let xs := execRat args [] (t.corridor.baseRows++t.corridor.rest)
  let x := readRef xs t.room.x s
  let y := readRef xs t.room.y s
  have data := coords t args s
  exact (congrArg (axes t.chart) data).symm.trans (axes_map _ _ x y rfl rfl)

end ArtGallery.Orthogonal.BoundaryPoint.ShapeRefs
end
