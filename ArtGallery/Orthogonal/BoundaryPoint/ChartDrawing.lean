module

public import ArtGallery.Orthogonal.BoundaryPoint.CatalogPlan
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Shifted_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Lower_10_40_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Lower_10_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Lower_10_360_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.Lower_10_520_1000
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_1_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_1_360
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_1_520
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvRevGe_1_10
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvLe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingChart.InvRevGe_40_200

/-! # Numeric plan to boundary-point gallery
The complete hub cycle and private rectangular coordinate tables are drawn
with fixed turn charts. The machine-time proof covers every operation from
an arbitrary numeric plan to its list of rational vertices and guard budget. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.ChartDrawing
open PlanGeometry CorridorProgram BoundaryChart RectContour CatalogPlan BankCoordinates
open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade

structure Template where
  corridor : Layout
  room : ArithmeticRoom
  chart : Chart

def catalog : List Template := [
  ⟨BankCorridor.Ordinary_40_200_520.layout, ⟨RoomFamily.Ordinary.xAxis, RoomFamily.Ordinary.yAxis, RoomFamily.Ordinary.cells, RoomFamily.Ordinary.roles⟩, WingChart.Ordinary_40_200_520.chart⟩,
  ⟨BankCorridor.Shifted_40_200_520.layout, ⟨RoomFamily.Shifted.xAxis, RoomFamily.Shifted.yAxis, RoomFamily.Shifted.cells, RoomFamily.Shifted.roles⟩, WingChart.Shifted_40_200_520.chart⟩,
  ⟨BankCorridor.Lower_40_200_1000.layout, ⟨RoomFamily.Lower.xAxis, RoomFamily.Lower.yAxis, RoomFamily.Lower.cells, RoomFamily.Lower.roles⟩, WingChart.Lower_40_200_1000.chart⟩,
  ⟨BankCorridor.Lower_10_40_1000.layout, ⟨RoomFamily.Lower.xAxis, RoomFamily.Lower.yAxis, RoomFamily.Lower.cells, RoomFamily.Lower.roles⟩, WingChart.Lower_10_40_1000.chart⟩,
  ⟨BankCorridor.Lower_10_200_1000.layout, ⟨RoomFamily.Lower.xAxis, RoomFamily.Lower.yAxis, RoomFamily.Lower.cells, RoomFamily.Lower.roles⟩, WingChart.Lower_10_200_1000.chart⟩,
  ⟨BankCorridor.Lower_10_360_1000.layout, ⟨RoomFamily.Lower.xAxis, RoomFamily.Lower.yAxis, RoomFamily.Lower.cells, RoomFamily.Lower.roles⟩, WingChart.Lower_10_360_1000.chart⟩,
  ⟨BankCorridor.Lower_10_520_1000.layout, ⟨RoomFamily.Lower.xAxis, RoomFamily.Lower.yAxis, RoomFamily.Lower.cells, RoomFamily.Lower.roles⟩, WingChart.Lower_10_520_1000.chart⟩,
  ⟨BankCorridor.InvLe_1_40.layout, ⟨RoomFamily.InvLe.xAxis, RoomFamily.InvLe.yAxis, RoomFamily.InvLe.cells, RoomFamily.InvLe.roles⟩, WingChart.InvLe_1_40.chart⟩,
  ⟨BankCorridor.InvLe_1_200.layout, ⟨RoomFamily.InvLe.xAxis, RoomFamily.InvLe.yAxis, RoomFamily.InvLe.cells, RoomFamily.InvLe.roles⟩, WingChart.InvLe_1_200.chart⟩,
  ⟨BankCorridor.InvLe_1_360.layout, ⟨RoomFamily.InvLe.xAxis, RoomFamily.InvLe.yAxis, RoomFamily.InvLe.cells, RoomFamily.InvLe.roles⟩, WingChart.InvLe_1_360.chart⟩,
  ⟨BankCorridor.InvLe_1_520.layout, ⟨RoomFamily.InvLe.xAxis, RoomFamily.InvLe.yAxis, RoomFamily.InvLe.cells, RoomFamily.InvLe.roles⟩, WingChart.InvLe_1_520.chart⟩,
  ⟨BankCorridor.InvRevGe_1_10.layout, ⟨RoomFamily.InvRevGe.xAxis, RoomFamily.InvRevGe.yAxis, RoomFamily.InvRevGe.cells, RoomFamily.InvRevGe.roles⟩, WingChart.InvRevGe_1_10.chart⟩,
  ⟨BankCorridor.InvLe_40_200.layout, ⟨RoomFamily.InvLe.xAxis, RoomFamily.InvLe.yAxis, RoomFamily.InvLe.cells, RoomFamily.InvLe.roles⟩, WingChart.InvLe_40_200.chart⟩,
  ⟨BankCorridor.InvRevGe_40_200.layout, ⟨RoomFamily.InvRevGe.xAxis, RoomFamily.InvRevGe.yAxis, RoomFamily.InvRevGe.cells, RoomFamily.InvRevGe.roles⟩, WingChart.InvRevGe_40_200.chart⟩]

def choose {β : Type} (tables : List Template) (value : Template → β) (i : Nat) (fallback : β) : β :=
  match tables with
  | [] => fallback
  | t::ts => if i=0 then value t else choose ts value (i-1) fallback

abbrev Drawn := Option ContourJoin.Entrance × Nat

def drawOne (t : Template) (n j : Nat) (ranks : List Nat) : Drawn :=
  let s := (1:ℚ)/n
  let h := t.corridor.coords (s::((j:ℚ)*s)::(ranks.map fun (i : Nat) => (i:ℚ)*s))
  let r := t.room.coords s
  let cycle := t.chart.draw (h.1++r.1,h.2++r.2)
  ((ContourJoin.atDoor (door j) (W n) cycle).map (fun path => (door j,path)),
   t.corridor.roles.length+t.room.roles.length+1)

def batch (n : Nat) (rows : List Row) : List Drawn :=
  rows.zipIdx.map fun (r,j) => choose catalog (fun t => drawOne t n j r.2) r.1 (none,0)

def vertices (p : Input) : Option (List Vertex × Nat) :=
  if p.1.isEmpty then some ([(0,0),(1,0),(1,1),(0,1)],1) else
  let n := max p.1.length p.2.length
  let drawn := batch n p.1
  let hub := hubCycle n p.1.length (p.2.map fun a => slotX n a.1 a.2)
  if drawn.all (fun v => v.1.isSome) then
    (ContourJoin.splice (W n) hub (drawn.filterMap Prod.fst)).map
      (fun cycle => (cycle,p.2.length+(drawn.map Prod.snd).sum))
  else none

section Time
variable {α β : Type} [Code α] [Code β]

theorem choose_pt (tables : List Template) {f : α → Template → β} {i : α → Nat} {d : α → β}
    (hf : ∀ t, PT (fun a => f a t)) (hi : PT i) (hd : PT d) :
    PT (fun a => choose tables (f a) (i a) (d a)) := by
  induction tables generalizing i with
  | nil => exact hd
  | cons t ts ih =>
    simp only [choose]
    apply PT.ite_prop (PT.decide_eq hi (PT.const 0)) (hf t)
    exact ih (show PT (fun a => i a-1) by fun_prop)

@[fun_prop] theorem draw_one_pt (t : Template) {n j : α → Nat} {ranks : α → List Nat}
    (hn : PT n) (hj : PT j) (hr : PT ranks) :
    PT (fun a => drawOne t (n a) (j a) (ranks a)) := by
  have h := GeometryTime.leaf_coords t.corridor t.room hn hj hr
  have c := BoundaryChart.draw_pt t.chart h
  have path := ContourJoin.at_door_pt (show PT (fun a => door (j a)) by fun_prop)
    (show PT (fun a => W (n a)) by fun_prop) c
  unfold drawOne
  dsimp only at path ⊢
  exact PT.pair (PT.optionMap path (by fun_prop)) (PT.const _)

@[fun_prop] theorem batch_pt {n : α → Nat} {r : α → List Row} (hn : PT n) (hr : PT r) :
    PT (fun a => batch (n a) (r a)) := by
  unfold batch
  apply PT.map _ (by fun_prop)
  apply choose_pt
  · intro t; fun_prop
  · fun_prop
  · exact PT.const _

theorem vertices_pt {p : α → Input} (hp : PT p) : PT (fun a => vertices (p a)) := by
  unfold vertices
  have hn : PT (fun a => max (p a).1.length (p a).2.length) := by fun_prop
  have hd := batch_pt hn (PT.fst hp)
  have hh := BoundaryChart.hub_pt hn (PT.length (PT.fst hp))
    (show PT (fun a => (p a).2.map fun i => slotX (max (p a).1.length (p a).2.length) i.1 i.2) by fun_prop)
  have join := ContourJoin.splice_pt (show PT (fun a => W (max (p a).1.length (p a).2.length)) by fun_prop)
    hh (PT.filterMap (f:=fun (_ : α) (w : Drawn) => w.1) (PT.fst PT.snd') hd)
  dsimp only
  fun_prop

end Time
end ArtGallery.Orthogonal.BoundaryPoint.ChartDrawing
end
