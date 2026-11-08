module

public import ArtGallery.Orthogonal.BoundaryPoint.PlanGeometry
public import ArtGallery.Orthogonal.BoundaryPoint.ContourJoin

/-! # Polynomial-time geometry of the hub and a physical leaf

The room and profile are fixed from finite catalogues. The source supplies
the size, door index, and two or three ranks. The hub is computed from a
polynomial-time list of ordered slot coordinates. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.GeometryTime
open Complexity Complexity.PT Complexity.PT.Code ArtGallery.Stade
open PlanGeometry CorridorProgram RoomCoordinates

variable {α : Type} [Code α]

@[fun_prop] theorem room_coords (r : ArithmeticRoom) {s : α → ℚ} (hs : PT s) :
    PT (fun a => r.coords (s a)) := by
  let x (a : α) (i : Nat) := (r.x.coordsQ (s a)).getD i 0
  let y (a : α) (i : Nat) := (r.y.coordsQ (s a)).getD i 0
  have hx (i : Nat) : PT (fun a => x a i) :=
    PT.listGetD (RoomCoordinates.coords_pt r.x hs) (PT.const i) (PT.const 0)
  have hy (i : Nat) : PT (fun a => y a i) :=
    PT.listGetD (RoomCoordinates.coords_pt r.y hs) (PT.const i) (PT.const 0)
  let rect (a : α) (j : Rect Nat) := (x a j.1,x a j.2.1,y a j.2.2.1,y a j.2.2.2)
  let point (a : α) (j : RoomGrid.Index) := (x a j.1,y a j.2)
  have cells (l : List (Rect Nat)) : PT (fun a => l.map (rect a)) := by
    induction l with
    | nil => exact PT.const []
    | cons j l ih => exact PT.cons (PT.pair (hx _) (PT.pair (hx _) (PT.pair (hy _) (hy _)))) ih
  have group (l : List RoomGrid.Index) : PT (fun a => l.map (point a)) := by
    induction l with
    | nil => exact PT.const []
    | cons j l ih => exact PT.cons (PT.pair (hx _) (hy _)) ih
  have groups (ll : List (List RoomGrid.Index)) : PT (fun a => ll.map (fun l => l.map (point a))) := by
    induction ll with
    | nil => exact PT.const []
    | cons l ll ih => exact PT.cons (group l) ih
  exact PT.pair (cells r.cells) (groups r.roles)

@[fun_prop] theorem shift_pt {d : α → ℚ} {r : α → Rect ℚ} (hd : PT d) (hr : PT r) :
    PT (fun a => shift (d a) (r a)) := by unfold shift; fun_prop

@[fun_prop] theorem step_cells {n j : α → Nat} (hn : PT n) (hj : PT j) :
    PT (fun a => stepCells (n a) (j a)) := by unfold stepCells; fun_prop

@[fun_prop] theorem hub_pt {n count : α → Nat} {ordered : α → List ℚ}
    (hn : PT n) (hc : PT count) (ho : PT ordered) :
    PT (fun a => hub (n a) (count a) (ordered a)) := by
  unfold hub
  fun_prop

theorem leaf_coords (c : Layout) (r : ArithmeticRoom) {n j : α → Nat} {ranks : α → List Nat}
    (hn : PT n) (hj : PT j) (hr : PT ranks) :
    PT (fun a =>
      let s := (1:ℚ)/(n a)
      let h := c.coords (s::((j a:ℚ)*s)::((ranks a).map fun (i : Nat) => (i:ℚ)*s))
      let t := r.coords s
      (h.1++t.1,h.2++t.2)) := by
  have h : PT (fun a => c.coords (((1:ℚ)/(n a))::((j a:ℚ)*((1:ℚ)/(n a)))::
      ((ranks a).map fun (i : Nat) => (i:ℚ)*((1:ℚ)/(n a))))) := CorridorProgram.coords_pt c (by fun_prop)
  have t := room_coords r (show PT (fun a => (1:ℚ)/(n a)) by fun_prop)
  dsimp only
  fun_prop

end ArtGallery.Orthogonal.BoundaryPoint.GeometryTime
end
