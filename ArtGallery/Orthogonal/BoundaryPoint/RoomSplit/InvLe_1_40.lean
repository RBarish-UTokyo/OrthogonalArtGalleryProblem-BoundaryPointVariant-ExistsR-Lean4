module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomJoin
public import ArtGallery.Orthogonal.BoundaryPoint.WingFill.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.RoomFill.InvLe

/-! The InvLe room of this executed wing meets its staircase exactly in the room window. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomSplit.InvLe_1_40
open WingOrder.InvLe_1_40 WingRecords.InvLe_1_40 RoomFamily.InvLe GridParity RoomGrid ArtGallery.Orthogonal.Hard
set_option maxRecDepth 16000
set_option maxHeartbeats 16000000

theorem contact : RoomContact.check (index.1.take 33) (index.1.drop 33) (44,13,16)=true := by decide +kernel
theorem alias_x : RegisterAlias.equivalent (template.corridor.baseRows++template.corridor.rest).reverse cache
    template.room.x (.level 1) ((IndexedWing.refsFor template false).getD 44 0)=true := by decide +kernel
theorem alias_y₀ : RegisterAlias.equivalent (template.corridor.baseRows++template.corridor.rest).reverse cache
    template.room.y (.level 12) ((IndexedWing.refsFor template true).getD 13 0)=true := by decide +kernel
theorem alias_y₁ : RegisterAlias.equivalent (template.corridor.baseRows++template.corridor.rest).reverse cache
    template.room.y (.level 13) ((IndexedWing.refsFor template true).getD 16 0)=true := by decide +kernel

theorem split {ranks : List Nat} (size : ranks.length=2) (n j : Nat) (hn : 65≤n) (hj : j≤n) (hr : ∀ i∈ranks,i≤n) :
    let s := (1:ℚ)/n
    let args := s::((j:ℚ)*s)::(ranks.map fun (i:Nat) => (i:ℚ)*s)
    let pt := gridPt (xAxis.coordsR (1/(n:ℝ))) (yAxis.coordsR (1/(n:ℝ)))
    (BoundaryChart.actual template.chart (ShapeRefs.join (template.corridor.coords args) (template.room.coords s))).filled=
      WingTiles.cells (template.corridor.coords args).1 ∪ (room n).filled ∧
    WingTiles.cells (template.corridor.coords args).1 ∩ (room n).filled=ArtGallery.segment (pt window.1) (pt window.2) := by
  intro s args pt
  have roomEq : WingTiles.cells (template.room.coords s).1=(room n).filled := by
    rw [RoomJoin.room_cells,RoomFill.InvLe.filled_eq n hn]
  refine ⟨?_,?_⟩
  · have h : _=_ := WingFill.InvLe_1_40.filled_eq size n j hn hj hr
    refine h.trans ?_
    show WingTiles.cells ((template.corridor.coords args).1++(template.room.coords s).1)=_
    rw [RoomJoin.cells_append,roomEq]
  · have h := RoomJoin.split (t:=template) (size ▸ CertifiedWing.InvLe_1_40.evidence) n j hn hj hr index
      ⟨sizes,verified,x_ok,y_ok,records⟩ cell_indices rfl contact alias_x alias_y₀ alias_y₁
    rw [←roomEq]
    exact h

end ArtGallery.Orthogonal.BoundaryPoint.RoomSplit.InvLe_1_40
end
