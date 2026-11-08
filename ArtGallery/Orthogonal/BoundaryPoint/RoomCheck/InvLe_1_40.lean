module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomRow.InvLe
public import ArtGallery.Orthogonal.BoundaryPoint.RoomSplit.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvLe_1_40

/-! Room facts of profile `InvLe_1_40` (generated): the corridor spots miss the window wedges of the
critical boxes, the corridor program has certified register boxes, and the catalogue entry. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.InvLe_1_40
open MarginCert RoomWedge RoomGlobal WingOrder.InvLe_1_40 ChartDrawing

theorem clear1 : corridorClear template.corridor RoomRow.InvLe.win RoomRow.InvLe.box1 RoomRow.InvLe.xmin=true := by
  decide +kernel

theorem program_ok : ok (params 2) [] (template.corridor.baseRows++template.corridor.rest)=true :=
  WingDoor.InvLe_1_40.checks

theorem room_eq : template.room=⟨RoomFamily.InvLe.xAxis,RoomFamily.InvLe.yAxis,RoomFamily.InvLe.cells,
    RoomFamily.InvLe.roles⟩ := rfl

theorem tag_eq : catalog[7]?=some template := rfl

end ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.InvLe_1_40
end
