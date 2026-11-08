module

public import ArtGallery.Orthogonal.BoundaryPoint.RoomRow.InvRevGe
public import ArtGallery.Orthogonal.BoundaryPoint.RoomSplit.InvRevGe_40_200
public import ArtGallery.Orthogonal.BoundaryPoint.WingDoor.InvRevGe_40_200

/-! Room facts of profile `InvRevGe_40_200` (generated): the corridor spots miss the window wedges of the
critical boxes, the corridor program has certified register boxes, and the catalogue entry. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.InvRevGe_40_200
open MarginCert RoomWedge RoomGlobal WingOrder.InvRevGe_40_200 ChartDrawing

theorem clear1 : corridorClear template.corridor RoomRow.InvRevGe.win RoomRow.InvRevGe.box1 RoomRow.InvRevGe.xmin=true := by
  decide +kernel

theorem program_ok : ok (params 2) [] (template.corridor.baseRows++template.corridor.rest)=true :=
  WingDoor.InvRevGe_40_200.checks

theorem room_eq : template.room=⟨RoomFamily.InvRevGe.xAxis,RoomFamily.InvRevGe.yAxis,RoomFamily.InvRevGe.cells,
    RoomFamily.InvRevGe.roles⟩ := rfl

theorem tag_eq : catalog[13]?=some template := rfl

end ArtGallery.Orthogonal.BoundaryPoint.RoomCheck.InvRevGe_40_200
end
